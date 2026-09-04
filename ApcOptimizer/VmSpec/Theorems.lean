import ApcOptimizer.VmSpec.Implementation.OpenVmChain

set_option autoImplicit false

namespace ApcOptimizer.OpenVM

variable {p : ℕ}

/-- **Substitution soundness, for OpenVM.** Assumes `hLegal` (every chip of `G ++ G'` — input and
    output — is legal for the VM `P` configures) and `hSound` (each per-chip replacement is
    sound). -/
theorem openVm_vmSoundReplacement [Fact p.Prime] {P : OpenVmParams p} {G G' : Guest p}
    -- TODO(AO): `G'`'s legality isn't derivable from `G`'s via `isSoundReplacementOf` yet.
    (hLegal : ∀ c ∈ G ++ G',
      c.legalGuest (openVmGuestRules defaultBusMap openVmMemBusId) P.maxWindow
        openVmTimestampBound P.maxInteractions)
    -- NB: legality carries the size bounds `isSoundReplacementOf` itself doesn't depend on.
    (hSound : List.Forall₂ (fun c c' => c'.isSoundReplacementOf c
      (openVmBusSemantics p defaultBusMap)) G G') :
    VmSoundReplacement (openVmHost P) G G' :=
  vmSoundReplacement_of_forall₂
    (openVmHost_realizes P
      (openVmGuestRules_eq defaultBusMap openVmMemBusId ▸ openVmHost_ordersRanks P))
    hLegal hSound

/-- **Substitution completeness, for OpenVM.** The mirror of `openVm_vmSoundReplacement`: every
    effect the original chips can produce, the replacements can produce too.

    It needs exactly one hypothesis soundness does not, `hAdm` — that the VM only ever realizes
    `Circuit.admissible` guest assignments. That is a claim about the machine rather than about any
    circuit, and it is where the remaining work is; `Host.forcesAdmissible` says why it cannot be
    made a per-circuit clause and what it should be derived from.

    Everything else is shared with the soundness direction, because
    `VmCompleteReplacement host G G'` *is* `VmSoundReplacement host G' G` — the same lifting runs,
    with witness generation supplying the existential. -/
theorem openVm_vmCompleteReplacement [Fact p.Prime] {P : OpenVmParams p} {G G' : Guest p}
    (hAdm : (openVmHost P).forcesAdmissible (openVmBusSemantics p defaultBusMap))
    (hLegal : ∀ c ∈ G ++ G',
      c.legalGuest (openVmGuestRules defaultBusMap openVmMemBusId) P.maxWindow
        openVmTimestampBound P.maxInteractions)
    (hComplete : List.Forall₂ (fun c c' => (∀ v ∈ Circuit.vars c, v.powdrId?.isSome) ∧
      ∃ ds : Derivations p, Circuit.isCompleteReplacementOf c' c
        (openVmBusSemantics p defaultBusMap) ds) G G') :
    VmCompleteReplacement (openVmHost P) G G' :=
  vmCompleteReplacement_of_forall₂
    (openVmHost_realizes P
      (openVmGuestRules_eq defaultBusMap openVmMemBusId ▸ openVmHost_ordersRanks P))
    hAdm hLegal hComplete

/-- **Substitution equivalence, for OpenVM**: the two directions together. -/
theorem openVm_vmEquivalent [Fact p.Prime] {P : OpenVmParams p} {G G' : Guest p}
    (hAdm : (openVmHost P).forcesAdmissible (openVmBusSemantics p defaultBusMap))
    (hLegal : ∀ c ∈ G ++ G',
      c.legalGuest (openVmGuestRules defaultBusMap openVmMemBusId) P.maxWindow
        openVmTimestampBound P.maxInteractions)
    (hSound : List.Forall₂ (fun c c' => c'.isSoundReplacementOf c
      (openVmBusSemantics p defaultBusMap)) G G')
    (hComplete : List.Forall₂ (fun c c' => (∀ v ∈ Circuit.vars c, v.powdrId?.isSome) ∧
      ∃ ds : Derivations p, Circuit.isCompleteReplacementOf c' c
        (openVmBusSemantics p defaultBusMap) ds) G G') :
    VmEquivalent (openVmHost P) G G' :=
  ⟨openVm_vmSoundReplacement hLegal hSound, openVm_vmCompleteReplacement hAdm hLegal hComplete⟩

end ApcOptimizer.OpenVM
