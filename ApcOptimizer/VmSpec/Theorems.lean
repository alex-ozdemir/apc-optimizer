import ApcOptimizer.VmSpec.Implementation.MemChain

set_option autoImplicit false

namespace ApcOptimizer.OpenVM

open ApcOptimizer.OpenVM.OrderFree

variable {p : ℕ}

/-- **Substitution soundness, for OpenVM.**

    ## Flaws

    This assumes legality for inputs `G` **and** outputs `G'`. The optimizer should be proved to
    preserve legality, so we can lift the `G'` assumption.

    -/
theorem openVm_vmSoundReplacement [Fact p.Prime] {P : OpenVmParams p} {G G' : Guest p}
    (hLegal : ∀ c ∈ G ++ G',
      c.legalGuestOF (openVmGuestRules defaultBusMap openVmMemBusId) openVmMemAddress
        P.maxWindow openVmTimestampBound P.maxInteractions)
    (hSound : List.Forall₂ (fun c c' => c'.isSoundReplacementOf c
      (openVmBusSemantics p defaultBusMap)) G G') :
    VmSoundReplacement (openVmHost P) G G' :=
  vmSoundReplacement_of_forall₂
    (openVmHost_realizes P
      (openVmGuestRules_eq defaultBusMap openVmMemBusId ▸ openVmHost_ordersRanks P))
    hLegal hSound

/-- **Substitution soundness, for OpenVM, order-free.** -/
theorem openVm_vmSoundReplacementOF [Fact p.Prime] {P : OpenVmParams p} {G G' : Guest p}
    (hLegal : ∀ c ∈ G ++ G',
      c.legalGuestOF (openVmGuestRules defaultBusMap openVmMemBusId) openVmMemAddress
        P.maxWindow openVmTimestampBound P.maxInteractions)
    (hSound : List.Forall₂ (fun c c' => c'.isSoundReplacementOf c
      (openVmBusSemanticsOF p defaultBusMap none)) G G') :
    VmSoundReplacement (openVmHost P) G G' :=
  openVm_vmSoundReplacement hLegal hSound

/-- **Substitution completeness, for OpenVM, order-free.**

    ## Flaws

    This assumes legality for inputs `G` **and** outputs `G'`. The optimizer should be proved to
    preserve legality, so we can lift the `G'` assumption.

    Targets the order-free variant of `BusSemantics.admissible` (`openVmBusSemanticsOF`) rather than
    the original one (`openVmBusSemantics`). The latter has proved hard to integrate with becuase of
    its syntactic order requirements.

    -/
theorem openVm_vmCompleteReplacementOF [Fact p.Prime] {P : OpenVmParams p} {G G' : Guest p}
    (hLegal : ∀ c ∈ G ++ G',
      c.legalGuestOF (openVmGuestRules defaultBusMap openVmMemBusId) openVmMemAddress
        P.maxWindow openVmTimestampBound P.maxInteractions)
    (hComplete : List.Forall₂ (fun c c' => (∀ v ∈ Circuit.vars c, v.powdrId?.isSome) ∧
      ∃ ds : Derivations p, Circuit.isCompleteReplacementOf c' c
        (openVmBusSemanticsOF p defaultBusMap none) ds) G G') :
    VmCompleteReplacement (openVmHost P) G G' :=
  vmCompleteReplacement_of_forall₂
    (openVmHost_realizesOF P none
      (openVmGuestRules_eq defaultBusMap openVmMemBusId ▸ openVmHost_ordersRanks P))
    (openVmHost_forcesAdmissible P) hLegal hComplete

/-- **Substitution equivalence, for OpenVM, order-free**: the two directions together. -/
theorem openVm_vmEquivalentOF [Fact p.Prime] {P : OpenVmParams p} {G G' : Guest p}
    (hLegal : ∀ c ∈ G ++ G',
      c.legalGuestOF (openVmGuestRules defaultBusMap openVmMemBusId) openVmMemAddress
        P.maxWindow openVmTimestampBound P.maxInteractions)
    (hSound : List.Forall₂ (fun c c' => c'.isSoundReplacementOf c
      (openVmBusSemanticsOF p defaultBusMap none)) G G')
    (hComplete : List.Forall₂ (fun c c' => (∀ v ∈ Circuit.vars c, v.powdrId?.isSome) ∧
      ∃ ds : Derivations p, Circuit.isCompleteReplacementOf c' c
        (openVmBusSemanticsOF p defaultBusMap none) ds) G G') :
    VmEquivalent (openVmHost P) G G' :=
  ⟨openVm_vmSoundReplacementOF hLegal hSound, openVm_vmCompleteReplacementOF hLegal hComplete⟩

end ApcOptimizer.OpenVM
