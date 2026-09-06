import ApcOptimizer.VmSpec.Legal

set_option autoImplicit false

/-! # A candidate `legalGuest` compatible with `BusSemantics.admissible` for OpenVM.

    OF means "order-free", because we target the order-free variant of `BusSemantics.admissible`
    (`openVmBusSemanticsOF`) rather than the positional one (`openVmBusSemantics`).  -/

variable {p : ℕ}

--------- The per-chip memory discipline ---------

/-- **Proposed extension for `StepLayout`.** Adds the memory-access discipline: a chip's memory
    traffic is a set of *accesses*, each a `getPrevious`/`setNew` pair at one address, no two
    sending simultaneously, all sending inside the window. -/
structure StepLayoutOF {p : ℕ} (c : Circuit p) (r : GuestBusRules p) (asg : ChipAssignment p)
    (memAddress : BusMessage p → List (Option (ZMod p)))
    (maxWindow maxLookback : ℕ)
    extends StepLayout c r asg maxWindow maxLookback where

  /-- Memory sends have distinct times. -/
  sendTimesDistinct : ∀ i j : Fin c.busInteractions.length,
    c.memSend r asg i → c.memSend r asg j →
      memAddress (c.msgAt asg i) = memAddress (c.msgAt asg j) →
        toStepLayout.tOffset i = toStepLayout.tOffset j → i = j

  /-- Memory sends are in-window. -/
  sendInWindow : ∀ i : Fin c.busInteractions.length,
    c.memSend r asg i → 0 ≤ toStepLayout.tOffset i ∧ toStepLayout.tOffset i < toStepLayout.tWindow

  /-- Any pre-window interactions are memory receives. -/
  negOffsetOnlyMemRecv : ∀ i : Fin c.busInteractions.length,
    c.activeStateful r asg i → toStepLayout.tOffset i < 0 →
      (c.busInteractions.get i).busId = r.memBusId ∧ c.multAt asg i = -1

  /-- Memory accesses are paired. This function is the pairing; its requirements follow.

      This function is not important for other accesses. -/
  memPartner : Fin c.busInteractions.length → Fin c.busInteractions.length

  /-- The pairing is closed on memory interactions and is a fixpoint-free involution there. -/
  memPartner_invol : ∀ i : Fin c.busInteractions.length,
    (c.busInteractions.get i).busId = r.memBusId →
      memPartner (memPartner i) = i ∧ memPartner i ≠ i ∧
        (c.busInteractions.get (memPartner i)).busId = r.memBusId

  /-- Sends and receives are paired. -/
  memPartner_mult : ∀ i : Fin c.busInteractions.length,
    (c.busInteractions.get i).busId = r.memBusId →
      c.multAt asg (memPartner i) = - c.multAt asg i ∧
      memAddress (c.msgAt asg i) = memAddress (c.msgAt asg (memPartner i))

  /-- Receives are constrained to preceed sends. (Typically via range-checks.) -/
  memPartner_time : ∀ i : Fin c.busInteractions.length,
    (c.busInteractions.get i).busId = r.memBusId → c.multAt asg i = -1 →
      toStepLayout.tOffset i < toStepLayout.tOffset (memPartner i)

/-- Every assignment to `c` lays out as one instruction step *with* the memory-access discipline. -/
def Circuit.hasStepLayoutOF (c : Circuit p) (r : GuestBusRules p)
    (memAddress : BusMessage p → List (Option (ZMod p))) (maxWindow maxLookback : ℕ) : Prop :=
  ∀ asg : ChipAssignment p, c.satisfiesAlgebraic asg → c.satisfiesStateless r asg →
    Nonempty (StepLayoutOF c r asg memAddress maxWindow maxLookback)

/-- Our new, order-free legality condition. -/
structure Circuit.legalGuestOF (c : Circuit p) (r : GuestBusRules p)
    (memAddress : BusMessage p → List (Option (ZMod p)))
    (maxWindow maxLookback maxInteractions : ℕ) : Prop where
  sendOnly : c.statelessSendOnly r
  polarity : c.statefulPolarity r
  stepLayout : c.hasStepLayoutOF r memAddress maxWindow maxLookback
  size : c.busInteractions.length ≤ maxInteractions
  /-- Any assignment that interacts with register 0 has value 0.

      TODO(AO): study APCs that interact with register 0 to see if this requirement is correctly
      phrased. I have not seen such APCs yet. -/
  x0Zero : ∀ asg : ChipAssignment p, c.satisfiesAlgebraic asg → c.satisfiesStateless r asg →
    ∀ i : Fin c.busInteractions.length, c.memSend r asg i →
      (c.msgAt asg i).2[0]? = some 1 → (c.msgAt asg i).2[1]? = some 0 →
        (c.msgAt asg i).2[2]? = some 0 ∧ (c.msgAt asg i).2[3]? = some 0 ∧
          (c.msgAt asg i).2[4]? = some 0 ∧ (c.msgAt asg i).2[5]? = some 0


--------- Useful weakenings ---------

/-- `StepLayoutOF` is a `StepLayout` with more clauses, so the old obligation still follows. -/
theorem Circuit.hasStepLayoutOF.toHasStepLayout {c : Circuit p} {r : GuestBusRules p}
    {memAddress : BusMessage p → List (Option (ZMod p))} {maxWindow maxLookback : ℕ}
    (h : c.hasStepLayoutOF r memAddress maxWindow maxLookback) :
    c.hasStepLayout r maxWindow maxLookback :=
  fun asg h1 h2 => (h asg h1 h2).map (fun L => L.toStepLayout)

/-- …hence `legalGuestOF` implies `legalGuest`, which is what lets the existing soundness
    development run unchanged under the stronger legality. -/
theorem Circuit.legalGuestOF.toLegalGuest {c : Circuit p} {r : GuestBusRules p}
    {memAddress : BusMessage p → List (Option (ZMod p))}
    {maxWindow maxLookback maxInteractions : ℕ}
    (h : c.legalGuestOF r memAddress maxWindow maxLookback maxInteractions) :
    c.legalGuest r maxWindow maxLookback maxInteractions where
  sendOnly := h.sendOnly
  polarity := h.polarity
  stepLayout := h.stepLayout.toHasStepLayout
  size := h.size
