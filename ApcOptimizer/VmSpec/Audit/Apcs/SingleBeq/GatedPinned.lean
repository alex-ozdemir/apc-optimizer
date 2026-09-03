import ApcOptimizer.VmSpec.Audit.Apcs.SingleBeq.Layout

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

/-! **The pipeline's output with `is_valid` pinned to `1`: `Circuit.legalGuest` in full.** Every
    clause the checkers prove for the preceding stage carries over -- the circuits differ only by
    the `is_valid` factor on each multiplicity and on the comparison constraint's right side, both
    of which fold away against the pin. -/

namespace ApcOptimizer.OpenVM.SingleBeq

/-- **`gated` fails `hasStepLayout` only because `is_valid` is unpinned** — pin it, and every
    clause the checkers proved for the preceding stage carries over verbatim. -/
def gatedPinRules : List (PinRule babyBear) :=
  gatedPinned.algebraicConstraints.filterMap pinRuleOf

theorem gatedPinRules_hold (asg : ChipAssignment babyBear)
    (halg : gatedPinned.satisfiesAlgebraic asg) :
    ∀ q ∈ gatedPinRules, q.1.eval asg = q.2 := by
  intro q hq
  obtain ⟨con, hcon, hpin⟩ := List.mem_filterMap.mp hq
  exact pinRuleOf_eval (by rw [hpin]) (halg con hcon)

theorem gatedIsValid {asg : ChipAssignment babyBear}
    (halg : gatedPinned.satisfiesAlgebraic asg) :
    asg ⟨"is_valid", some 31⟩ = 1 :=
  gatedPinRules_hold asg halg (.var ⟨"is_valid", some 31⟩, 1) (by decide)

theorem gatedIsValid_ne_zero {asg : ChipAssignment babyBear}
    (halg : gatedPinned.satisfiesAlgebraic asg) :
    asg ⟨"is_valid", some 31⟩ ≠ 0 := by
  rw [gatedIsValid halg]; exact (show (1 : ZMod babyBear) ≠ 0 by decide)

/-- **The strengthened check passes, `is_valid` pinned**: every multiplicity is a literal times
    `is_valid`, legal only because the pin says `is_valid = 1`. -/
theorem gatedPinned_checkMultiplicitiesWith :
    checkMultiplicitiesWith apcRules.isStateful gatedPinned = true := by decide

theorem gatedPinned_legalMultiplicities :
    gatedPinned.statelessSendOnly apcRules ∧ gatedPinned.statefulPolarity apcRules :=
  checkMultiplicitiesWith_sound gatedPinned_checkMultiplicitiesWith rfl

/-- **The bridge half of the layout, by static analysis.** The outgoing `pc` is not a literal here
    but `4 - 2 * cmp_result_0`: `bridgeCheck` normalizes it like any other payload and separates
    the two endpoints at position `1`, where they differ by the constant `d = 2`. -/
theorem gatedBaseLin : Expression.toLin layoutVars gatedPinRules baseE = some baseF := by decide

theorem gatedBridgeCheck :
    bridgeCheck layoutVars gatedPinRules 0 gatedPinned 2 1 (.const 0) baseE
        (.add (.const 4) (.mul (.const 2013265920)
          (.mul (.const 2) (.var ⟨"cmp_result_0", some 18⟩))))
      = true := by decide

theorem gatedByteCheck :
    byteCheckAll layoutVars gatedPinRules gatedPinned.busInteractions witnesses = true := by decide

/-- **A real optimized branch APC has a step layout.** One arc — `(0, t) → (4 - 2·cmp, t + 2)` —
    and the six stateful interactions placed at `offsets`, read off the two surviving lt gadgets
    (`lt_gadget_offset`). Both memory sends echo the read that preceded them, so the byte
    invariant is entirely decidable: a branch computes nothing it sends. -/
theorem gatedPinned_hasStepLayout {maxWindow : ℕ} (hw : 2 < maxWindow) :
    gatedPinned.hasStepLayout apcRules maxWindow openVmTimestampBound := by
  haveI : Fact (1 < babyBear) := ⟨by decide⟩
  intro asg halg hacc
  have hiv := gatedIsValid halg
  have hivne := gatedIsValid_ne_zero halg
  obtain ⟨nr0, hnr0, htr0⟩ : ∃ n : ℕ, n < 2 ^ 29 ∧
      asg ⟨"reads_aux__0__base__prev_timestamp_0", some 4⟩
        = asg ⟨"from_state__timestamp_0", some 1⟩ + ((((-1) - (n : ℤ)) : ℤ) : ZMod babyBear) := by
    have hacc6 := acceptsAt hacc 6 (by decide) _ rfl rfl
      (show asg ⟨"is_valid", some 31⟩ ≠ 0 from hivne)
    have hacc7 := acceptsAt hacc 7 (by decide) _ rfl rfl
      (show asg ⟨"is_valid", some 31⟩ ≠ 0 from hivne)
    simp only [gatedPinned, gated, BusInteraction.eval] at hacc6 hacc7
    obtain ⟨hb, ht⟩ := lookback_of_gadget (vs := layoutVars) (rules := gatedPinRules)
      (baseE := baseE) (baseF := baseF) (k := (-1))
      (tsE := .var ⟨"reads_aux__0__base__prev_timestamp_0", some 4⟩)
      (loE := payloadOf gatedPinned 6 0) (hiE := payloadOf gatedPinned 7 0)
      (gatedPinRules_hold asg halg) gatedBaseLin (by decide)
      hacc6 hacc7
    rw [Recipe.place_eq] at ht
    exact ⟨_, hb, ht⟩
  obtain ⟨nr1, hnr1, htr1⟩ : ∃ n : ℕ, n < 2 ^ 29 ∧
      asg ⟨"reads_aux__1__base__prev_timestamp_0", some 7⟩
        = asg ⟨"from_state__timestamp_0", some 1⟩ + (((0 - (n : ℤ)) : ℤ) : ZMod babyBear) := by
    have hacc8 := acceptsAt hacc 8 (by decide) _ rfl rfl
      (show asg ⟨"is_valid", some 31⟩ ≠ 0 from hivne)
    have hacc9 := acceptsAt hacc 9 (by decide) _ rfl rfl
      (show asg ⟨"is_valid", some 31⟩ ≠ 0 from hivne)
    simp only [gatedPinned, gated, BusInteraction.eval] at hacc8 hacc9
    obtain ⟨hb, ht⟩ := lookback_of_gadget (vs := layoutVars) (rules := gatedPinRules)
      (baseE := baseE) (baseF := baseF) (k := 0)
      (tsE := .var ⟨"reads_aux__1__base__prev_timestamp_0", some 7⟩)
      (loE := payloadOf gatedPinned 8 0) (hiE := payloadOf gatedPinned 9 0)
      (gatedPinRules_hold asg halg) gatedBaseLin (by decide)
      hacc8 hacc9
    rw [Recipe.place_eq] at ht
    exact ⟨_, hb, ht⟩
  -- `memOrdered` reads only the memory bus, so both tables are consulted only there: the bridge
  -- send sits at index `5`, after every memory send, and is never a `b` in `offsetUb_dominates`.
  have hub : ∀ i : Fin gatedPinned.busInteractions.length, gatedPinned.activeMem apcRules asg i →
      (offsets nr0 nr1).getD i.val 0 ≤ offsetUb.getD i.val 0 := by
    intro i hi
    obtain ⟨⟨hst, -⟩, hmem⟩ := hi
    fin_cases i <;>
      simp [offsets, offsetUb, gatedPinned, gated, apcRules, openVmGuestRules, openVmIsStateful,
        defaultBusMap, OpenVmBusType.isStateful, openVmMemBusId] at hst hmem ⊢
  have hsendIdx : ∀ i : Fin gatedPinned.busInteractions.length, gatedPinned.memSend apcRules asg i →
      i.val ∈ [1, 3] ∧ (offsets nr0 nr1).getD i.val 0 = offsetUb.getD i.val 0 := by
    intro i hi
    obtain ⟨⟨hst, hm⟩, hmem⟩ := hi
    fin_cases i <;>
      simp_all [offsets, offsetUb, gatedPinned, gated, apcRules, openVmGuestRules, openVmIsStateful,
        defaultBusMap, OpenVmBusType.isStateful, openVmMemBusId, Circuit.multAt,
        BusInteraction.eval, Expression.eval, babyBear_negOne_ne_one]
  obtain ⟨hrecv, hsend, hother⟩ := bridgeCheck_sound gatedBridgeCheck (gatedPinRules_hold asg halg)
  refine ⟨_, _, _, 2, by norm_num, hw, hrecv, hsend, hother,
    fun i => (offsets nr0 nr1).getD i.val 0, ?_, ?_⟩
  · -- The placement, offset by offset.
    rintro i ⟨hst, hm⟩
    fin_cases i
    · exact ⟨by simp [offsets, openVmTimestampBound, openVmTimestampBits]; omega,
        by simp [offsets]; omega,
        by simpa [offsets, baseE, gatedPinned, gated, BusInteraction.eval, Expression.eval, apcRules,
          openVmGuestRules, openVmTimestamp, Circuit.msgAt] using htr0⟩
    · exact ⟨by simp [offsets, openVmTimestampBound, openVmTimestampBits],
        by simp [offsets],
        by simp [offsets, baseE, gatedPinned, gated, BusInteraction.eval, Expression.eval, apcRules,
          openVmGuestRules, openVmTimestamp, Circuit.msgAt]⟩
    · exact ⟨by simp [offsets, openVmTimestampBound, openVmTimestampBits]; omega,
        by simp [offsets],
        by simpa [offsets, baseE, gatedPinned, gated, BusInteraction.eval, Expression.eval, apcRules,
          openVmGuestRules, openVmTimestamp, Circuit.msgAt] using htr1⟩
    · exact ⟨by simp [offsets, openVmTimestampBound, openVmTimestampBits],
        by simp [offsets],
        by simp [offsets, baseE, gatedPinned, gated, BusInteraction.eval, Expression.eval, apcRules,
          openVmGuestRules, openVmTimestamp, Circuit.msgAt]⟩
    · exact ⟨by simp [offsets, openVmTimestampBound, openVmTimestampBits],
        by simp [offsets],
        by simp [offsets, baseE, gatedPinned, gated, BusInteraction.eval, Expression.eval, apcRules,
          openVmGuestRules, openVmTimestamp, Circuit.msgAt, openVmMemBusId, openVmExecBusId]⟩
    · exact ⟨by simp [offsets, openVmTimestampBound, openVmTimestampBits],
        by simp [offsets],
        by simp [offsets, baseE, gatedPinned, gated, BusInteraction.eval, Expression.eval, apcRules,
          openVmGuestRules, openVmTimestamp, Circuit.msgAt, openVmMemBusId, openVmExecBusId]⟩
    all_goals
      simp [gatedPinned, gated, apcRules, openVmGuestRules, openVmIsStateful, defaultBusMap,
        OpenVmBusType.isStateful] at hst
  · -- The byte invariant, entirely by static analysis: every memory send is an echo.
    intro i hsend hlow
    have hordered : ∀ j : Fin gatedPinned.busInteractions.length, j < i →
        gatedPinned.activeMem apcRules asg j →
        apcRules.payloadOk (gatedPinned.msgAt asg j) := by
      intro j hji hactj
      obtain ⟨hmem, heq⟩ := hsendIdx i hsend
      refine hlow j ?_ hactj
      show (offsets nr0 nr1).getD j.val 0 < (offsets nr0 nr1).getD i.val 0
      rw [heq]
      exact lt_of_le_of_lt (hub j hactj)
        (offsetUb_dominates i.val hmem j.val (Fin.lt_def.mp hji))
    refine memSendsOk_of_sendsOk (byteCheck_sendsOk (gatedPinRules_hold asg halg) gatedByteCheck ?_)
      i hsend hordered
    intro i hi _ _
    fin_cases i <;> exact absurd hi (by decide)

theorem gatedPinned_legalGuest {maxWindow maxInteractions : ℕ} (hw : 2 < maxWindow)
    (hi : 10 ≤ maxInteractions) :
    gatedPinned.legalGuest apcRules maxWindow openVmTimestampBound maxInteractions where
  sendOnly := gatedPinned_legalMultiplicities.1
  polarity := gatedPinned_legalMultiplicities.2
  stepLayout := gatedPinned_hasStepLayout hw
  size := by simpa [gatedPinned, gated] using hi

end ApcOptimizer.OpenVM.SingleBeq
