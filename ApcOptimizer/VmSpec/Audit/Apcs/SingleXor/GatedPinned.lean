import ApcOptimizer.VmSpec.Audit.Apcs.SingleXor.Layout

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

/-! **The pipeline's output with `is_valid` pinned to `1`: `Circuit.legalGuest` in full.** Every
    clause the checkers prove for the preceding stage carries over -- the circuits differ only by
    the `is_valid` factor on each multiplicity, which folds away against the pin. -/

namespace ApcOptimizer.OpenVM.SingleXor

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
    asg ⟨"is_valid", some 36⟩ = 1 :=
  gatedPinRules_hold asg halg (.var ⟨"is_valid", some 36⟩, 1) (by decide)

theorem gatedIsValid_ne_zero {asg : ChipAssignment babyBear}
    (halg : gatedPinned.satisfiesAlgebraic asg) :
    asg ⟨"is_valid", some 36⟩ ≠ 0 := by
  rw [gatedIsValid halg]; exact (show (1 : ZMod babyBear) ≠ 0 by decide)

/-- **The strengthened check passes, `is_valid` pinned**: every multiplicity is a literal times
    `is_valid`, legal only because the pin says `is_valid = 1`. -/
theorem gatedPinned_checkMultiplicitiesWith :
    checkMultiplicitiesWith apcRules.isStateful gatedPinned = true := by decide

theorem gatedPinned_legalMultiplicities :
    gatedPinned.statelessSendOnly apcRules ∧ gatedPinned.statefulPolarity apcRules :=
  checkMultiplicitiesWith_sound gatedPinned_checkMultiplicitiesWith rfl

/-- **The bridge half of the layout, by static analysis**: `bridgeCheck` normalizes the two bus-`0`
    payloads, sees the receive first and the send last with nothing between them, reads `d = 3` off
    the timestamps, and separates the two endpoints at payload position `1`. -/
theorem gatedBaseLin : Expression.toLin layoutVars gatedPinRules baseE = some baseF := by decide

theorem gatedBridgeCheck :
    bridgeCheck layoutVars gatedPinRules 0 gatedPinned 3 1 (.const 0) baseE (.const 4) = true := by decide

theorem gatedByteCheck :
    byteCheckAll layoutVars gatedPinRules gatedPinned.busInteractions witnesses = true := by decide

/-- **A real optimized APC has a step layout.** One arc — `(0, t) → (4, t + 3)` — and the six
    stateful interactions placed at `offsets`, read off the three surviving lt gadgets
    (`lt_gadget_offset`). Its three memory sends are byte-valued: two echo the read that preceded
    them, and the third is the `xor` the bitwise table computes (`isByte_of_xorEq`). -/
theorem gatedPinned_hasStepLayout {maxWindow : ℕ} (hw : 3 < maxWindow) :
    gatedPinned.hasStepLayout apcRules maxWindow openVmTimestampBound := by
  haveI : Fact (1 < babyBear) := ⟨by decide⟩
  intro asg halg hacc
  have hiv := gatedIsValid halg
  have hivne := gatedIsValid_ne_zero halg
  obtain ⟨nr0, hnr0, htr0⟩ : ∃ n : ℕ, n < 2 ^ 29 ∧
      asg ⟨"reads_aux__0__base__prev_timestamp_0", some 6⟩
        = asg ⟨"from_state__timestamp_0", some 1⟩ + ((((-1) - (n : ℤ)) : ℤ) : ZMod babyBear) := by
    have hacc12 := acceptsAt hacc 12 (by decide) _ rfl rfl
      (show asg ⟨"is_valid", some 36⟩ ≠ 0 from hivne)
    have hacc13 := acceptsAt hacc 13 (by decide) _ rfl rfl
      (show asg ⟨"is_valid", some 36⟩ ≠ 0 from hivne)
    simp only [gatedPinned, gated, BusInteraction.eval] at hacc12 hacc13
    obtain ⟨hb, ht⟩ := lookback_of_gadget (vs := layoutVars) (rules := gatedPinRules)
      (baseE := baseE) (baseF := baseF) (k := (-1))
      (tsE := .var ⟨"reads_aux__0__base__prev_timestamp_0", some 6⟩)
      (loE := payloadOf gatedPinned 12 0) (hiE := payloadOf gatedPinned 13 0)
      (gatedPinRules_hold asg halg) gatedBaseLin (by decide)
      hacc12 hacc13
    rw [Recipe.place_eq] at ht
    exact ⟨_, hb, ht⟩
  obtain ⟨nr1, hnr1, htr1⟩ : ∃ n : ℕ, n < 2 ^ 29 ∧
      asg ⟨"reads_aux__1__base__prev_timestamp_0", some 9⟩
        = asg ⟨"from_state__timestamp_0", some 1⟩ + (((0 - (n : ℤ)) : ℤ) : ZMod babyBear) := by
    have hacc14 := acceptsAt hacc 14 (by decide) _ rfl rfl
      (show asg ⟨"is_valid", some 36⟩ ≠ 0 from hivne)
    have hacc15 := acceptsAt hacc 15 (by decide) _ rfl rfl
      (show asg ⟨"is_valid", some 36⟩ ≠ 0 from hivne)
    simp only [gatedPinned, gated, BusInteraction.eval] at hacc14 hacc15
    obtain ⟨hb, ht⟩ := lookback_of_gadget (vs := layoutVars) (rules := gatedPinRules)
      (baseE := baseE) (baseF := baseF) (k := 0)
      (tsE := .var ⟨"reads_aux__1__base__prev_timestamp_0", some 9⟩)
      (loE := payloadOf gatedPinned 14 0) (hiE := payloadOf gatedPinned 15 0)
      (gatedPinRules_hold asg halg) gatedBaseLin (by decide)
      hacc14 hacc15
    rw [Recipe.place_eq] at ht
    exact ⟨_, hb, ht⟩
  obtain ⟨nw, hnw, htw⟩ : ∃ n : ℕ, n < 2 ^ 29 ∧
      asg ⟨"writes_aux__base__prev_timestamp_0", some 12⟩
        = asg ⟨"from_state__timestamp_0", some 1⟩ + (((1 - (n : ℤ)) : ℤ) : ZMod babyBear) := by
    have hacc16 := acceptsAt hacc 16 (by decide) _ rfl rfl
      (show asg ⟨"is_valid", some 36⟩ ≠ 0 from hivne)
    have hacc17 := acceptsAt hacc 17 (by decide) _ rfl rfl
      (show asg ⟨"is_valid", some 36⟩ ≠ 0 from hivne)
    simp only [gatedPinned, gated, BusInteraction.eval] at hacc16 hacc17
    obtain ⟨hb, ht⟩ := lookback_of_gadget (vs := layoutVars) (rules := gatedPinRules)
      (baseE := baseE) (baseF := baseF) (k := 1)
      (tsE := .var ⟨"writes_aux__base__prev_timestamp_0", some 12⟩)
      (loE := payloadOf gatedPinned 16 0) (hiE := payloadOf gatedPinned 17 0)
      (gatedPinRules_hold asg halg) gatedBaseLin (by decide)
      hacc16 hacc17
    rw [Recipe.place_eq] at ht
    exact ⟨_, hb, ht⟩
  -- The write's four limbs are the bitwise table's `xor` output, hence bytes.
  have hbit0 : accepts (p := babyBear) defaultBusMap
      { busId := 6, multiplicity := 1,
        payload := [asg ⟨"b__0_0", some 23⟩, asg ⟨"c__0_0", some 27⟩,
          asg ⟨"a__0_0", some 19⟩, 1] } :=
    accepts_congr_mult6
      (acceptsAt hacc 0 (by decide) _ rfl rfl (show asg ⟨"is_valid", some 36⟩ ≠ 0 from hivne))
  have ha0 : isByte (asg ⟨"a__0_0", some 19⟩) :=
    isByte_of_xorEq (bitwiseTable_extract hbit0).1 (bitwiseTable_extract hbit0).2.1
      (bitwiseTable_extract hbit0).2.2 rfl
  have hbit1 : accepts (p := babyBear) defaultBusMap
      { busId := 6, multiplicity := 1,
        payload := [asg ⟨"b__1_0", some 24⟩, asg ⟨"c__1_0", some 28⟩,
          asg ⟨"a__1_0", some 20⟩, 1] } :=
    accepts_congr_mult6
      (acceptsAt hacc 1 (by decide) _ rfl rfl (show asg ⟨"is_valid", some 36⟩ ≠ 0 from hivne))
  have ha1 : isByte (asg ⟨"a__1_0", some 20⟩) :=
    isByte_of_xorEq (bitwiseTable_extract hbit1).1 (bitwiseTable_extract hbit1).2.1
      (bitwiseTable_extract hbit1).2.2 rfl
  have hbit2 : accepts (p := babyBear) defaultBusMap
      { busId := 6, multiplicity := 1,
        payload := [asg ⟨"b__2_0", some 25⟩, asg ⟨"c__2_0", some 29⟩,
          asg ⟨"a__2_0", some 21⟩, 1] } :=
    accepts_congr_mult6
      (acceptsAt hacc 2 (by decide) _ rfl rfl (show asg ⟨"is_valid", some 36⟩ ≠ 0 from hivne))
  have ha2 : isByte (asg ⟨"a__2_0", some 21⟩) :=
    isByte_of_xorEq (bitwiseTable_extract hbit2).1 (bitwiseTable_extract hbit2).2.1
      (bitwiseTable_extract hbit2).2.2 rfl
  have hbit3 : accepts (p := babyBear) defaultBusMap
      { busId := 6, multiplicity := 1,
        payload := [asg ⟨"b__3_0", some 26⟩, asg ⟨"c__3_0", some 30⟩,
          asg ⟨"a__3_0", some 22⟩, 1] } :=
    accepts_congr_mult6
      (acceptsAt hacc 3 (by decide) _ rfl rfl (show asg ⟨"is_valid", some 36⟩ ≠ 0 from hivne))
  have ha3 : isByte (asg ⟨"a__3_0", some 22⟩) :=
    isByte_of_xorEq (bitwiseTable_extract hbit3).1 (bitwiseTable_extract hbit3).2.1
      (bitwiseTable_extract hbit3).2.2 rfl
  have hub : ∀ i : Fin gatedPinned.busInteractions.length,
      apcRules.isStateful (gatedPinned.busInteractions.get i).busId = true →
      ((gatedPinned.busInteractions.get i).eval asg).multiplicity ≠ 0 →
      (offsets nr0 nr1 nw).getD i.val 0 ≤ offsetUb.getD i.val 0 := by
    intro i hst _
    fin_cases i <;>
      simp [offsets, offsetUb, gatedPinned, gated, apcRules, openVmGuestRules, openVmIsStateful,
        defaultBusMap, OpenVmBusType.isStateful] at hst ⊢
  have hsendIdx : ∀ i : Fin gatedPinned.busInteractions.length,
      apcRules.isStateful (gatedPinned.busInteractions.get i).busId = true →
      ((gatedPinned.busInteractions.get i).eval asg).multiplicity = 1 →
      i.val ∈ [5, 7, 9, 11] ∧ (offsets nr0 nr1 nw).getD i.val 0 = offsetUb.getD i.val 0 := by
    intro i hst hm
    fin_cases i <;>
      simp_all [offsets, offsetUb, gatedPinned, gated, apcRules, openVmGuestRules,
        openVmIsStateful, defaultBusMap, OpenVmBusType.isStateful, BusInteraction.eval,
        Expression.eval, babyBear_negOne_ne_one]
  obtain ⟨hrecv, hsend, hother⟩ := bridgeCheck_sound gatedBridgeCheck (gatedPinRules_hold asg halg)
  refine ⟨_, _, _, 3, by norm_num, hw, hrecv, hsend, hother,
    fun i => (offsets nr0 nr1 nw).getD i.val 0, ?_, ?_⟩
  · -- The placement, offset by offset.
    rintro i ⟨hst, hm⟩
    fin_cases i
    · simp [gatedPinned, gated, apcRules, openVmGuestRules, openVmIsStateful, defaultBusMap,
        OpenVmBusType.isStateful] at hst
    · simp [gatedPinned, gated, apcRules, openVmGuestRules, openVmIsStateful, defaultBusMap,
        OpenVmBusType.isStateful] at hst
    · simp [gatedPinned, gated, apcRules, openVmGuestRules, openVmIsStateful, defaultBusMap,
        OpenVmBusType.isStateful] at hst
    · simp [gatedPinned, gated, apcRules, openVmGuestRules, openVmIsStateful, defaultBusMap,
        OpenVmBusType.isStateful] at hst
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
    · exact ⟨by simp [offsets, openVmTimestampBound, openVmTimestampBits]; omega,
        by simp [offsets]; omega,
        by simpa [offsets, baseE, gatedPinned, gated, BusInteraction.eval, Expression.eval, apcRules,
          openVmGuestRules, openVmTimestamp, Circuit.msgAt] using htw⟩
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
    · simp [gatedPinned, gated, apcRules, openVmGuestRules, openVmIsStateful, defaultBusMap,
        OpenVmBusType.isStateful] at hst
    · simp [gatedPinned, gated, apcRules, openVmGuestRules, openVmIsStateful, defaultBusMap,
        OpenVmBusType.isStateful] at hst
    · simp [gatedPinned, gated, apcRules, openVmGuestRules, openVmIsStateful, defaultBusMap,
        OpenVmBusType.isStateful] at hst
    · simp [gatedPinned, gated, apcRules, openVmGuestRules, openVmIsStateful, defaultBusMap,
        OpenVmBusType.isStateful] at hst
    · simp [gatedPinned, gated, apcRules, openVmGuestRules, openVmIsStateful, defaultBusMap,
        OpenVmBusType.isStateful] at hst
    · simp [gatedPinned, gated, apcRules, openVmGuestRules, openVmIsStateful, defaultBusMap,
        OpenVmBusType.isStateful] at hst
  · intro i hsend hlow
    have hordered : ∀ j : Fin gatedPinned.busInteractions.length, j < i →
        gatedPinned.activeMem apcRules asg j →
        apcRules.payloadOk (gatedPinned.msgAt asg j) := by
      intro j hji hactj
      obtain ⟨hmem, heq⟩ := hsendIdx i hsend.1.1 hsend.1.2
      refine hlow j ?_ hactj
      show (offsets nr0 nr1 nw).getD j.val 0 < (offsets nr0 nr1 nw).getD i.val 0
      rw [heq]
      exact lt_of_le_of_lt (hub j hactj.1.1 hactj.1.2)
        (offsetUb_dominates i.val hmem j.val (Fin.lt_def.mp hji))
    refine memSendsOk_of_sendsOk (byteCheck_sendsOk (gatedPinRules_hold asg halg) gatedByteCheck ?_)
      i hsend hordered
    intro i hi hsend hlow
    fin_cases i
    all_goals try exact absurd hi (by decide)
    show openVmPayloadOk defaultBusMap ((1 : ℕ), [(1 : ZMod babyBear), 8,
      asg ⟨"a__0_0", some 19⟩, asg ⟨"a__1_0", some 20⟩, asg ⟨"a__2_0", some 21⟩,
      asg ⟨"a__3_0", some 22⟩, asg ⟨"from_state__timestamp_0", some 1⟩ + 2])
    exact (openVmPayloadOk_mem_iff _ _ _ _ _ _).mpr
      ⟨ha0, ha1, ha2, ha3⟩

theorem gatedPinned_legalGuest {maxWindow maxInteractions : ℕ} (hw : 3 < maxWindow)
    (hi : 18 ≤ maxInteractions) :
    gatedPinned.legalGuest apcRules maxWindow openVmTimestampBound maxInteractions where
  sendOnly := gatedPinned_legalMultiplicities.1
  polarity := gatedPinned_legalMultiplicities.2
  stepLayout := gatedPinned_hasStepLayout hw
  size := by simpa [gatedPinned, gated] using hi

end ApcOptimizer.OpenVM.SingleXor
