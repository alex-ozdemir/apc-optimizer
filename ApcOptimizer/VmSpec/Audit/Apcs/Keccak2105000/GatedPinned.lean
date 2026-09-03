import ApcOptimizer.VmSpec.Audit.Apcs.Keccak2105000.Layout

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

/-! **Stage `040` with `is_valid` pinned to `1`: `Circuit.legalGuest` in full.** Every clause the
    checkers prove for stage `039` carries over -- the circuits differ only by the `is_valid`
    factor on each multiplicity, which folds away against the pin. -/

namespace ApcOptimizer.OpenVM.Keccak2105000

/-- **`gated` fails `hasStepLayout` only because `is_valid` is unpinned** — pin it, and
    every clause the checkers proved for `opt` carries over verbatim: `gated`
    is `opt`'s own algebraic constraints and bus interactions, each multiplicity
    additionally scaled by `is_valid`, which folds away to the literal it already was. -/
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
    asg ⟨"is_valid", some 137⟩ = 1 :=
  gatedPinRules_hold asg halg (.var ⟨"is_valid", some 137⟩, 1) (by decide)

theorem gatedIsValid_ne_zero {asg : ChipAssignment babyBear}
    (halg : gatedPinned.satisfiesAlgebraic asg) :
    asg ⟨"is_valid", some 137⟩ ≠ 0 := by
  rw [gatedIsValid halg]; exact (show (1 : ZMod babyBear) ≠ 0 by decide)

/-- **The strengthened check passes, `is_valid` pinned.** Same shape as `unopt`'s: every
    multiplicity is a literal times `is_valid`, legal only because the pin says `is_valid = 1`. -/
theorem gatedPinned_checkMultiplicitiesWith :
    checkMultiplicitiesWith apcRules.isStateful gatedPinned = true := by decide

theorem gatedPinned_legalMultiplicities :
    gatedPinned.statelessSendOnly apcRules ∧
      gatedPinned.statefulPolarity apcRules :=
  checkMultiplicitiesWith_sound gatedPinned_checkMultiplicitiesWith rfl

theorem gatedBaseLin : Expression.toLin layoutVars gatedPinRules baseE = some baseF := by decide

theorem gatedBridgeCheck :
    bridgeCheck layoutVars gatedPinRules 0 gatedPinned 11 1
        (.const 2105000)
        baseE
        (.add (.const 2105016) (.mul (.const 2013265920)
          (.mul (.const 192) (.var ⟨"cmp_result_3", some 126⟩))))
      = true := by decide

theorem gatedByteCheck :
    byteCheckAll layoutVars gatedPinRules gatedPinned.busInteractions witnesses = true := by
  decide

/-- **A pinned gated APC has a step layout.** Identical in shape to `opt_hasStepLayout`
    — same offsets, same gadgets, same byte witnesses — since pinning `is_valid` is exactly what
    collapses `gatedPinned` back to `opt`'s multiplicities. -/
theorem gatedPinned_hasStepLayout {maxWindow : ℕ} (hw : 11 < maxWindow) :
    gatedPinned.hasStepLayout apcRules maxWindow openVmTimestampBound := by
  haveI : Fact (1 < babyBear) := ⟨by decide⟩
  intro asg halg hacc
  have hiv := gatedIsValid halg
  have hivne := gatedIsValid_ne_zero halg
  obtain ⟨n0, hn0, ht0⟩ : ∃ n : ℕ, n < 2 ^ 29 ∧
      asg ⟨"reads_aux__0__base__prev_timestamp_0", some 6⟩
        = asg ⟨"from_state__timestamp_0", some 1⟩ + ((((-1) - (n : ℤ)) : ℤ) : ZMod babyBear) := by
    have hacc13 := acceptsAt hacc 13 (by decide) _ rfl rfl
      (show asg ⟨"is_valid", some 137⟩ ≠ 0 from hivne)
    have hacc14 := acceptsAt hacc 14 (by decide) _ rfl rfl
      (show asg ⟨"is_valid", some 137⟩ ≠ 0 from hivne)
    simp only [gatedPinned, gated, BusInteraction.eval] at hacc13 hacc14
    obtain ⟨hb, ht⟩ := lookback_of_gadget (vs := layoutVars) (rules := gatedPinRules)
      (baseE := baseE) (baseF := baseF) (k := (-1))
      (tsE := .var ⟨"reads_aux__0__base__prev_timestamp_0", some 6⟩)
      (loE := payloadOf gatedPinned 13 0) (hiE := payloadOf gatedPinned 14 0)
      (gatedPinRules_hold asg halg) gatedBaseLin (by decide)
      hacc13
      hacc14
    rw [Recipe.place_eq] at ht
    exact ⟨_, hb, ht⟩
  obtain ⟨nw0, hnw0, htw0⟩ : ∃ n : ℕ, n < 2 ^ 29 ∧
      asg ⟨"writes_aux__base__prev_timestamp_0", some 12⟩
        = asg ⟨"from_state__timestamp_0", some 1⟩ + (((1 - (n : ℤ)) : ℤ) : ZMod babyBear) := by
    have hacc15 := acceptsAt hacc 15 (by decide) _ rfl rfl
      (show asg ⟨"is_valid", some 137⟩ ≠ 0 from hivne)
    have hacc16 := acceptsAt hacc 16 (by decide) _ rfl rfl
      (show asg ⟨"is_valid", some 137⟩ ≠ 0 from hivne)
    simp only [gatedPinned, gated, BusInteraction.eval] at hacc15 hacc16
    obtain ⟨hb, ht⟩ := lookback_of_gadget (vs := layoutVars) (rules := gatedPinRules)
      (baseE := baseE) (baseF := baseF) (k := 1)
      (tsE := .var ⟨"writes_aux__base__prev_timestamp_0", some 12⟩)
      (loE := payloadOf gatedPinned 15 0) (hiE := payloadOf gatedPinned 16 0)
      (gatedPinRules_hold asg halg) gatedBaseLin (by decide)
      hacc15
      hacc16
    rw [Recipe.place_eq] at ht
    exact ⟨_, hb, ht⟩
  obtain ⟨nr1, hnr1, htr1⟩ : ∃ n : ℕ, n < 2 ^ 29 ∧
      asg ⟨"reads_aux__0__base__prev_timestamp_1", some 42⟩
        = asg ⟨"from_state__timestamp_0", some 1⟩ + (((2 - (n : ℤ)) : ℤ) : ZMod babyBear) := by
    have hacc17 := acceptsAt hacc 17 (by decide) _ rfl rfl
      (show asg ⟨"is_valid", some 137⟩ ≠ 0 from hivne)
    have hacc18 := acceptsAt hacc 18 (by decide) _ rfl rfl
      (show asg ⟨"is_valid", some 137⟩ ≠ 0 from hivne)
    simp only [gatedPinned, gated, BusInteraction.eval] at hacc17 hacc18
    obtain ⟨hb, ht⟩ := lookback_of_gadget (vs := layoutVars) (rules := gatedPinRules)
      (baseE := baseE) (baseF := baseF) (k := 2)
      (tsE := .var ⟨"reads_aux__0__base__prev_timestamp_1", some 42⟩)
      (loE := payloadOf gatedPinned 17 0) (hiE := payloadOf gatedPinned 18 0)
      (gatedPinRules_hold asg halg) gatedBaseLin (by decide)
      hacc17
      hacc18
    rw [Recipe.place_eq] at ht
    exact ⟨_, hb, ht⟩
  obtain ⟨nw1, hnw1, htw1⟩ : ∃ n : ℕ, n < 2 ^ 29 ∧
      asg ⟨"writes_aux__base__prev_timestamp_1", some 48⟩
        = asg ⟨"from_state__timestamp_0", some 1⟩ + (((4 - (n : ℤ)) : ℤ) : ZMod babyBear) := by
    have hacc19 := acceptsAt hacc 19 (by decide) _ rfl rfl
      (show asg ⟨"is_valid", some 137⟩ ≠ 0 from hivne)
    have hacc20 := acceptsAt hacc 20 (by decide) _ rfl rfl
      (show asg ⟨"is_valid", some 137⟩ ≠ 0 from hivne)
    simp only [gatedPinned, gated, BusInteraction.eval] at hacc19 hacc20
    obtain ⟨hb, ht⟩ := lookback_of_gadget (vs := layoutVars) (rules := gatedPinRules)
      (baseE := baseE) (baseF := baseF) (k := 4)
      (tsE := .var ⟨"writes_aux__base__prev_timestamp_1", some 48⟩)
      (loE := payloadOf gatedPinned 19 0) (hiE := payloadOf gatedPinned 20 0)
      (gatedPinRules_hold asg halg) gatedBaseLin (by decide)
      hacc19
      hacc20
    rw [Recipe.place_eq] at ht
    exact ⟨_, hb, ht⟩
  obtain ⟨nr3, hnr3, htr3⟩ : ∃ n : ℕ, n < 2 ^ 29 ∧
      asg ⟨"reads_aux__1__base__prev_timestamp_3", some 115⟩
        = asg ⟨"from_state__timestamp_0", some 1⟩ + (((9 - (n : ℤ)) : ℤ) : ZMod babyBear) := by
    have hacc21 := acceptsAt hacc 21 (by decide) _ rfl rfl
      (show asg ⟨"is_valid", some 137⟩ ≠ 0 from hivne)
    have hacc22 := acceptsAt hacc 22 (by decide) _ rfl rfl
      (show asg ⟨"is_valid", some 137⟩ ≠ 0 from hivne)
    simp only [gatedPinned, gated, BusInteraction.eval] at hacc21 hacc22
    obtain ⟨hb, ht⟩ := lookback_of_gadget (vs := layoutVars) (rules := gatedPinRules)
      (baseE := baseE) (baseF := baseF) (k := 9)
      (tsE := .var ⟨"reads_aux__1__base__prev_timestamp_3", some 115⟩)
      (loE := payloadOf gatedPinned 21 0) (hiE := payloadOf gatedPinned 22 0)
      (gatedPinRules_hold asg halg) gatedBaseLin (by decide)
      hacc21
      hacc22
    rw [Recipe.place_eq] at ht
    exact ⟨_, hb, ht⟩
  have hbit : accepts (p := babyBear) defaultBusMap
      { busId := 6, multiplicity := 1,
        payload := [asg ⟨"a__0_0", some 19⟩, 3,
          asg ⟨"a__0_0", some 19⟩ + 3 + 2013265920 * (2 * asg ⟨"a__0_2", some 91⟩), 1] } :=
    acceptsAt hacc 7 (by decide) _ (by simp [gatedPinned, gated,
      BusInteraction.eval, Expression.eval, hiv]) rfl (show (1 : ZMod babyBear) ≠ 0 by decide)
  replace hbit : isByte (asg ⟨"a__0_0", some 19⟩) ∧ isByte (3 : ZMod babyBear) ∧
      (asg ⟨"a__0_0", some 19⟩ + 3 + 2013265920 * (2 * asg ⟨"a__0_2", some 91⟩)).val
        = Nat.xor (asg ⟨"a__0_0", some 19⟩).val (3 : ZMod babyBear).val := hbit
  have ha02 : isByte (asg ⟨"a__0_2", some 91⟩) :=
    isByte_of_xorThree hbit.1
      (by rw [hbit.2.2, show (3 : ZMod babyBear).val = 3 from by decide])
      (by linear_combination (2 * asg ⟨"a__0_2", some 91⟩) * babyBear_negOne)
  have hub : ∀ i : Fin gatedPinned.busInteractions.length,
      apcRules.isStateful (gatedPinned.busInteractions.get i).busId = true →
      ((gatedPinned.busInteractions.get i).eval asg).multiplicity ≠ 0 →
      (offsets n0 nw0 nr1 nw1 nr3).getD i.val 0 ≤ offsetUb.getD i.val 0 := by
    intro i hst _
    fin_cases i <;>
      simp [offsets, offsetUb, gatedPinned, gated, apcRules,
        openVmGuestRules, openVmIsStateful, defaultBusMap, OpenVmBusType.isStateful] at hst ⊢
  have hsendIdx : ∀ i : Fin gatedPinned.busInteractions.length,
      apcRules.isStateful (gatedPinned.busInteractions.get i).busId = true →
      ((gatedPinned.busInteractions.get i).eval asg).multiplicity = 1 →
      i.val ∈ [1, 6, 8, 9, 11, 12] ∧
      (offsets n0 nw0 nr1 nw1 nr3).getD i.val 0 = offsetUb.getD i.val 0 := by
    intro i hst hm
    fin_cases i <;>
      simp_all [offsets, offsetUb, gatedPinned, gated, apcRules,
        openVmGuestRules, openVmIsStateful, defaultBusMap, OpenVmBusType.isStateful,
        BusInteraction.eval, Expression.eval, babyBear_negOne_ne_one]
  -- The bridge, by static analysis: `gatedBridgeCheck` is a `decide`.
  obtain ⟨hrecv, hsend, hother⟩ := bridgeCheck_sound gatedBridgeCheck (gatedPinRules_hold asg halg)
  refine ⟨_, _, _, 11, by norm_num, hw, hrecv, hsend, hother,
    fun i => (offsets n0 nw0 nr1 nw1 nr3).getD i.val 0, ?_, ?_⟩
  · -- The placement, offset by offset.
    rintro i ⟨hst, hm⟩
    fin_cases i
    · exact ⟨by simp [offsets, openVmTimestampBound, openVmTimestampBits]; omega,
        by simp [offsets]; omega,
        by simpa [offsets, baseE, gatedPinned, gated,
          BusInteraction.eval, Expression.eval, apcRules, openVmGuestRules, openVmTimestamp,
          Circuit.msgAt] using ht0⟩
    · exact ⟨by simp [offsets, openVmTimestampBound, openVmTimestampBits],
        by simp [offsets],
        by simp [offsets, baseE, gatedPinned, gated,
          BusInteraction.eval, Expression.eval, apcRules, openVmGuestRules, openVmTimestamp,
          Circuit.msgAt]⟩
    · exact ⟨by simp [offsets, openVmTimestampBound, openVmTimestampBits]; omega,
        by simp [offsets]; omega,
        by simpa [offsets, baseE, gatedPinned, gated,
          BusInteraction.eval, Expression.eval, apcRules, openVmGuestRules, openVmTimestamp,
          Circuit.msgAt] using htw0⟩
    · exact ⟨by simp [offsets, openVmTimestampBound, openVmTimestampBits],
        by simp [offsets],
        by simp [offsets, baseE, gatedPinned, gated,
          BusInteraction.eval, Expression.eval, apcRules, openVmGuestRules, openVmTimestamp,
          Circuit.msgAt, openVmMemBusId, openVmExecBusId]⟩
    · exact ⟨by simp [offsets, openVmTimestampBound, openVmTimestampBits]; omega,
        by simp [offsets]; omega,
        by simpa [offsets, baseE, gatedPinned, gated,
          BusInteraction.eval, Expression.eval, apcRules, openVmGuestRules, openVmTimestamp,
          Circuit.msgAt] using htr1⟩
    · exact ⟨by simp [offsets, openVmTimestampBound, openVmTimestampBits]; omega,
        by simp [offsets]; omega,
        by simpa [offsets, baseE, gatedPinned, gated,
          BusInteraction.eval, Expression.eval, apcRules, openVmGuestRules, openVmTimestamp,
          Circuit.msgAt] using htw1⟩
    · exact ⟨by simp [offsets, openVmTimestampBound, openVmTimestampBits],
        by simp [offsets],
        by simp [offsets, baseE, gatedPinned, gated,
          BusInteraction.eval, Expression.eval, apcRules, openVmGuestRules, openVmTimestamp,
          Circuit.msgAt]⟩
    · simp [gatedPinned, gated, apcRules, openVmGuestRules, openVmIsStateful,
        defaultBusMap, OpenVmBusType.isStateful] at hst
    · exact ⟨by simp [offsets, openVmTimestampBound, openVmTimestampBits],
        by simp [offsets],
        by simp [offsets, baseE, gatedPinned, gated,
          BusInteraction.eval, Expression.eval, apcRules, openVmGuestRules, openVmTimestamp,
          Circuit.msgAt]⟩
    · exact ⟨by simp [offsets, openVmTimestampBound, openVmTimestampBits],
        by simp [offsets],
        by simp [offsets, baseE, gatedPinned, gated,
          BusInteraction.eval, Expression.eval, apcRules, openVmGuestRules, openVmTimestamp,
          Circuit.msgAt]⟩
    · exact ⟨by simp [offsets, openVmTimestampBound, openVmTimestampBits]; omega,
        by simp [offsets]; omega,
        by simpa [offsets, baseE, gatedPinned, gated,
          BusInteraction.eval, Expression.eval, apcRules, openVmGuestRules, openVmTimestamp,
          Circuit.msgAt] using htr3⟩
    · exact ⟨by simp [offsets, openVmTimestampBound, openVmTimestampBits],
        by simp [offsets],
        by simp [offsets, baseE, gatedPinned, gated,
          BusInteraction.eval, Expression.eval, apcRules, openVmGuestRules, openVmTimestamp,
          Circuit.msgAt]⟩
    · exact ⟨by simp [offsets, openVmTimestampBound, openVmTimestampBits],
        by simp [offsets],
        by simp [offsets, baseE, gatedPinned, gated,
          BusInteraction.eval, Expression.eval, apcRules, openVmGuestRules, openVmTimestamp,
          Circuit.msgAt, openVmMemBusId, openVmExecBusId]⟩
    all_goals
      simp [gatedPinned, gated, apcRules, openVmGuestRules, openVmIsStateful,
        defaultBusMap, OpenVmBusType.isStateful] at hst
  · -- The byte invariant, by static analysis: only the masked write is left by hand. What used to
    -- be `memOrdered` (`offsetUb_dominates`) is inlined here, converting the caller's
    -- `place`-ordered hypothesis into the index order `byteCheck_sendsOk` expects.
    intro i hsend hlow
    have hordered : ∀ j : Fin gatedPinned.busInteractions.length, j < i →
        gatedPinned.activeMem apcRules asg j →
        apcRules.payloadOk (gatedPinned.msgAt asg j) := by
      intro j hji hactj
      obtain ⟨hmem, heq⟩ := hsendIdx i hsend.1.1 hsend.1.2
      refine hlow j ?_ hactj
      show (offsets n0 nw0 nr1 nw1 nr3).getD j.val 0
        < (offsets n0 nw0 nr1 nw1 nr3).getD i.val 0
      rw [heq]
      exact lt_of_le_of_lt (hub j hactj.1.1 hactj.1.2)
        (offsetUb_dominates i.val hmem j.val (Fin.lt_def.mp hji))
    refine memSendsOk_of_sendsOk (byteCheck_sendsOk (gatedPinRules_hold asg halg) gatedByteCheck ?_)
      i hsend hordered
    intro i hi hsend hlow
    fin_cases i
    all_goals try exact absurd hi (by decide)
    show openVmPayloadOk defaultBusMap ((1 : ℕ), [(1 : ZMod babyBear), 44,
      asg ⟨"a__0_2", some 91⟩, 0, 0, 0, asg ⟨"from_state__timestamp_0", some 1⟩ + 9])
    exact (openVmPayloadOk_mem_iff _ _ _ _ _ _).mpr ⟨ha02, isByte_zero, isByte_zero, isByte_zero⟩

theorem gatedPinned_legalGuest {maxWindow maxInteractions : ℕ} (hw : 11 < maxWindow)
    (hi : 23 ≤ maxInteractions) :
    gatedPinned.legalGuest apcRules maxWindow openVmTimestampBound maxInteractions where
  sendOnly := gatedPinned_legalMultiplicities.1
  polarity := gatedPinned_legalMultiplicities.2
  stepLayout := gatedPinned_hasStepLayout hw
  size := by simpa [gatedPinned, gated] using hi

end ApcOptimizer.OpenVM.Keccak2105000
