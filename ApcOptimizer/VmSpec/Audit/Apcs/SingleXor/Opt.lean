import ApcOptimizer.VmSpec.Audit.Apcs.SingleXor.Layout

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

/-! **The last `trivial_simp` stage: `Circuit.legalGuest` in full.** Every multiplicity is a field
    literal, so the constant-folding tier of `Audit/SendOnlyPolarity.lean` settles both
    multiplicity clauses, and the layout is read off the three surviving lt gadgets. -/

namespace ApcOptimizer.OpenVM.SingleXor

/-- **The static check passes.** Every multiplicity this stage carries is a field literal, so
    `Expression.foldConst` resolves all 18 of them and `decide` closes the check in the kernel. -/
theorem opt_checkMultiplicities :
    checkMultiplicities apcRules.isStateful opt = true := by decide

theorem opt_legalMultiplicities :
    opt.statelessSendOnly apcRules ∧ opt.statefulPolarity apcRules :=
  checkMultiplicities_sound opt_checkMultiplicities rfl

/-- **The optimized APC has no padding row**: its multiplicities are literals, and one of them is
    nonzero under every assignment — so unlike `gated_not_hasStepLayout`'s row, no assignment makes
    this circuit silent. -/
theorem opt_no_padding_row (asg : ChipAssignment babyBear) :
    ¬ ∀ bi ∈ opt.busInteractions, (bi.eval asg).multiplicity = 0 := by
  intro h
  have hne := h (opt.busInteractions.get ⟨0, by decide⟩) (List.get_mem _ _)
  simp only [opt, BusInteraction.eval, Expression.eval, List.get] at hne
  exact absurd hne (by decide)

/-- The pin rules this stage's own constraints supply: none, it has no constraints left. -/
def optPinRules : List (PinRule babyBear) :=
  opt.algebraicConstraints.filterMap pinRuleOf

theorem optPinRules_hold (asg : ChipAssignment babyBear)
    (halg : opt.satisfiesAlgebraic asg) : ∀ q ∈ optPinRules, q.1.eval asg = q.2 := by
  intro q hq
  obtain ⟨con, hcon, hpin⟩ := List.mem_filterMap.mp hq
  exact pinRuleOf_eval (by rw [hpin]) (halg con hcon)

/-- **The bridge half of the layout, by static analysis**: `bridgeCheck` normalizes the two bus-`0`
    payloads, sees the receive first and the send last with nothing between them, reads `d = 3` off
    the timestamps, and separates the two endpoints at payload position `1`. -/
theorem optBaseLin : Expression.toLin layoutVars optPinRules baseE = some baseF := by decide

theorem optBridgeCheck :
    bridgeCheck layoutVars optPinRules 0 opt 3 1 (.const 0) baseE (.const 4) = true := by decide

theorem optByteCheck :
    byteCheckAll layoutVars optPinRules opt.busInteractions witnesses = true := by decide

/-- **A real optimized APC has a step layout.** One arc — `(0, t) → (4, t + 3)` — and the six
    stateful interactions placed at `offsets`, read off the three surviving lt gadgets
    (`lt_gadget_offset`). Its three memory sends are byte-valued: two echo the read that preceded
    them, and the third is the `xor` the bitwise table computes (`isByte_of_xorEq`). -/
theorem opt_hasStepLayout {maxWindow : ℕ} (hw : 3 < maxWindow) :
    opt.hasStepLayout apcRules maxWindow openVmTimestampBound := by
  haveI : Fact (1 < babyBear) := ⟨by decide⟩
  intro asg halg hacc
  obtain ⟨nr0, hnr0, htr0⟩ : ∃ n : ℕ, n < 2 ^ 29 ∧
      asg ⟨"reads_aux__0__base__prev_timestamp_0", some 6⟩
        = asg ⟨"from_state__timestamp_0", some 1⟩ + ((((-1) - (n : ℤ)) : ℤ) : ZMod babyBear) := by
    obtain ⟨hb, ht⟩ := lookback_of_gadget (vs := layoutVars) (rules := optPinRules)
      (baseE := baseE) (baseF := baseF) (k := (-1))
      (tsE := .var ⟨"reads_aux__0__base__prev_timestamp_0", some 6⟩)
      (loE := payloadOf opt 12 0) (hiE := payloadOf opt 13 0)
      (optPinRules_hold asg halg) optBaseLin (by decide)
      (acceptsAt hacc 12 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
      (acceptsAt hacc 13 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
    rw [Recipe.place_eq] at ht
    exact ⟨_, hb, ht⟩
  obtain ⟨nr1, hnr1, htr1⟩ : ∃ n : ℕ, n < 2 ^ 29 ∧
      asg ⟨"reads_aux__1__base__prev_timestamp_0", some 9⟩
        = asg ⟨"from_state__timestamp_0", some 1⟩ + (((0 - (n : ℤ)) : ℤ) : ZMod babyBear) := by
    obtain ⟨hb, ht⟩ := lookback_of_gadget (vs := layoutVars) (rules := optPinRules)
      (baseE := baseE) (baseF := baseF) (k := 0)
      (tsE := .var ⟨"reads_aux__1__base__prev_timestamp_0", some 9⟩)
      (loE := payloadOf opt 14 0) (hiE := payloadOf opt 15 0)
      (optPinRules_hold asg halg) optBaseLin (by decide)
      (acceptsAt hacc 14 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
      (acceptsAt hacc 15 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
    rw [Recipe.place_eq] at ht
    exact ⟨_, hb, ht⟩
  obtain ⟨nw, hnw, htw⟩ : ∃ n : ℕ, n < 2 ^ 29 ∧
      asg ⟨"writes_aux__base__prev_timestamp_0", some 12⟩
        = asg ⟨"from_state__timestamp_0", some 1⟩ + (((1 - (n : ℤ)) : ℤ) : ZMod babyBear) := by
    obtain ⟨hb, ht⟩ := lookback_of_gadget (vs := layoutVars) (rules := optPinRules)
      (baseE := baseE) (baseF := baseF) (k := 1)
      (tsE := .var ⟨"writes_aux__base__prev_timestamp_0", some 12⟩)
      (loE := payloadOf opt 16 0) (hiE := payloadOf opt 17 0)
      (optPinRules_hold asg halg) optBaseLin (by decide)
      (acceptsAt hacc 16 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
      (acceptsAt hacc 17 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
    rw [Recipe.place_eq] at ht
    exact ⟨_, hb, ht⟩
  -- The write's four limbs are the bitwise table's `xor` output, hence bytes.
  have hbit0 : accepts (p := babyBear) defaultBusMap
      { busId := 6, multiplicity := 1,
        payload := [asg ⟨"b__0_0", some 23⟩, asg ⟨"c__0_0", some 27⟩,
          asg ⟨"a__0_0", some 19⟩, 1] } :=
    acceptsAt hacc 0 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide)
  have ha0 : isByte (asg ⟨"a__0_0", some 19⟩) :=
    isByte_of_xorEq (bitwiseTable_extract hbit0).1 (bitwiseTable_extract hbit0).2.1
      (bitwiseTable_extract hbit0).2.2 rfl
  have hbit1 : accepts (p := babyBear) defaultBusMap
      { busId := 6, multiplicity := 1,
        payload := [asg ⟨"b__1_0", some 24⟩, asg ⟨"c__1_0", some 28⟩,
          asg ⟨"a__1_0", some 20⟩, 1] } :=
    acceptsAt hacc 1 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide)
  have ha1 : isByte (asg ⟨"a__1_0", some 20⟩) :=
    isByte_of_xorEq (bitwiseTable_extract hbit1).1 (bitwiseTable_extract hbit1).2.1
      (bitwiseTable_extract hbit1).2.2 rfl
  have hbit2 : accepts (p := babyBear) defaultBusMap
      { busId := 6, multiplicity := 1,
        payload := [asg ⟨"b__2_0", some 25⟩, asg ⟨"c__2_0", some 29⟩,
          asg ⟨"a__2_0", some 21⟩, 1] } :=
    acceptsAt hacc 2 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide)
  have ha2 : isByte (asg ⟨"a__2_0", some 21⟩) :=
    isByte_of_xorEq (bitwiseTable_extract hbit2).1 (bitwiseTable_extract hbit2).2.1
      (bitwiseTable_extract hbit2).2.2 rfl
  have hbit3 : accepts (p := babyBear) defaultBusMap
      { busId := 6, multiplicity := 1,
        payload := [asg ⟨"b__3_0", some 26⟩, asg ⟨"c__3_0", some 30⟩,
          asg ⟨"a__3_0", some 22⟩, 1] } :=
    acceptsAt hacc 3 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide)
  have ha3 : isByte (asg ⟨"a__3_0", some 22⟩) :=
    isByte_of_xorEq (bitwiseTable_extract hbit3).1 (bitwiseTable_extract hbit3).2.1
      (bitwiseTable_extract hbit3).2.2 rfl
  have hub : ∀ i : Fin opt.busInteractions.length,
      apcRules.isStateful (opt.busInteractions.get i).busId = true →
      ((opt.busInteractions.get i).eval asg).multiplicity ≠ 0 →
      (offsets nr0 nr1 nw).getD i.val 0 ≤ offsetUb.getD i.val 0 := by
    intro i hst _
    fin_cases i <;>
      simp [offsets, offsetUb, opt, apcRules, openVmGuestRules, openVmIsStateful,
        defaultBusMap, OpenVmBusType.isStateful] at hst ⊢
  have hsendIdx : ∀ i : Fin opt.busInteractions.length,
      apcRules.isStateful (opt.busInteractions.get i).busId = true →
      ((opt.busInteractions.get i).eval asg).multiplicity = 1 →
      i.val ∈ [5, 7, 9, 11] ∧ (offsets nr0 nr1 nw).getD i.val 0 = offsetUb.getD i.val 0 := by
    intro i hst hm
    fin_cases i <;>
      simp_all [offsets, offsetUb, opt, apcRules, openVmGuestRules,
        openVmIsStateful, defaultBusMap, OpenVmBusType.isStateful, BusInteraction.eval,
        Expression.eval, babyBear_negOne_ne_one]
  obtain ⟨hrecv, hsend, hother⟩ := bridgeCheck_sound optBridgeCheck (optPinRules_hold asg halg)
  refine ⟨_, _, _, 3, by norm_num, hw, hrecv, hsend, hother,
    fun i => (offsets nr0 nr1 nw).getD i.val 0, ?_, ?_⟩
  · -- The placement, offset by offset.
    rintro i ⟨hst, hm⟩
    fin_cases i
    · simp [opt, apcRules, openVmGuestRules, openVmIsStateful, defaultBusMap,
        OpenVmBusType.isStateful] at hst
    · simp [opt, apcRules, openVmGuestRules, openVmIsStateful, defaultBusMap,
        OpenVmBusType.isStateful] at hst
    · simp [opt, apcRules, openVmGuestRules, openVmIsStateful, defaultBusMap,
        OpenVmBusType.isStateful] at hst
    · simp [opt, apcRules, openVmGuestRules, openVmIsStateful, defaultBusMap,
        OpenVmBusType.isStateful] at hst
    · exact ⟨by simp [offsets, openVmTimestampBound, openVmTimestampBits]; omega,
        by simp [offsets]; omega,
        by simpa [offsets, baseE, opt, BusInteraction.eval, Expression.eval, apcRules,
          openVmGuestRules, openVmTimestamp, Circuit.msgAt] using htr0⟩
    · exact ⟨by simp [offsets, openVmTimestampBound, openVmTimestampBits],
        by simp [offsets],
        by simp [offsets, baseE, opt, BusInteraction.eval, Expression.eval, apcRules,
          openVmGuestRules, openVmTimestamp, Circuit.msgAt]⟩
    · exact ⟨by simp [offsets, openVmTimestampBound, openVmTimestampBits]; omega,
        by simp [offsets],
        by simpa [offsets, baseE, opt, BusInteraction.eval, Expression.eval, apcRules,
          openVmGuestRules, openVmTimestamp, Circuit.msgAt] using htr1⟩
    · exact ⟨by simp [offsets, openVmTimestampBound, openVmTimestampBits],
        by simp [offsets],
        by simp [offsets, baseE, opt, BusInteraction.eval, Expression.eval, apcRules,
          openVmGuestRules, openVmTimestamp, Circuit.msgAt]⟩
    · exact ⟨by simp [offsets, openVmTimestampBound, openVmTimestampBits]; omega,
        by simp [offsets]; omega,
        by simpa [offsets, baseE, opt, BusInteraction.eval, Expression.eval, apcRules,
          openVmGuestRules, openVmTimestamp, Circuit.msgAt] using htw⟩
    · exact ⟨by simp [offsets, openVmTimestampBound, openVmTimestampBits],
        by simp [offsets],
        by simp [offsets, baseE, opt, BusInteraction.eval, Expression.eval, apcRules,
          openVmGuestRules, openVmTimestamp, Circuit.msgAt]⟩
    · exact ⟨by simp [offsets, openVmTimestampBound, openVmTimestampBits],
        by simp [offsets],
        by simp [offsets, baseE, opt, BusInteraction.eval, Expression.eval, apcRules,
          openVmGuestRules, openVmTimestamp, Circuit.msgAt, openVmMemBusId, openVmExecBusId]⟩
    · exact ⟨by simp [offsets, openVmTimestampBound, openVmTimestampBits],
        by simp [offsets],
        by simp [offsets, baseE, opt, BusInteraction.eval, Expression.eval, apcRules,
          openVmGuestRules, openVmTimestamp, Circuit.msgAt, openVmMemBusId, openVmExecBusId]⟩
    · simp [opt, apcRules, openVmGuestRules, openVmIsStateful, defaultBusMap,
        OpenVmBusType.isStateful] at hst
    · simp [opt, apcRules, openVmGuestRules, openVmIsStateful, defaultBusMap,
        OpenVmBusType.isStateful] at hst
    · simp [opt, apcRules, openVmGuestRules, openVmIsStateful, defaultBusMap,
        OpenVmBusType.isStateful] at hst
    · simp [opt, apcRules, openVmGuestRules, openVmIsStateful, defaultBusMap,
        OpenVmBusType.isStateful] at hst
    · simp [opt, apcRules, openVmGuestRules, openVmIsStateful, defaultBusMap,
        OpenVmBusType.isStateful] at hst
    · simp [opt, apcRules, openVmGuestRules, openVmIsStateful, defaultBusMap,
        OpenVmBusType.isStateful] at hst
  · intro i hsend hlow
    have hordered : ∀ j : Fin opt.busInteractions.length, j < i →
        opt.activeMem apcRules asg j →
        apcRules.payloadOk (opt.msgAt asg j) := by
      intro j hji hactj
      obtain ⟨hmem, heq⟩ := hsendIdx i hsend.1.1 hsend.1.2
      refine hlow j ?_ hactj
      show (offsets nr0 nr1 nw).getD j.val 0 < (offsets nr0 nr1 nw).getD i.val 0
      rw [heq]
      exact lt_of_le_of_lt (hub j hactj.1.1 hactj.1.2)
        (offsetUb_dominates i.val hmem j.val (Fin.lt_def.mp hji))
    refine memSendsOk_of_sendsOk (byteCheck_sendsOk (optPinRules_hold asg halg) optByteCheck ?_)
      i hsend hordered
    intro i hi hsend hlow
    fin_cases i
    all_goals try exact absurd hi (by decide)
    show openVmPayloadOk defaultBusMap ((1 : ℕ), [(1 : ZMod babyBear), 8,
      asg ⟨"a__0_0", some 19⟩, asg ⟨"a__1_0", some 20⟩, asg ⟨"a__2_0", some 21⟩,
      asg ⟨"a__3_0", some 22⟩, asg ⟨"from_state__timestamp_0", some 1⟩ + 2])
    exact (openVmPayloadOk_mem_iff _ _ _ _ _ _).mpr
      ⟨ha0, ha1, ha2, ha3⟩

theorem opt_legalGuest {maxWindow maxInteractions : ℕ} (hw : 3 < maxWindow)
    (hi : 18 ≤ maxInteractions) :
    opt.legalGuest apcRules maxWindow openVmTimestampBound maxInteractions where
  sendOnly := opt_legalMultiplicities.1
  polarity := opt_legalMultiplicities.2
  stepLayout := opt_hasStepLayout hw
  size := by simpa [opt] using hi

end ApcOptimizer.OpenVM.SingleXor
