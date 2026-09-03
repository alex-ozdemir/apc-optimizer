import ApcOptimizer.VmSpec.Audit.Apcs.Keccak2105000.Layout

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

/-! **Stage `039_trivial_simp`: `Circuit.legalGuest` in full.** Every multiplicity is a field
    literal, so the constant-folding tier of `Audit/SendOnlyPolarity.lean` settles both
    multiplicity clauses, and the layout is read off the five surviving lt gadgets. -/

namespace ApcOptimizer.OpenVM.Keccak2105000

/-- **The static check passes on a real optimized APC.** Every multiplicity stage `039` carries is
    a field literal, so `Expression.foldConst` — `Audit/SendOnlyPolarity.lean`'s first and only
    tier — resolves all 23 of them, and `decide` closes the check in the kernel. No case analysis
    over the circuit is written by hand. -/
theorem opt_checkMultiplicities :
    checkMultiplicities apcRules.isStateful opt = true := by decide

/-- **Both multiplicity clauses of `Circuit.legalGuest`, for a real optimized APC**, discharged by
    `checkMultiplicities_sound` from the `Bool` above rather than by a proof about this particular
    circuit. -/
theorem opt_legalMultiplicities :
    opt.statelessSendOnly apcRules ∧ opt.statefulPolarity apcRules :=
  checkMultiplicities_sound opt_checkMultiplicities rfl

/-- **The optimized APC has no padding row**: its multiplicities are literals, and one of them is
    nonzero under every assignment — so unlike `gated_not_hasStepLayout`'s row, no
    assignment makes this circuit silent. -/
theorem opt_no_padding_row (asg : ChipAssignment babyBear) :
    ¬ ∀ bi ∈ opt.busInteractions, (bi.eval asg).multiplicity = 0 := by
  intro h
  have hne := h (opt.busInteractions.get ⟨0, by decide⟩) (List.get_mem _ _)
  simp only [opt, BusInteraction.eval, Expression.eval, List.get] at hne
  exact absurd hne (by decide)

/-- The pin rules the optimized APC's own constraints supply. -/
def optPinRules : List (PinRule babyBear) :=
  opt.algebraicConstraints.filterMap pinRuleOf

theorem optPinRules_hold (asg : ChipAssignment babyBear)
    (halg : opt.satisfiesAlgebraic asg) : ∀ q ∈ optPinRules, q.1.eval asg = q.2 := by
  intro q hq
  obtain ⟨con, hcon, hpin⟩ := List.mem_filterMap.mp hq
  exact pinRuleOf_eval (by rw [hpin]) (halg con hcon)

/-- **The bridge half of the layout, by static analysis.** No case analysis over the circuit is
    written by hand: `bridgeCheck` normalizes the two bus-`0` payloads, sees the receive first and
    the send last with nothing between them, reads `d = 11` off the timestamps, and separates the
    two endpoints at payload position `1` — they carry the same coefficient on
    `from_state__timestamp_0` and differ by the constant `11`.

    The three expressions name the endpoints, and the checker verifies them against the traffic, so
    `bridgeCheck_sound` hands back facts about exactly these messages. -/
theorem optBaseLin : Expression.toLin layoutVars optPinRules baseE = some baseF := by decide

theorem optBridgeCheck :
    bridgeCheck layoutVars optPinRules 0 opt 11 1
        (.const 2105000)
        baseE
        (.add (.const 2105016) (.mul (.const 2013265920)
          (.mul (.const 192) (.var ⟨"cmp_result_3", some 126⟩))))
      = true := by decide

theorem optByteCheck :
    byteCheckAll layoutVars optPinRules opt.busInteractions witnesses = true := by decide

/-- **A real optimized APC has a step layout.** One arc — `(2105000, t) → (2105016 - 192·cmp,
    t + 11)` — and the twelve stateful interactions placed at `offsets`, read off the five
    surviving lt gadgets (`lt_gadget_offset`). Its five memory sends are byte-valued: four echo a
    receive earlier in the same step, and the fifth is the masked value the bitwise table checks
    (`isByte_of_xorThree`).

    This is finding G's memory half, closed. The clause the old `Circuit.advancesClock` failed on
    every APC — memory strictly inside `(base, base + d)` — is gone; what replaces it, an integer
    offset in `[-2 ^ 29, 11]` with the sends ordered, this circuit satisfies. -/
theorem opt_hasStepLayout {maxWindow : ℕ} (hw : 11 < maxWindow) :
    opt.hasStepLayout apcRules maxWindow openVmTimestampBound := by
  haveI : Fact (1 < babyBear) := ⟨by decide⟩
  intro asg halg hacc
  obtain ⟨n0, hn0, ht0⟩ : ∃ n : ℕ, n < 2 ^ 29 ∧
      asg ⟨"reads_aux__0__base__prev_timestamp_0", some 6⟩
        = asg ⟨"from_state__timestamp_0", some 1⟩ + ((((-1) - (n : ℤ)) : ℤ) : ZMod babyBear) := by
    obtain ⟨hb, ht⟩ := lookback_of_gadget (vs := layoutVars) (rules := optPinRules)
      (baseE := baseE) (baseF := baseF) (k := (-1))
      (tsE := .var ⟨"reads_aux__0__base__prev_timestamp_0", some 6⟩)
      (loE := payloadOf opt 13 0) (hiE := payloadOf opt 14 0)
      (optPinRules_hold asg halg) optBaseLin (by decide)
      (acceptsAt hacc 13 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
      (acceptsAt hacc 14 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
    rw [Recipe.place_eq] at ht
    exact ⟨_, hb, ht⟩
  obtain ⟨nw0, hnw0, htw0⟩ : ∃ n : ℕ, n < 2 ^ 29 ∧
      asg ⟨"writes_aux__base__prev_timestamp_0", some 12⟩
        = asg ⟨"from_state__timestamp_0", some 1⟩ + (((1 - (n : ℤ)) : ℤ) : ZMod babyBear) := by
    obtain ⟨hb, ht⟩ := lookback_of_gadget (vs := layoutVars) (rules := optPinRules)
      (baseE := baseE) (baseF := baseF) (k := 1)
      (tsE := .var ⟨"writes_aux__base__prev_timestamp_0", some 12⟩)
      (loE := payloadOf opt 15 0) (hiE := payloadOf opt 16 0)
      (optPinRules_hold asg halg) optBaseLin (by decide)
      (acceptsAt hacc 15 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
      (acceptsAt hacc 16 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
    rw [Recipe.place_eq] at ht
    exact ⟨_, hb, ht⟩
  obtain ⟨nr1, hnr1, htr1⟩ : ∃ n : ℕ, n < 2 ^ 29 ∧
      asg ⟨"reads_aux__0__base__prev_timestamp_1", some 42⟩
        = asg ⟨"from_state__timestamp_0", some 1⟩ + (((2 - (n : ℤ)) : ℤ) : ZMod babyBear) := by
    obtain ⟨hb, ht⟩ := lookback_of_gadget (vs := layoutVars) (rules := optPinRules)
      (baseE := baseE) (baseF := baseF) (k := 2)
      (tsE := .var ⟨"reads_aux__0__base__prev_timestamp_1", some 42⟩)
      (loE := payloadOf opt 17 0) (hiE := payloadOf opt 18 0)
      (optPinRules_hold asg halg) optBaseLin (by decide)
      (acceptsAt hacc 17 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
      (acceptsAt hacc 18 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
    rw [Recipe.place_eq] at ht
    exact ⟨_, hb, ht⟩
  obtain ⟨nw1, hnw1, htw1⟩ : ∃ n : ℕ, n < 2 ^ 29 ∧
      asg ⟨"writes_aux__base__prev_timestamp_1", some 48⟩
        = asg ⟨"from_state__timestamp_0", some 1⟩ + (((4 - (n : ℤ)) : ℤ) : ZMod babyBear) := by
    obtain ⟨hb, ht⟩ := lookback_of_gadget (vs := layoutVars) (rules := optPinRules)
      (baseE := baseE) (baseF := baseF) (k := 4)
      (tsE := .var ⟨"writes_aux__base__prev_timestamp_1", some 48⟩)
      (loE := payloadOf opt 19 0) (hiE := payloadOf opt 20 0)
      (optPinRules_hold asg halg) optBaseLin (by decide)
      (acceptsAt hacc 19 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
      (acceptsAt hacc 20 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
    rw [Recipe.place_eq] at ht
    exact ⟨_, hb, ht⟩
  obtain ⟨nr3, hnr3, htr3⟩ : ∃ n : ℕ, n < 2 ^ 29 ∧
      asg ⟨"reads_aux__1__base__prev_timestamp_3", some 115⟩
        = asg ⟨"from_state__timestamp_0", some 1⟩ + (((9 - (n : ℤ)) : ℤ) : ZMod babyBear) := by
    obtain ⟨hb, ht⟩ := lookback_of_gadget (vs := layoutVars) (rules := optPinRules)
      (baseE := baseE) (baseF := baseF) (k := 9)
      (tsE := .var ⟨"reads_aux__1__base__prev_timestamp_3", some 115⟩)
      (loE := payloadOf opt 21 0) (hiE := payloadOf opt 22 0)
      (optPinRules_hold asg halg) optBaseLin (by decide)
      (acceptsAt hacc 21 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
      (acceptsAt hacc 22 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
    rw [Recipe.place_eq] at ht
    exact ⟨_, hb, ht⟩
  have hbit : accepts (p := babyBear) defaultBusMap
      { busId := 6, multiplicity := 1,
        payload := [asg ⟨"a__0_0", some 19⟩, 3,
          asg ⟨"a__0_0", some 19⟩ + 3 + 2013265920 * (2 * asg ⟨"a__0_2", some 91⟩), 1] } :=
    acceptsAt hacc 7 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide)
  replace hbit : isByte (asg ⟨"a__0_0", some 19⟩) ∧ isByte (3 : ZMod babyBear) ∧
      (asg ⟨"a__0_0", some 19⟩ + 3 + 2013265920 * (2 * asg ⟨"a__0_2", some 91⟩)).val
        = Nat.xor (asg ⟨"a__0_0", some 19⟩).val (3 : ZMod babyBear).val := hbit
  have ha02 : isByte (asg ⟨"a__0_2", some 91⟩) :=
    isByte_of_xorThree hbit.1
      (by rw [hbit.2.2, show (3 : ZMod babyBear).val = 3 from by decide])
      (by linear_combination (2 * asg ⟨"a__0_2", some 91⟩) * babyBear_negOne)
  have hub : ∀ i : Fin opt.busInteractions.length,
      apcRules.isStateful (opt.busInteractions.get i).busId = true →
      ((opt.busInteractions.get i).eval asg).multiplicity ≠ 0 →
      (offsets n0 nw0 nr1 nw1 nr3).getD i.val 0 ≤ offsetUb.getD i.val 0 := by
    intro i hst _
    fin_cases i <;>
      simp [offsets, offsetUb, opt, apcRules, openVmGuestRules, openVmIsStateful,
        defaultBusMap, OpenVmBusType.isStateful] at hst ⊢
  have hsendIdx : ∀ i : Fin opt.busInteractions.length,
      apcRules.isStateful (opt.busInteractions.get i).busId = true →
      ((opt.busInteractions.get i).eval asg).multiplicity = 1 →
      i.val ∈ [1, 6, 8, 9, 11, 12] ∧
      (offsets n0 nw0 nr1 nw1 nr3).getD i.val 0 = offsetUb.getD i.val 0 := by
    intro i hst hm
    fin_cases i <;>
      simp_all [offsets, offsetUb, opt, apcRules, openVmGuestRules,
        openVmIsStateful, defaultBusMap, OpenVmBusType.isStateful, BusInteraction.eval,
        Expression.eval, babyBear_negOne_ne_one]
  -- The bridge, by static analysis: `optBridgeCheck` is a `decide`.
  obtain ⟨hrecv, hsend, hother⟩ := bridgeCheck_sound optBridgeCheck (optPinRules_hold asg halg)
  refine ⟨_, _, _, 11, by norm_num, hw, hrecv, hsend, hother,
    fun i => (offsets n0 nw0 nr1 nw1 nr3).getD i.val 0, ?_, ?_⟩
  · -- The placement, offset by offset.
    rintro i ⟨hst, hm⟩
    fin_cases i
    · exact ⟨by simp [offsets, openVmTimestampBound, openVmTimestampBits]; omega,
        by simp [offsets]; omega,
        by simpa [offsets, baseE, opt, BusInteraction.eval, Expression.eval, apcRules,
          openVmGuestRules, openVmTimestamp, Circuit.msgAt] using ht0⟩
    · exact ⟨by simp [offsets, openVmTimestampBound, openVmTimestampBits],
        by simp [offsets],
        by simp [offsets, baseE, opt, BusInteraction.eval, Expression.eval, apcRules,
          openVmGuestRules, openVmTimestamp, Circuit.msgAt]⟩
    · exact ⟨by simp [offsets, openVmTimestampBound, openVmTimestampBits]; omega,
        by simp [offsets]; omega,
        by simpa [offsets, baseE, opt, BusInteraction.eval, Expression.eval, apcRules,
          openVmGuestRules, openVmTimestamp, Circuit.msgAt] using htw0⟩
    · exact ⟨by simp [offsets, openVmTimestampBound, openVmTimestampBits],
        by simp [offsets],
        by simp [offsets, baseE, opt, BusInteraction.eval, Expression.eval, apcRules,
          openVmGuestRules, openVmTimestamp, Circuit.msgAt, openVmMemBusId,
          openVmExecBusId]⟩
    · exact ⟨by simp [offsets, openVmTimestampBound, openVmTimestampBits]; omega,
        by simp [offsets]; omega,
        by simpa [offsets, baseE, opt, BusInteraction.eval, Expression.eval, apcRules,
          openVmGuestRules, openVmTimestamp, Circuit.msgAt] using htr1⟩
    · exact ⟨by simp [offsets, openVmTimestampBound, openVmTimestampBits]; omega,
        by simp [offsets]; omega,
        by simpa [offsets, baseE, opt, BusInteraction.eval, Expression.eval, apcRules,
          openVmGuestRules, openVmTimestamp, Circuit.msgAt] using htw1⟩
    · exact ⟨by simp [offsets, openVmTimestampBound, openVmTimestampBits],
        by simp [offsets],
        by simp [offsets, baseE, opt, BusInteraction.eval, Expression.eval, apcRules,
          openVmGuestRules, openVmTimestamp, Circuit.msgAt]⟩
    · simp [opt, apcRules, openVmGuestRules, openVmIsStateful, defaultBusMap,
        OpenVmBusType.isStateful] at hst
    · exact ⟨by simp [offsets, openVmTimestampBound, openVmTimestampBits],
        by simp [offsets],
        by simp [offsets, baseE, opt, BusInteraction.eval, Expression.eval, apcRules,
          openVmGuestRules, openVmTimestamp, Circuit.msgAt]⟩
    · exact ⟨by simp [offsets, openVmTimestampBound, openVmTimestampBits],
        by simp [offsets],
        by simp [offsets, baseE, opt, BusInteraction.eval, Expression.eval, apcRules,
          openVmGuestRules, openVmTimestamp, Circuit.msgAt]⟩
    · exact ⟨by simp [offsets, openVmTimestampBound, openVmTimestampBits]; omega,
        by simp [offsets]; omega,
        by simpa [offsets, baseE, opt, BusInteraction.eval, Expression.eval, apcRules,
          openVmGuestRules, openVmTimestamp, Circuit.msgAt] using htr3⟩
    · exact ⟨by simp [offsets, openVmTimestampBound, openVmTimestampBits],
        by simp [offsets],
        by simp [offsets, baseE, opt, BusInteraction.eval, Expression.eval, apcRules,
          openVmGuestRules, openVmTimestamp, Circuit.msgAt]⟩
    · exact ⟨by simp [offsets, openVmTimestampBound, openVmTimestampBits],
        by simp [offsets],
        by simp [offsets, baseE, opt, BusInteraction.eval, Expression.eval, apcRules,
          openVmGuestRules, openVmTimestamp, Circuit.msgAt, openVmMemBusId,
          openVmExecBusId]⟩
    all_goals
      simp [opt, apcRules, openVmGuestRules, openVmIsStateful, defaultBusMap,
        OpenVmBusType.isStateful] at hst
  · -- The byte invariant, by static analysis: only the masked write is left by hand. What used to
    -- be `memOrdered` (`offsetUb_dominates`) is inlined here, converting the caller's
    -- `place`-ordered hypothesis into the index order `byteCheck_sendsOk` expects.
    intro i hsend hlow
    have hordered : ∀ j : Fin opt.busInteractions.length, j < i →
        opt.activeMem apcRules asg j →
        apcRules.payloadOk (opt.msgAt asg j) := by
      intro j hji hactj
      obtain ⟨hmem, heq⟩ := hsendIdx i hsend.1.1 hsend.1.2
      refine hlow j ?_ hactj
      show (offsets n0 nw0 nr1 nw1 nr3).getD j.val 0
        < (offsets n0 nw0 nr1 nw1 nr3).getD i.val 0
      rw [heq]
      exact lt_of_le_of_lt (hub j hactj.1.1 hactj.1.2)
        (offsetUb_dominates i.val hmem j.val (Fin.lt_def.mp hji))
    refine memSendsOk_of_sendsOk (byteCheck_sendsOk (optPinRules_hold asg halg) optByteCheck ?_)
      i hsend hordered
    intro i hi hsend hlow
    fin_cases i
    all_goals try exact absurd hi (by decide)
    show openVmPayloadOk defaultBusMap ((1 : ℕ), [(1 : ZMod babyBear), 44,
      asg ⟨"a__0_2", some 91⟩, 0, 0, 0, asg ⟨"from_state__timestamp_0", some 1⟩ + 9])
    exact (openVmPayloadOk_mem_iff _ _ _ _ _ _).mpr ⟨ha02, isByte_zero, isByte_zero, isByte_zero⟩

theorem opt_legalGuest {maxWindow maxInteractions : ℕ} (hw : 11 < maxWindow)
    (hi : 23 ≤ maxInteractions) :
    opt.legalGuest apcRules maxWindow openVmTimestampBound maxInteractions where
  sendOnly := opt_legalMultiplicities.1
  polarity := opt_legalMultiplicities.2
  stepLayout := opt_hasStepLayout hw
  size := by simpa [opt] using hi

end ApcOptimizer.OpenVM.Keccak2105000
