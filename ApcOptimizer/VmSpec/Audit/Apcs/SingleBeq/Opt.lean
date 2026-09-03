import ApcOptimizer.VmSpec.Audit.Apcs.SingleBeq.Layout

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

/-! **The last `trivial_simp` stage: `Circuit.legalGuest` in full.** Every multiplicity is a field
    literal, so the constant-folding tier of `Audit/SendOnlyPolarity.lean` settles both
    multiplicity clauses, and the layout is read off the two surviving lt gadgets. -/

namespace ApcOptimizer.OpenVM.SingleBeq

/-- **The static check passes.** Every multiplicity this stage carries is a field literal, so
    `Expression.foldConst` resolves all 10 of them and `decide` closes the check in the kernel. -/
theorem opt_checkMultiplicities :
    checkMultiplicities apcRules.isStateful opt = true := by decide

theorem opt_legalMultiplicities :
    opt.statelessSendOnly apcRules ∧ opt.statefulPolarity apcRules :=
  checkMultiplicities_sound opt_checkMultiplicities rfl

/-- **The optimized APC has no padding row**: its multiplicities are literals, and one of them is
    nonzero under every assignment. -/
theorem opt_no_padding_row (asg : ChipAssignment babyBear) :
    ¬ ∀ bi ∈ opt.busInteractions, (bi.eval asg).multiplicity = 0 := by
  intro h
  have hne := h (opt.busInteractions.get ⟨1, by decide⟩) (List.get_mem _ _)
  simp only [opt, BusInteraction.eval, Expression.eval, List.get] at hne
  exact absurd hne (by decide)

/-- The pin rules this stage's own constraints supply. -/
def optPinRules : List (PinRule babyBear) :=
  opt.algebraicConstraints.filterMap pinRuleOf

theorem optPinRules_hold (asg : ChipAssignment babyBear)
    (halg : opt.satisfiesAlgebraic asg) : ∀ q ∈ optPinRules, q.1.eval asg = q.2 := by
  intro q hq
  obtain ⟨con, hcon, hpin⟩ := List.mem_filterMap.mp hq
  exact pinRuleOf_eval (by rw [hpin]) (halg con hcon)

/-- **The bridge half of the layout, by static analysis.** The outgoing `pc` is not a literal here
    but `4 - 2 * cmp_result_0`: `bridgeCheck` normalizes it like any other payload and separates
    the two endpoints at position `1`, where they differ by the constant `d = 2`. -/
theorem optBaseLin : Expression.toLin layoutVars optPinRules baseE = some baseF := by decide

theorem optBridgeCheck :
    bridgeCheck layoutVars optPinRules 0 opt 2 1 (.const 0) baseE
        (.add (.const 4) (.mul (.const 2013265920)
          (.mul (.const 2) (.var ⟨"cmp_result_0", some 18⟩))))
      = true := by decide

theorem optByteCheck :
    byteCheckAll layoutVars optPinRules opt.busInteractions witnesses = true := by decide

/-- **A real optimized branch APC has a step layout.** One arc — `(0, t) → (4 - 2·cmp, t + 2)` —
    and the six stateful interactions placed at `offsets`, read off the two surviving lt gadgets
    (`lt_gadget_offset`). Both memory sends echo the read that preceded them, so the byte
    invariant is entirely decidable: a branch computes nothing it sends. -/
theorem opt_hasStepLayout {maxWindow : ℕ} (hw : 2 < maxWindow) :
    opt.hasStepLayout apcRules maxWindow openVmTimestampBound := by
  haveI : Fact (1 < babyBear) := ⟨by decide⟩
  intro asg halg hacc
  obtain ⟨nr0, hnr0, htr0⟩ : ∃ n : ℕ, n < 2 ^ 29 ∧
      asg ⟨"reads_aux__0__base__prev_timestamp_0", some 4⟩
        = asg ⟨"from_state__timestamp_0", some 1⟩ + ((((-1) - (n : ℤ)) : ℤ) : ZMod babyBear) := by
    obtain ⟨hb, ht⟩ := lookback_of_gadget (vs := layoutVars) (rules := optPinRules)
      (baseE := baseE) (baseF := baseF) (k := (-1))
      (tsE := .var ⟨"reads_aux__0__base__prev_timestamp_0", some 4⟩)
      (loE := payloadOf opt 6 0) (hiE := payloadOf opt 7 0)
      (optPinRules_hold asg halg) optBaseLin (by decide)
      (acceptsAt hacc 6 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
      (acceptsAt hacc 7 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
    rw [Recipe.place_eq] at ht
    exact ⟨_, hb, ht⟩
  obtain ⟨nr1, hnr1, htr1⟩ : ∃ n : ℕ, n < 2 ^ 29 ∧
      asg ⟨"reads_aux__1__base__prev_timestamp_0", some 7⟩
        = asg ⟨"from_state__timestamp_0", some 1⟩ + (((0 - (n : ℤ)) : ℤ) : ZMod babyBear) := by
    obtain ⟨hb, ht⟩ := lookback_of_gadget (vs := layoutVars) (rules := optPinRules)
      (baseE := baseE) (baseF := baseF) (k := 0)
      (tsE := .var ⟨"reads_aux__1__base__prev_timestamp_0", some 7⟩)
      (loE := payloadOf opt 8 0) (hiE := payloadOf opt 9 0)
      (optPinRules_hold asg halg) optBaseLin (by decide)
      (acceptsAt hacc 8 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
      (acceptsAt hacc 9 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
    rw [Recipe.place_eq] at ht
    exact ⟨_, hb, ht⟩
  -- `memOrdered` reads only the memory bus, so both tables are consulted only there: the bridge
  -- send sits at index `5`, after every memory send, and is never a `b` in `offsetUb_dominates`.
  have hub : ∀ i : Fin opt.busInteractions.length, opt.activeMem apcRules asg i →
      (offsets nr0 nr1).getD i.val 0 ≤ offsetUb.getD i.val 0 := by
    intro i hi
    obtain ⟨⟨hst, -⟩, hmem⟩ := hi
    fin_cases i <;>
      simp [offsets, offsetUb, opt, apcRules, openVmGuestRules, openVmIsStateful,
        defaultBusMap, OpenVmBusType.isStateful, openVmMemBusId] at hst hmem ⊢
  have hsendIdx : ∀ i : Fin opt.busInteractions.length, opt.memSend apcRules asg i →
      i.val ∈ [1, 3] ∧ (offsets nr0 nr1).getD i.val 0 = offsetUb.getD i.val 0 := by
    intro i hi
    obtain ⟨⟨hst, hm⟩, hmem⟩ := hi
    fin_cases i <;>
      simp_all [offsets, offsetUb, opt, apcRules, openVmGuestRules, openVmIsStateful,
        defaultBusMap, OpenVmBusType.isStateful, openVmMemBusId, Circuit.multAt,
        BusInteraction.eval, Expression.eval, babyBear_negOne_ne_one]
  obtain ⟨hrecv, hsend, hother⟩ := bridgeCheck_sound optBridgeCheck (optPinRules_hold asg halg)
  refine ⟨_, _, _, 2, by norm_num, hw, hrecv, hsend, hother,
    fun i => (offsets nr0 nr1).getD i.val 0, ?_, ?_⟩
  · -- The placement, offset by offset.
    rintro i ⟨hst, hm⟩
    fin_cases i
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
    · exact ⟨by simp [offsets, openVmTimestampBound, openVmTimestampBits],
        by simp [offsets],
        by simp [offsets, baseE, opt, BusInteraction.eval, Expression.eval, apcRules,
          openVmGuestRules, openVmTimestamp, Circuit.msgAt, openVmMemBusId, openVmExecBusId]⟩
    · exact ⟨by simp [offsets, openVmTimestampBound, openVmTimestampBits],
        by simp [offsets],
        by simp [offsets, baseE, opt, BusInteraction.eval, Expression.eval, apcRules,
          openVmGuestRules, openVmTimestamp, Circuit.msgAt, openVmMemBusId, openVmExecBusId]⟩
    all_goals
      simp [opt, apcRules, openVmGuestRules, openVmIsStateful, defaultBusMap,
        OpenVmBusType.isStateful] at hst
  · -- The byte invariant, entirely by static analysis: every memory send is an echo.
    intro i hsend hlow
    have hordered : ∀ j : Fin opt.busInteractions.length, j < i →
        opt.activeMem apcRules asg j →
        apcRules.payloadOk (opt.msgAt asg j) := by
      intro j hji hactj
      obtain ⟨hmem, heq⟩ := hsendIdx i hsend
      refine hlow j ?_ hactj
      show (offsets nr0 nr1).getD j.val 0 < (offsets nr0 nr1).getD i.val 0
      rw [heq]
      exact lt_of_le_of_lt (hub j hactj)
        (offsetUb_dominates i.val hmem j.val (Fin.lt_def.mp hji))
    refine memSendsOk_of_sendsOk (byteCheck_sendsOk (optPinRules_hold asg halg) optByteCheck ?_)
      i hsend hordered
    intro i hi _ _
    fin_cases i <;> exact absurd hi (by decide)

theorem opt_legalGuest {maxWindow maxInteractions : ℕ} (hw : 2 < maxWindow)
    (hi : 10 ≤ maxInteractions) :
    opt.legalGuest apcRules maxWindow openVmTimestampBound maxInteractions where
  sendOnly := opt_legalMultiplicities.1
  polarity := opt_legalMultiplicities.2
  stepLayout := opt_hasStepLayout hw
  size := by simpa [opt] using hi

end ApcOptimizer.OpenVM.SingleBeq
