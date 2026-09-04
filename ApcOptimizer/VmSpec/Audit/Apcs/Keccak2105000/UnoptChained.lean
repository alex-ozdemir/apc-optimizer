import ApcOptimizer.VmSpec.Audit.Apcs.Common
import ApcOptimizer.VmSpec.Audit.Apcs.Keccak2105000.Stages

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

/-! **Stage `000_unopt` with its four fused instructions' timestamps chained: `Circuit.legalGuest`
    in full.** The only stage whose layout is not read off the substituted lt gadget: powdr has not
    run its substitution pass yet, so each memory receive's offset comes from the raw gadget
    constraint (`gadgetLookback_raw`), and each fresh ALU write's byte-ness from a one-hot
    decomposition of that instruction's opcode selector (`isByte_of_aluLimb`). -/

namespace ApcOptimizer.OpenVM.Keccak2105000

/-- **The strengthened check still passes**: the three chaining constraints are not pin-rule
    shaped (their right side is `from_state__timestamp_i + 3`, a variable plus a constant, not a
    literal), so `pinRuleOf` extracts nothing new from them — the check runs on exactly
    `unopt`'s own 27 rules. -/
theorem unoptChained_checkMultiplicitiesWith :
    checkMultiplicitiesWith apcRules.isStateful unoptChained = true := by decide

theorem unoptChained_legalMultiplicities :
    unoptChained.statelessSendOnly apcRules ∧
      unoptChained.statefulPolarity apcRules :=
  checkMultiplicitiesWith_sound unoptChained_checkMultiplicitiesWith rfl

/-- **The three chaining hypotheses, unpacked from `satisfiesAlgebraic`.** The constraints
    themselves; `pinRuleOf`'s reach ends at literals, so this is by hand. -/
theorem chainedTimes {asg : ChipAssignment babyBear}
    (halg : unoptChained.satisfiesAlgebraic asg) :
    asg ⟨"from_state__timestamp_1", some 37⟩
        = asg ⟨"from_state__timestamp_0", some 1⟩ + 3 ∧
      asg ⟨"from_state__timestamp_2", some 73⟩
        = asg ⟨"from_state__timestamp_1", some 37⟩ + 3 ∧
      asg ⟨"from_state__timestamp_3", some 109⟩
        = asg ⟨"from_state__timestamp_2", some 73⟩ + 3 := by
  have h1 := halg
    (.add (.var ⟨"from_state__timestamp_1", some 37⟩)
      (.mul (.const 2013265920)
        (.add (.var ⟨"from_state__timestamp_0", some 1⟩) (.const 3))))
    (by simp [unoptChained])
  have h2 := halg
    (.add (.var ⟨"from_state__timestamp_2", some 73⟩)
      (.mul (.const 2013265920)
        (.add (.var ⟨"from_state__timestamp_1", some 37⟩) (.const 3))))
    (by simp [unoptChained])
  have h3 := halg
    (.add (.var ⟨"from_state__timestamp_3", some 109⟩)
      (.mul (.const 2013265920)
        (.add (.var ⟨"from_state__timestamp_2", some 73⟩) (.const 3))))
    (by simp [unoptChained])
  simp only [Expression.eval] at h1 h2 h3
  refine ⟨by linear_combination h1 - (asg ⟨"from_state__timestamp_0", some 1⟩ + 3) * babyBear_negOne,
    by linear_combination h2 - (asg ⟨"from_state__timestamp_1", some 37⟩ + 3) * babyBear_negOne,
    by linear_combination h3 - (asg ⟨"from_state__timestamp_2", some 73⟩ + 3) * babyBear_negOne⟩

/-- The variables the unoptimized (chained) APC's bridge payloads mention. -/
def unoptVars : List Variable :=
  [⟨"from_state__timestamp_0", some 1⟩, ⟨"from_state__timestamp_1", some 37⟩,
   ⟨"from_state__timestamp_2", some 73⟩, ⟨"from_state__timestamp_3", some 109⟩,
   ⟨"cmp_result_3", some 126⟩]

/-- The pin rules `unopt`'s own constraints supply -- identical to
    `unoptChained`'s, since the three chaining constraints extract none (their right
    side is not a literal). -/
def unoptPinRules : List (PinRule babyBear) :=
  unopt.algebraicConstraints.filterMap pinRuleOf

theorem unoptPinRules_hold (asg : ChipAssignment babyBear)
    (halg : unoptChained.satisfiesAlgebraic asg) :
    ∀ q ∈ unoptPinRules, q.1.eval asg = q.2 := by
  intro q hq
  obtain ⟨con, hcon, hpin⟩ := List.mem_filterMap.mp hq
  exact pinRuleOf_eval (by rw [hpin]) (halg con (List.mem_append_left _ hcon))

/-- **The bridge's linear pins**: each fused instruction's own start timestamp, in terms of
    `from_state__timestamp_0`, read off `chainedTimes` rather than a literal constraint. -/
def unoptLinRules : List (LinPinRule babyBear) :=
  [ (⟨"from_state__timestamp_1", some 37⟩, ⟨3, [1, 0, 0, 0, 0]⟩)
  , (⟨"from_state__timestamp_2", some 73⟩, ⟨6, [1, 0, 0, 0, 0]⟩)
  , (⟨"from_state__timestamp_3", some 109⟩, ⟨9, [1, 0, 0, 0, 0]⟩) ]

theorem unoptLinRules_sized : ∀ q ∈ unoptLinRules, q.2.Sized unoptVars.length := by
  intro q hq
  simp only [unoptLinRules, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl <;> (unfold LinForm.Sized unoptVars; decide)

theorem unoptLinRules_hold {asg : ChipAssignment babyBear}
    (halg : unoptChained.satisfiesAlgebraic asg) :
    ∀ q ∈ unoptLinRules, asg q.1 = q.2.eval unoptVars asg := by
  obtain ⟨ht01, ht12, ht23⟩ := chainedTimes halg
  intro q hq
  simp only [unoptLinRules, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · simp only [LinForm.eval, unoptVars, List.zipWith_cons_cons, List.zipWith_nil_right,
      List.sum_cons, List.sum_nil]
    linear_combination ht01
  · simp only [LinForm.eval, unoptVars, List.zipWith_cons_cons, List.zipWith_nil_right,
      List.sum_cons, List.sum_nil]
    linear_combination ht12 + ht01
  · simp only [LinForm.eval, unoptVars, List.zipWith_cons_cons, List.zipWith_nil_right,
      List.sum_cons, List.sum_nil]
    linear_combination ht23 + ht12 + ht01

/-- **The bridge check, with the chain's linear pins in scope.** With `unoptLinRules` normalizing
    each fused instruction's start timestamp back to `from_state__timestamp_0`, `bridgeCheckL` sees
    the six intermediate bridge messages cancel automatically — no per-pair hand argument needed,
    unlike `unopt` (unchained) or the earlier hand proof this replaces. -/
theorem unoptBridgeCheckL :
    bridgeCheckL unoptVars unoptPinRules unoptLinRules 0 unoptChained 11 1
        (.const 2105000)
        (.var ⟨"from_state__timestamp_0", some 1⟩)
        (.add (.const 2105016) (.mul (.const 2013265920)
          (.mul (.const 192) (.var ⟨"cmp_result_3", some 126⟩))))
      = true := by decide

/-- **The bridge, closing finding G2.** `bridgeCheckL_sound` from `unoptBridgeCheckL`, a `decide`
    — the linear pins do the work `unoptChained_bridge`'s earlier hand proof did by
    unfolding `allEffects` and cancelling six terms in pairs. -/
theorem unoptChained_bridge {asg : ChipAssignment babyBear}
    (halg : unoptChained.satisfiesAlgebraic asg) :
    unoptChained.allEffects asg
        (0, [2105000, asg ⟨"from_state__timestamp_0", some 1⟩]) = -1 ∧
      unoptChained.allEffects asg
        (0, [2105016 + 2013265920 * (192 * asg ⟨"cmp_result_3", some 126⟩),
          asg ⟨"from_state__timestamp_0", some 1⟩ + 11]) = 1 ∧
      ∀ m : BusMessage babyBear, m.1 = 0 →
        m ≠ (0, [2105000, asg ⟨"from_state__timestamp_0", some 1⟩]) →
        m ≠ (0, [2105016 + 2013265920 * (192 * asg ⟨"cmp_result_3", some 126⟩),
          asg ⟨"from_state__timestamp_0", some 1⟩ + 11]) →
        unoptChained.allEffects asg m = 0 := by
  simpa using bridgeCheckL_sound unoptBridgeCheckL (unoptPinRules_hold asg halg)
    unoptLinRules_sized (unoptLinRules_hold halg)

/-- **The pins `unopt`'s own constraints supply, read directly rather than through
    `pinRuleOf`.** One-hot flags force `rs2_as_i = 0` on all three arithmetic slots (this basic
    block's second operand is always an immediate), the four `pc_i` and `imm_3`, and each slot's
    flag sum is `1`. -/
theorem unoptPins {asg : ChipAssignment babyBear}
    (halg : unoptChained.satisfiesAlgebraic asg) :
    (asg ⟨"opcode_add_flag_0", some 31⟩ + asg ⟨"opcode_sub_flag_0", some 32⟩
        + asg ⟨"opcode_xor_flag_0", some 33⟩ + asg ⟨"opcode_or_flag_0", some 34⟩
        + asg ⟨"opcode_and_flag_0", some 35⟩ = 1) ∧
    (asg ⟨"opcode_add_flag_1", some 67⟩ + asg ⟨"opcode_sub_flag_1", some 68⟩
        + asg ⟨"opcode_xor_flag_1", some 69⟩ + asg ⟨"opcode_or_flag_1", some 70⟩
        + asg ⟨"opcode_and_flag_1", some 71⟩ = 1) ∧
    (asg ⟨"opcode_add_flag_2", some 103⟩ + asg ⟨"opcode_sub_flag_2", some 104⟩
        + asg ⟨"opcode_xor_flag_2", some 105⟩ + asg ⟨"opcode_or_flag_2", some 106⟩
        + asg ⟨"opcode_and_flag_2", some 107⟩ = 1) ∧
    (asg ⟨"opcode_beq_flag_3", some 128⟩ + asg ⟨"opcode_bne_flag_3", some 129⟩ = 1) ∧
    asg ⟨"from_state__pc_0", some 0⟩ = 2105000 ∧
    asg ⟨"from_state__pc_1", some 36⟩ = 2105004 ∧
    asg ⟨"from_state__pc_2", some 72⟩ = 2105008 ∧
    asg ⟨"from_state__pc_3", some 108⟩ = 2105012 ∧
    asg ⟨"rs2_as_0", some 5⟩ = 0 ∧
    asg ⟨"rs2_as_1", some 41⟩ = 0 ∧
    asg ⟨"rs2_as_2", some 77⟩ = 0 := by
  have hfs0 := halg
    (.add (.mul (.const 2013265920)
        (.add (.add (.add (.add (.add (.const 0) (.var ⟨"opcode_add_flag_0", some 31⟩))
          (.var ⟨"opcode_sub_flag_0", some 32⟩)) (.var ⟨"opcode_xor_flag_0", some 33⟩))
          (.var ⟨"opcode_or_flag_0", some 34⟩)) (.var ⟨"opcode_and_flag_0", some 35⟩)))
      (.const 1)) (List.mem_append_left _ (by decide))
  have hfs1 := halg
    (.add (.mul (.const 2013265920)
        (.add (.add (.add (.add (.add (.const 0) (.var ⟨"opcode_add_flag_1", some 67⟩))
          (.var ⟨"opcode_sub_flag_1", some 68⟩)) (.var ⟨"opcode_xor_flag_1", some 69⟩))
          (.var ⟨"opcode_or_flag_1", some 70⟩)) (.var ⟨"opcode_and_flag_1", some 71⟩)))
      (.const 1)) (List.mem_append_left _ (by decide))
  have hfs2 := halg
    (.add (.mul (.const 2013265920)
        (.add (.add (.add (.add (.add (.const 0) (.var ⟨"opcode_add_flag_2", some 103⟩))
          (.var ⟨"opcode_sub_flag_2", some 104⟩)) (.var ⟨"opcode_xor_flag_2", some 105⟩))
          (.var ⟨"opcode_or_flag_2", some 106⟩)) (.var ⟨"opcode_and_flag_2", some 107⟩)))
      (.const 1)) (List.mem_append_left _ (by decide))
  have hfs3 := halg
    (.add (.mul (.const 2013265920)
        (.add (.add (.const 0) (.var ⟨"opcode_beq_flag_3", some 128⟩))
          (.var ⟨"opcode_bne_flag_3", some 129⟩))) (.const 1))
    (List.mem_append_left _ (by decide))
  have hpc0 := halg
    (.add (.var ⟨"from_state__pc_0", some 0⟩) (.mul (.const 2013265920) (.const 2105000)))
    (List.mem_append_left _ (by decide))
  have hpc1 := halg
    (.add (.var ⟨"from_state__pc_1", some 36⟩) (.mul (.const 2013265920) (.const 2105004)))
    (List.mem_append_left _ (by decide))
  have hpc2 := halg
    (.add (.var ⟨"from_state__pc_2", some 72⟩) (.mul (.const 2013265920) (.const 2105008)))
    (List.mem_append_left _ (by decide))
  have hpc3 := halg
    (.add (.var ⟨"from_state__pc_3", some 108⟩) (.mul (.const 2013265920) (.const 2105012)))
    (List.mem_append_left _ (by decide))
  have hrs0 := halg
    (.add (.var ⟨"rs2_as_0", some 5⟩) (.mul (.const 2013265920) (.const 0)))
    (List.mem_append_left _ (by decide))
  have hrs1 := halg
    (.add (.var ⟨"rs2_as_1", some 41⟩) (.mul (.const 2013265920) (.const 0)))
    (List.mem_append_left _ (by decide))
  have hrs2 := halg
    (.add (.var ⟨"rs2_as_2", some 77⟩) (.mul (.const 2013265920) (.const 0)))
    (List.mem_append_left _ (by decide))
  simp only [Expression.eval] at hfs0 hfs1 hfs2 hfs3 hpc0 hpc1 hpc2 hpc3 hrs0 hrs1 hrs2
  rw [babyBear_negOne] at hfs0 hfs1 hfs2 hfs3 hpc0 hpc1 hpc2 hpc3 hrs0 hrs1 hrs2
  refine ⟨by linear_combination -hfs0, by linear_combination -hfs1,
    by linear_combination -hfs2, by linear_combination -hfs3,
    by linear_combination hpc0, by linear_combination hpc1,
    by linear_combination hpc2, by linear_combination hpc3,
    by linear_combination hrs0, by linear_combination hrs1, by linear_combination hrs2⟩

set_option maxRecDepth 32000 in
/-- Instr `0`'s `rs1` read: send offset `0`. -/
theorem unoptLookback_r1_0 {asg : ChipAssignment babyBear}
    (halg : unoptChained.satisfiesAlgebraic asg)
    (hacc : unoptChained.satisfiesStateless apcRules asg) :
    ∃ n : ℕ, n < 2 ^ 29 ∧
      asg ⟨"reads_aux__0__base__prev_timestamp_0", some 6⟩
        = asg ⟨"from_state__timestamp_0", some 1⟩
          + ((((-1) - (n : ℤ)) : ℤ) : ZMod babyBear) := by
  have hgate := (unoptPins halg).1
  have hcon := halg
    (.mul (.add (.add (.add (.add (.add (.const 0) (.var ⟨"opcode_add_flag_0", some 31⟩))
        (.var ⟨"opcode_sub_flag_0", some 32⟩)) (.var ⟨"opcode_xor_flag_0", some 33⟩))
        (.var ⟨"opcode_or_flag_0", some 34⟩)) (.var ⟨"opcode_and_flag_0", some 35⟩))
      (.add (.add (.add (.add (.var ⟨"from_state__timestamp_0", some 1⟩) (.const 0))
        (.mul (.const 2013265920) (.var ⟨"reads_aux__0__base__prev_timestamp_0", some 6⟩)))
        (.mul (.const 2013265920) (.const 1)))
        (.mul (.const 2013265920) (.add (.add (.const 0)
          (.mul (.var ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_0", some 7⟩)
            (.const 1)))
          (.mul (.var ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__1_0", some 8⟩)
            (.const 131072))))))
    (List.mem_append_left _ (by decide))
  simp only [Expression.eval] at hcon
  rw [babyBear_negOne] at hcon
  have heq := gadgetLookback_raw (δ := 0)
    (ts := asg ⟨"from_state__timestamp_0", some 1⟩)
    (prev := asg ⟨"reads_aux__0__base__prev_timestamp_0", some 6⟩)
    (lo := asg ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_0", some 7⟩)
    (hi := asg ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__1_0", some 8⟩)
    hgate (by linear_combination hcon)
  have hlo := accepts_congr_mult3 (m2 := 1)
    (acceptsAt hacc 5 (by decide) _ rfl rfl (sum5_eq1_ne_zero hgate))
  have hhi := accepts_congr_mult3 (m2 := 1)
    (acceptsAt hacc 6 (by decide) _ rfl rfl (sum5_eq1_ne_zero hgate))
  simp only [Expression.eval] at hlo hhi
  obtain ⟨n, -, hn29, hplace⟩ := lt_gadget_offset (-1)
    (asg ⟨"reads_aux__0__base__prev_timestamp_0", some 6⟩)
    (asg ⟨"from_state__timestamp_0", some 1⟩) hlo hhi (by push_cast at heq ⊢; linear_combination heq)
  exact ⟨n, hn29, hplace⟩

set_option maxRecDepth 32000 in
/-- Instr `0`'s write: send offset `2`. -/
theorem unoptLookback_w_0 {asg : ChipAssignment babyBear}
    (halg : unoptChained.satisfiesAlgebraic asg)
    (hacc : unoptChained.satisfiesStateless apcRules asg) :
    ∃ n : ℕ, n < 2 ^ 29 ∧
      asg ⟨"writes_aux__base__prev_timestamp_0", some 12⟩
        = asg ⟨"from_state__timestamp_0", some 1⟩
          + ((((1 - (n : ℤ)) : ℤ)) : ZMod babyBear) := by
  have hgate := (unoptPins halg).1
  have hcon := halg
    (.mul (.add ((.add ((.add ((.add ((.add (.const 0) (.var ⟨"opcode_add_flag_0", some 31⟩))) (.var ⟨"opcode_sub_flag_0", some 32⟩))) (.var ⟨"opcode_xor_flag_0", some 33⟩))) (.var ⟨"opcode_or_flag_0", some 34⟩))) (.var ⟨"opcode_and_flag_0", some 35⟩))
      (.add (.add (.add (.add (.var ⟨"from_state__timestamp_0", some 1⟩) (.const 2))
        (.mul (.const 2013265920) (.var ⟨"writes_aux__base__prev_timestamp_0", some 12⟩)))
        (.mul (.const 2013265920) (.const 1)))
        (.mul (.const 2013265920) (.add (.add (.const 0)
          (.mul (.var ⟨"writes_aux__base__timestamp_lt_aux__lower_decomp__0_0", some 13⟩) (.const 1)))
          (.mul (.var ⟨"writes_aux__base__timestamp_lt_aux__lower_decomp__1_0", some 14⟩) (.const 131072))))))
    (List.mem_append_left _ (by decide))
  simp only [Expression.eval] at hcon
  rw [babyBear_negOne] at hcon
  have heq := gadgetLookback_raw (δ := 2)
    (ts := asg ⟨"from_state__timestamp_0", some 1⟩)
    (prev := asg ⟨"writes_aux__base__prev_timestamp_0", some 12⟩)
    (lo := asg ⟨"writes_aux__base__timestamp_lt_aux__lower_decomp__0_0", some 13⟩)
    (hi := asg ⟨"writes_aux__base__timestamp_lt_aux__lower_decomp__1_0", some 14⟩)
    hgate (by linear_combination hcon)
  have hlo := accepts_congr_mult3 (m2 := 1)
    (acceptsAt hacc 13 (by decide) _ rfl rfl (sum5_eq1_ne_zero hgate))
  have hhi := accepts_congr_mult3 (m2 := 1)
    (acceptsAt hacc 14 (by decide) _ rfl rfl (sum5_eq1_ne_zero hgate))
  simp only [Expression.eval] at hlo hhi
  obtain ⟨n, -, hn29, hplace⟩ := lt_gadget_offset (1)
    (asg ⟨"writes_aux__base__prev_timestamp_0", some 12⟩)
    (asg ⟨"from_state__timestamp_0", some 1⟩) hlo hhi (by push_cast at heq ⊢; linear_combination heq)
  exact ⟨n, hn29, hplace⟩

set_option maxRecDepth 32000 in
/-- Instr `1`'s `rs1` read: send offset `0`. -/
theorem unoptLookback_r1_1 {asg : ChipAssignment babyBear}
    (halg : unoptChained.satisfiesAlgebraic asg)
    (hacc : unoptChained.satisfiesStateless apcRules asg) :
    ∃ n : ℕ, n < 2 ^ 29 ∧
      asg ⟨"reads_aux__0__base__prev_timestamp_1", some 42⟩
        = asg ⟨"from_state__timestamp_1", some 37⟩
          + ((((-1 - (n : ℤ)) : ℤ)) : ZMod babyBear) := by
  have hgate := (unoptPins halg).2.1
  have hcon := halg
    (.mul (.add ((.add ((.add ((.add ((.add (.const 0) (.var ⟨"opcode_add_flag_1", some 67⟩))) (.var ⟨"opcode_sub_flag_1", some 68⟩))) (.var ⟨"opcode_xor_flag_1", some 69⟩))) (.var ⟨"opcode_or_flag_1", some 70⟩))) (.var ⟨"opcode_and_flag_1", some 71⟩))
      (.add (.add (.add (.add (.var ⟨"from_state__timestamp_1", some 37⟩) (.const 0))
        (.mul (.const 2013265920) (.var ⟨"reads_aux__0__base__prev_timestamp_1", some 42⟩)))
        (.mul (.const 2013265920) (.const 1)))
        (.mul (.const 2013265920) (.add (.add (.const 0)
          (.mul (.var ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_1", some 43⟩) (.const 1)))
          (.mul (.var ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__1_1", some 44⟩) (.const 131072))))))
    (List.mem_append_left _ (by decide))
  simp only [Expression.eval] at hcon
  rw [babyBear_negOne] at hcon
  have heq := gadgetLookback_raw (δ := 0)
    (ts := asg ⟨"from_state__timestamp_1", some 37⟩)
    (prev := asg ⟨"reads_aux__0__base__prev_timestamp_1", some 42⟩)
    (lo := asg ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_1", some 43⟩)
    (hi := asg ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__1_1", some 44⟩)
    hgate (by linear_combination hcon)
  have hlo := accepts_congr_mult3 (m2 := 1)
    (acceptsAt hacc 25 (by decide) _ rfl rfl (sum5_eq1_ne_zero hgate))
  have hhi := accepts_congr_mult3 (m2 := 1)
    (acceptsAt hacc 26 (by decide) _ rfl rfl (sum5_eq1_ne_zero hgate))
  simp only [Expression.eval] at hlo hhi
  obtain ⟨n, -, hn29, hplace⟩ := lt_gadget_offset (-1)
    (asg ⟨"reads_aux__0__base__prev_timestamp_1", some 42⟩)
    (asg ⟨"from_state__timestamp_1", some 37⟩) hlo hhi (by push_cast at heq ⊢; linear_combination heq)
  exact ⟨n, hn29, hplace⟩

set_option maxRecDepth 32000 in
/-- Instr `1`'s write: send offset `2`. -/
theorem unoptLookback_w_1 {asg : ChipAssignment babyBear}
    (halg : unoptChained.satisfiesAlgebraic asg)
    (hacc : unoptChained.satisfiesStateless apcRules asg) :
    ∃ n : ℕ, n < 2 ^ 29 ∧
      asg ⟨"writes_aux__base__prev_timestamp_1", some 48⟩
        = asg ⟨"from_state__timestamp_1", some 37⟩
          + ((((1 - (n : ℤ)) : ℤ)) : ZMod babyBear) := by
  have hgate := (unoptPins halg).2.1
  have hcon := halg
    (.mul (.add ((.add ((.add ((.add ((.add (.const 0) (.var ⟨"opcode_add_flag_1", some 67⟩))) (.var ⟨"opcode_sub_flag_1", some 68⟩))) (.var ⟨"opcode_xor_flag_1", some 69⟩))) (.var ⟨"opcode_or_flag_1", some 70⟩))) (.var ⟨"opcode_and_flag_1", some 71⟩))
      (.add (.add (.add (.add (.var ⟨"from_state__timestamp_1", some 37⟩) (.const 2))
        (.mul (.const 2013265920) (.var ⟨"writes_aux__base__prev_timestamp_1", some 48⟩)))
        (.mul (.const 2013265920) (.const 1)))
        (.mul (.const 2013265920) (.add (.add (.const 0)
          (.mul (.var ⟨"writes_aux__base__timestamp_lt_aux__lower_decomp__0_1", some 49⟩) (.const 1)))
          (.mul (.var ⟨"writes_aux__base__timestamp_lt_aux__lower_decomp__1_1", some 50⟩) (.const 131072))))))
    (List.mem_append_left _ (by decide))
  simp only [Expression.eval] at hcon
  rw [babyBear_negOne] at hcon
  have heq := gadgetLookback_raw (δ := 2)
    (ts := asg ⟨"from_state__timestamp_1", some 37⟩)
    (prev := asg ⟨"writes_aux__base__prev_timestamp_1", some 48⟩)
    (lo := asg ⟨"writes_aux__base__timestamp_lt_aux__lower_decomp__0_1", some 49⟩)
    (hi := asg ⟨"writes_aux__base__timestamp_lt_aux__lower_decomp__1_1", some 50⟩)
    hgate (by linear_combination hcon)
  have hlo := accepts_congr_mult3 (m2 := 1)
    (acceptsAt hacc 33 (by decide) _ rfl rfl (sum5_eq1_ne_zero hgate))
  have hhi := accepts_congr_mult3 (m2 := 1)
    (acceptsAt hacc 34 (by decide) _ rfl rfl (sum5_eq1_ne_zero hgate))
  simp only [Expression.eval] at hlo hhi
  obtain ⟨n, -, hn29, hplace⟩ := lt_gadget_offset (1)
    (asg ⟨"writes_aux__base__prev_timestamp_1", some 48⟩)
    (asg ⟨"from_state__timestamp_1", some 37⟩) hlo hhi (by push_cast at heq ⊢; linear_combination heq)
  exact ⟨n, hn29, hplace⟩

set_option maxRecDepth 32000 in
/-- Instr `2`'s `rs1` read: send offset `0`. -/
theorem unoptLookback_r1_2 {asg : ChipAssignment babyBear}
    (halg : unoptChained.satisfiesAlgebraic asg)
    (hacc : unoptChained.satisfiesStateless apcRules asg) :
    ∃ n : ℕ, n < 2 ^ 29 ∧
      asg ⟨"reads_aux__0__base__prev_timestamp_2", some 78⟩
        = asg ⟨"from_state__timestamp_2", some 73⟩
          + ((((-1 - (n : ℤ)) : ℤ)) : ZMod babyBear) := by
  have hgate := (unoptPins halg).2.2.1
  have hcon := halg
    (.mul (.add ((.add ((.add ((.add ((.add (.const 0) (.var ⟨"opcode_add_flag_2", some 103⟩))) (.var ⟨"opcode_sub_flag_2", some 104⟩))) (.var ⟨"opcode_xor_flag_2", some 105⟩))) (.var ⟨"opcode_or_flag_2", some 106⟩))) (.var ⟨"opcode_and_flag_2", some 107⟩))
      (.add (.add (.add (.add (.var ⟨"from_state__timestamp_2", some 73⟩) (.const 0))
        (.mul (.const 2013265920) (.var ⟨"reads_aux__0__base__prev_timestamp_2", some 78⟩)))
        (.mul (.const 2013265920) (.const 1)))
        (.mul (.const 2013265920) (.add (.add (.const 0)
          (.mul (.var ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_2", some 79⟩) (.const 1)))
          (.mul (.var ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__1_2", some 80⟩) (.const 131072))))))
    (List.mem_append_left _ (by decide))
  simp only [Expression.eval] at hcon
  rw [babyBear_negOne] at hcon
  have heq := gadgetLookback_raw (δ := 0)
    (ts := asg ⟨"from_state__timestamp_2", some 73⟩)
    (prev := asg ⟨"reads_aux__0__base__prev_timestamp_2", some 78⟩)
    (lo := asg ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_2", some 79⟩)
    (hi := asg ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__1_2", some 80⟩)
    hgate (by linear_combination hcon)
  have hlo := accepts_congr_mult3 (m2 := 1)
    (acceptsAt hacc 45 (by decide) _ rfl rfl (sum5_eq1_ne_zero hgate))
  have hhi := accepts_congr_mult3 (m2 := 1)
    (acceptsAt hacc 46 (by decide) _ rfl rfl (sum5_eq1_ne_zero hgate))
  simp only [Expression.eval] at hlo hhi
  obtain ⟨n, -, hn29, hplace⟩ := lt_gadget_offset (-1)
    (asg ⟨"reads_aux__0__base__prev_timestamp_2", some 78⟩)
    (asg ⟨"from_state__timestamp_2", some 73⟩) hlo hhi (by push_cast at heq ⊢; linear_combination heq)
  exact ⟨n, hn29, hplace⟩

set_option maxRecDepth 32000 in
/-- Instr `2`'s write: send offset `2`. -/
theorem unoptLookback_w_2 {asg : ChipAssignment babyBear}
    (halg : unoptChained.satisfiesAlgebraic asg)
    (hacc : unoptChained.satisfiesStateless apcRules asg) :
    ∃ n : ℕ, n < 2 ^ 29 ∧
      asg ⟨"writes_aux__base__prev_timestamp_2", some 84⟩
        = asg ⟨"from_state__timestamp_2", some 73⟩
          + ((((1 - (n : ℤ)) : ℤ)) : ZMod babyBear) := by
  have hgate := (unoptPins halg).2.2.1
  have hcon := halg
    (.mul (.add ((.add ((.add ((.add ((.add (.const 0) (.var ⟨"opcode_add_flag_2", some 103⟩))) (.var ⟨"opcode_sub_flag_2", some 104⟩))) (.var ⟨"opcode_xor_flag_2", some 105⟩))) (.var ⟨"opcode_or_flag_2", some 106⟩))) (.var ⟨"opcode_and_flag_2", some 107⟩))
      (.add (.add (.add (.add (.var ⟨"from_state__timestamp_2", some 73⟩) (.const 2))
        (.mul (.const 2013265920) (.var ⟨"writes_aux__base__prev_timestamp_2", some 84⟩)))
        (.mul (.const 2013265920) (.const 1)))
        (.mul (.const 2013265920) (.add (.add (.const 0)
          (.mul (.var ⟨"writes_aux__base__timestamp_lt_aux__lower_decomp__0_2", some 85⟩) (.const 1)))
          (.mul (.var ⟨"writes_aux__base__timestamp_lt_aux__lower_decomp__1_2", some 86⟩) (.const 131072))))))
    (List.mem_append_left _ (by decide))
  simp only [Expression.eval] at hcon
  rw [babyBear_negOne] at hcon
  have heq := gadgetLookback_raw (δ := 2)
    (ts := asg ⟨"from_state__timestamp_2", some 73⟩)
    (prev := asg ⟨"writes_aux__base__prev_timestamp_2", some 84⟩)
    (lo := asg ⟨"writes_aux__base__timestamp_lt_aux__lower_decomp__0_2", some 85⟩)
    (hi := asg ⟨"writes_aux__base__timestamp_lt_aux__lower_decomp__1_2", some 86⟩)
    hgate (by linear_combination hcon)
  have hlo := accepts_congr_mult3 (m2 := 1)
    (acceptsAt hacc 53 (by decide) _ rfl rfl (sum5_eq1_ne_zero hgate))
  have hhi := accepts_congr_mult3 (m2 := 1)
    (acceptsAt hacc 54 (by decide) _ rfl rfl (sum5_eq1_ne_zero hgate))
  simp only [Expression.eval] at hlo hhi
  obtain ⟨n, -, hn29, hplace⟩ := lt_gadget_offset (1)
    (asg ⟨"writes_aux__base__prev_timestamp_2", some 84⟩)
    (asg ⟨"from_state__timestamp_2", some 73⟩) hlo hhi (by push_cast at heq ⊢; linear_combination heq)
  exact ⟨n, hn29, hplace⟩

set_option maxRecDepth 32000 in
/-- Instr `3`'s `rs1` read: send offset `0`. -/
theorem unoptLookback_r1_3 {asg : ChipAssignment babyBear}
    (halg : unoptChained.satisfiesAlgebraic asg)
    (hacc : unoptChained.satisfiesStateless apcRules asg) :
    ∃ n : ℕ, n < 2 ^ 29 ∧
      asg ⟨"reads_aux__0__base__prev_timestamp_3", some 112⟩
        = asg ⟨"from_state__timestamp_3", some 109⟩
          + ((((-1 - (n : ℤ)) : ℤ)) : ZMod babyBear) := by
  have hgate := (unoptPins halg).2.2.2.1
  have hcon := halg
    (.mul (.add (.add (.const 0) (.var ⟨"opcode_beq_flag_3", some 128⟩)) (.var ⟨"opcode_bne_flag_3", some 129⟩))
      (.add (.add (.add (.add (.var ⟨"from_state__timestamp_3", some 109⟩) (.const 0))
        (.mul (.const 2013265920) (.var ⟨"reads_aux__0__base__prev_timestamp_3", some 112⟩)))
        (.mul (.const 2013265920) (.const 1)))
        (.mul (.const 2013265920) (.add (.add (.const 0)
          (.mul (.var ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_3", some 113⟩) (.const 1)))
          (.mul (.var ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__1_3", some 114⟩) (.const 131072))))))
    (List.mem_append_left _ (by decide))
  simp only [Expression.eval] at hcon
  rw [babyBear_negOne] at hcon
  have heq := gadgetLookback_raw (δ := 0)
    (ts := asg ⟨"from_state__timestamp_3", some 109⟩)
    (prev := asg ⟨"reads_aux__0__base__prev_timestamp_3", some 112⟩)
    (lo := asg ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_3", some 113⟩)
    (hi := asg ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__1_3", some 114⟩)
    hgate (by linear_combination hcon)
  have hlo := accepts_congr_mult3 (m2 := 1)
    (acceptsAt hacc 60 (by decide) _ rfl rfl (sum2_eq1_ne_zero hgate))
  have hhi := accepts_congr_mult3 (m2 := 1)
    (acceptsAt hacc 61 (by decide) _ rfl rfl (sum2_eq1_ne_zero hgate))
  simp only [Expression.eval] at hlo hhi
  obtain ⟨n, -, hn29, hplace⟩ := lt_gadget_offset (-1)
    (asg ⟨"reads_aux__0__base__prev_timestamp_3", some 112⟩)
    (asg ⟨"from_state__timestamp_3", some 109⟩) hlo hhi (by push_cast at heq ⊢; linear_combination heq)
  exact ⟨n, hn29, hplace⟩

set_option maxRecDepth 32000 in
/-- Instr `3`'s `rs2` read: send offset `1`. -/
theorem unoptLookback_r2_3 {asg : ChipAssignment babyBear}
    (halg : unoptChained.satisfiesAlgebraic asg)
    (hacc : unoptChained.satisfiesStateless apcRules asg) :
    ∃ n : ℕ, n < 2 ^ 29 ∧
      asg ⟨"reads_aux__1__base__prev_timestamp_3", some 115⟩
        = asg ⟨"from_state__timestamp_3", some 109⟩
          + ((((0 - (n : ℤ)) : ℤ)) : ZMod babyBear) := by
  have hgate := (unoptPins halg).2.2.2.1
  have hcon := halg
    (.mul (.add (.add (.const 0) (.var ⟨"opcode_beq_flag_3", some 128⟩)) (.var ⟨"opcode_bne_flag_3", some 129⟩))
      (.add (.add (.add (.add (.var ⟨"from_state__timestamp_3", some 109⟩) (.const 1))
        (.mul (.const 2013265920) (.var ⟨"reads_aux__1__base__prev_timestamp_3", some 115⟩)))
        (.mul (.const 2013265920) (.const 1)))
        (.mul (.const 2013265920) (.add (.add (.const 0)
          (.mul (.var ⟨"reads_aux__1__base__timestamp_lt_aux__lower_decomp__0_3", some 116⟩) (.const 1)))
          (.mul (.var ⟨"reads_aux__1__base__timestamp_lt_aux__lower_decomp__1_3", some 117⟩) (.const 131072))))))
    (List.mem_append_left _ (by decide))
  simp only [Expression.eval] at hcon
  rw [babyBear_negOne] at hcon
  have heq := gadgetLookback_raw (δ := 1)
    (ts := asg ⟨"from_state__timestamp_3", some 109⟩)
    (prev := asg ⟨"reads_aux__1__base__prev_timestamp_3", some 115⟩)
    (lo := asg ⟨"reads_aux__1__base__timestamp_lt_aux__lower_decomp__0_3", some 116⟩)
    (hi := asg ⟨"reads_aux__1__base__timestamp_lt_aux__lower_decomp__1_3", some 117⟩)
    hgate (by linear_combination hcon)
  have hlo := accepts_congr_mult3 (m2 := 1)
    (acceptsAt hacc 64 (by decide) _ rfl rfl (sum2_eq1_ne_zero hgate))
  have hhi := accepts_congr_mult3 (m2 := 1)
    (acceptsAt hacc 65 (by decide) _ rfl rfl (sum2_eq1_ne_zero hgate))
  simp only [Expression.eval] at hlo hhi
  obtain ⟨n, -, hn29, hplace⟩ := lt_gadget_offset (0)
    (asg ⟨"reads_aux__1__base__prev_timestamp_3", some 115⟩)
    (asg ⟨"from_state__timestamp_3", some 109⟩) hlo hhi (by push_cast at heq ⊢; linear_combination heq)
  exact ⟨n, hn29, hplace⟩

/-- Instr `0`'s opcode selector is one-hot, from its booleanity constraints and `unoptPins`'s
    flag-sum pin. -/
theorem unoptAluCase0 {asg : ChipAssignment babyBear}
    (halg : unoptChained.satisfiesAlgebraic asg) :
    (asg ⟨"opcode_add_flag_0", some 31⟩ = 1 ∧ asg ⟨"opcode_sub_flag_0", some 32⟩ = 0 ∧
        asg ⟨"opcode_xor_flag_0", some 33⟩ = 0 ∧ asg ⟨"opcode_or_flag_0", some 34⟩ = 0 ∧
        asg ⟨"opcode_and_flag_0", some 35⟩ = 0) ∨
    (asg ⟨"opcode_add_flag_0", some 31⟩ = 0 ∧ asg ⟨"opcode_sub_flag_0", some 32⟩ = 1 ∧
        asg ⟨"opcode_xor_flag_0", some 33⟩ = 0 ∧ asg ⟨"opcode_or_flag_0", some 34⟩ = 0 ∧
        asg ⟨"opcode_and_flag_0", some 35⟩ = 0) ∨
    (asg ⟨"opcode_add_flag_0", some 31⟩ = 0 ∧ asg ⟨"opcode_sub_flag_0", some 32⟩ = 0 ∧
        asg ⟨"opcode_xor_flag_0", some 33⟩ = 1 ∧ asg ⟨"opcode_or_flag_0", some 34⟩ = 0 ∧
        asg ⟨"opcode_and_flag_0", some 35⟩ = 0) ∨
    (asg ⟨"opcode_add_flag_0", some 31⟩ = 0 ∧ asg ⟨"opcode_sub_flag_0", some 32⟩ = 0 ∧
        asg ⟨"opcode_xor_flag_0", some 33⟩ = 0 ∧ asg ⟨"opcode_or_flag_0", some 34⟩ = 1 ∧
        asg ⟨"opcode_and_flag_0", some 35⟩ = 0) ∨
    (asg ⟨"opcode_add_flag_0", some 31⟩ = 0 ∧ asg ⟨"opcode_sub_flag_0", some 32⟩ = 0 ∧
        asg ⟨"opcode_xor_flag_0", some 33⟩ = 0 ∧ asg ⟨"opcode_or_flag_0", some 34⟩ = 0 ∧
        asg ⟨"opcode_and_flag_0", some 35⟩ = 1) := by
  have hb_add := halg
    (.mul (.var ⟨"opcode_add_flag_0", some 31⟩)
      (.add (.var ⟨"opcode_add_flag_0", some 31⟩) (.mul (.const 2013265920) (.const 1))))
    (List.mem_append_left _ (by decide))
  have hb_sub := halg
    (.mul (.var ⟨"opcode_sub_flag_0", some 32⟩)
      (.add (.var ⟨"opcode_sub_flag_0", some 32⟩) (.mul (.const 2013265920) (.const 1))))
    (List.mem_append_left _ (by decide))
  have hb_xor := halg
    (.mul (.var ⟨"opcode_xor_flag_0", some 33⟩)
      (.add (.var ⟨"opcode_xor_flag_0", some 33⟩) (.mul (.const 2013265920) (.const 1))))
    (List.mem_append_left _ (by decide))
  have hb_or := halg
    (.mul (.var ⟨"opcode_or_flag_0", some 34⟩)
      (.add (.var ⟨"opcode_or_flag_0", some 34⟩) (.mul (.const 2013265920) (.const 1))))
    (List.mem_append_left _ (by decide))
  have hb_and := halg
    (.mul (.var ⟨"opcode_and_flag_0", some 35⟩)
      (.add (.var ⟨"opcode_and_flag_0", some 35⟩) (.mul (.const 2013265920) (.const 1))))
    (List.mem_append_left _ (by decide))
  simp only [Expression.eval] at hb_add hb_sub hb_xor hb_or hb_and
  exact aluOneHot (unoptPins halg).1 hb_add hb_sub hb_xor hb_or hb_and

/-- Instr `1`'s opcode selector is one-hot. -/
theorem unoptAluCase1 {asg : ChipAssignment babyBear}
    (halg : unoptChained.satisfiesAlgebraic asg) :
    (asg ⟨"opcode_add_flag_1", some 67⟩ = 1 ∧ asg ⟨"opcode_sub_flag_1", some 68⟩ = 0 ∧
        asg ⟨"opcode_xor_flag_1", some 69⟩ = 0 ∧ asg ⟨"opcode_or_flag_1", some 70⟩ = 0 ∧
        asg ⟨"opcode_and_flag_1", some 71⟩ = 0) ∨
    (asg ⟨"opcode_add_flag_1", some 67⟩ = 0 ∧ asg ⟨"opcode_sub_flag_1", some 68⟩ = 1 ∧
        asg ⟨"opcode_xor_flag_1", some 69⟩ = 0 ∧ asg ⟨"opcode_or_flag_1", some 70⟩ = 0 ∧
        asg ⟨"opcode_and_flag_1", some 71⟩ = 0) ∨
    (asg ⟨"opcode_add_flag_1", some 67⟩ = 0 ∧ asg ⟨"opcode_sub_flag_1", some 68⟩ = 0 ∧
        asg ⟨"opcode_xor_flag_1", some 69⟩ = 1 ∧ asg ⟨"opcode_or_flag_1", some 70⟩ = 0 ∧
        asg ⟨"opcode_and_flag_1", some 71⟩ = 0) ∨
    (asg ⟨"opcode_add_flag_1", some 67⟩ = 0 ∧ asg ⟨"opcode_sub_flag_1", some 68⟩ = 0 ∧
        asg ⟨"opcode_xor_flag_1", some 69⟩ = 0 ∧ asg ⟨"opcode_or_flag_1", some 70⟩ = 1 ∧
        asg ⟨"opcode_and_flag_1", some 71⟩ = 0) ∨
    (asg ⟨"opcode_add_flag_1", some 67⟩ = 0 ∧ asg ⟨"opcode_sub_flag_1", some 68⟩ = 0 ∧
        asg ⟨"opcode_xor_flag_1", some 69⟩ = 0 ∧ asg ⟨"opcode_or_flag_1", some 70⟩ = 0 ∧
        asg ⟨"opcode_and_flag_1", some 71⟩ = 1) := by
  have hb_add := halg
    (.mul (.var ⟨"opcode_add_flag_1", some 67⟩)
      (.add (.var ⟨"opcode_add_flag_1", some 67⟩) (.mul (.const 2013265920) (.const 1))))
    (List.mem_append_left _ (by decide))
  have hb_sub := halg
    (.mul (.var ⟨"opcode_sub_flag_1", some 68⟩)
      (.add (.var ⟨"opcode_sub_flag_1", some 68⟩) (.mul (.const 2013265920) (.const 1))))
    (List.mem_append_left _ (by decide))
  have hb_xor := halg
    (.mul (.var ⟨"opcode_xor_flag_1", some 69⟩)
      (.add (.var ⟨"opcode_xor_flag_1", some 69⟩) (.mul (.const 2013265920) (.const 1))))
    (List.mem_append_left _ (by decide))
  have hb_or := halg
    (.mul (.var ⟨"opcode_or_flag_1", some 70⟩)
      (.add (.var ⟨"opcode_or_flag_1", some 70⟩) (.mul (.const 2013265920) (.const 1))))
    (List.mem_append_left _ (by decide))
  have hb_and := halg
    (.mul (.var ⟨"opcode_and_flag_1", some 71⟩)
      (.add (.var ⟨"opcode_and_flag_1", some 71⟩) (.mul (.const 2013265920) (.const 1))))
    (List.mem_append_left _ (by decide))
  simp only [Expression.eval] at hb_add hb_sub hb_xor hb_or hb_and
  exact aluOneHot (unoptPins halg).2.1 hb_add hb_sub hb_xor hb_or hb_and

/-- Instr `2`'s opcode selector is one-hot. -/
theorem unoptAluCase2 {asg : ChipAssignment babyBear}
    (halg : unoptChained.satisfiesAlgebraic asg) :
    (asg ⟨"opcode_add_flag_2", some 103⟩ = 1 ∧ asg ⟨"opcode_sub_flag_2", some 104⟩ = 0 ∧
        asg ⟨"opcode_xor_flag_2", some 105⟩ = 0 ∧ asg ⟨"opcode_or_flag_2", some 106⟩ = 0 ∧
        asg ⟨"opcode_and_flag_2", some 107⟩ = 0) ∨
    (asg ⟨"opcode_add_flag_2", some 103⟩ = 0 ∧ asg ⟨"opcode_sub_flag_2", some 104⟩ = 1 ∧
        asg ⟨"opcode_xor_flag_2", some 105⟩ = 0 ∧ asg ⟨"opcode_or_flag_2", some 106⟩ = 0 ∧
        asg ⟨"opcode_and_flag_2", some 107⟩ = 0) ∨
    (asg ⟨"opcode_add_flag_2", some 103⟩ = 0 ∧ asg ⟨"opcode_sub_flag_2", some 104⟩ = 0 ∧
        asg ⟨"opcode_xor_flag_2", some 105⟩ = 1 ∧ asg ⟨"opcode_or_flag_2", some 106⟩ = 0 ∧
        asg ⟨"opcode_and_flag_2", some 107⟩ = 0) ∨
    (asg ⟨"opcode_add_flag_2", some 103⟩ = 0 ∧ asg ⟨"opcode_sub_flag_2", some 104⟩ = 0 ∧
        asg ⟨"opcode_xor_flag_2", some 105⟩ = 0 ∧ asg ⟨"opcode_or_flag_2", some 106⟩ = 1 ∧
        asg ⟨"opcode_and_flag_2", some 107⟩ = 0) ∨
    (asg ⟨"opcode_add_flag_2", some 103⟩ = 0 ∧ asg ⟨"opcode_sub_flag_2", some 104⟩ = 0 ∧
        asg ⟨"opcode_xor_flag_2", some 105⟩ = 0 ∧ asg ⟨"opcode_or_flag_2", some 106⟩ = 0 ∧
        asg ⟨"opcode_and_flag_2", some 107⟩ = 1) := by
  have hb_add := halg
    (.mul (.var ⟨"opcode_add_flag_2", some 103⟩)
      (.add (.var ⟨"opcode_add_flag_2", some 103⟩) (.mul (.const 2013265920) (.const 1))))
    (List.mem_append_left _ (by decide))
  have hb_sub := halg
    (.mul (.var ⟨"opcode_sub_flag_2", some 104⟩)
      (.add (.var ⟨"opcode_sub_flag_2", some 104⟩) (.mul (.const 2013265920) (.const 1))))
    (List.mem_append_left _ (by decide))
  have hb_xor := halg
    (.mul (.var ⟨"opcode_xor_flag_2", some 105⟩)
      (.add (.var ⟨"opcode_xor_flag_2", some 105⟩) (.mul (.const 2013265920) (.const 1))))
    (List.mem_append_left _ (by decide))
  have hb_or := halg
    (.mul (.var ⟨"opcode_or_flag_2", some 106⟩)
      (.add (.var ⟨"opcode_or_flag_2", some 106⟩) (.mul (.const 2013265920) (.const 1))))
    (List.mem_append_left _ (by decide))
  have hb_and := halg
    (.mul (.var ⟨"opcode_and_flag_2", some 107⟩)
      (.add (.var ⟨"opcode_and_flag_2", some 107⟩) (.mul (.const 2013265920) (.const 1))))
    (List.mem_append_left _ (by decide))
  simp only [Expression.eval] at hb_add hb_sub hb_xor hb_or hb_and
  exact aluOneHot (unoptPins halg).2.2.1 hb_add hb_sub hb_xor hb_or hb_and

set_option maxRecDepth 32000 in
/-- **Instr `0`'s write is byte-valued**, whichever ALU op fired: each limb's own `bitwiseLookup`
    row (positions `0`–`3`) plus `unoptAluCase0`'s one-hot split feeds `isByte_of_aluLimb`. -/
theorem unoptWriteIsByte_0 {asg : ChipAssignment babyBear}
    (halg : unoptChained.satisfiesAlgebraic asg)
    (hacc : unoptChained.satisfiesStateless apcRules asg) :
    isByte (asg ⟨"a__0_0", some 19⟩) ∧ isByte (asg ⟨"a__1_0", some 20⟩) ∧
      isByte (asg ⟨"a__2_0", some 21⟩) ∧ isByte (asg ⟨"a__3_0", some 22⟩) := by
  have hgate := (unoptPins halg).1
  have hcase := unoptAluCase0 halg
  have h0 := accepts_congr_mult6 (m2 := 1)
    (acceptsAt hacc 0 (by decide) _ rfl rfl (sum5_eq1_ne_zero hgate))
  have h1 := accepts_congr_mult6 (m2 := 1)
    (acceptsAt hacc 1 (by decide) _ rfl rfl (sum5_eq1_ne_zero hgate))
  have h2 := accepts_congr_mult6 (m2 := 1)
    (acceptsAt hacc 2 (by decide) _ rfl rfl (sum5_eq1_ne_zero hgate))
  have h3 := accepts_congr_mult6 (m2 := 1)
    (acceptsAt hacc 3 (by decide) _ rfl rfl (sum5_eq1_ne_zero hgate))
  simp only [Expression.eval] at h0 h1 h2 h3
  obtain ⟨hbx0, hby0, hxy0⟩ := bitwiseTable_extract h0
  obtain ⟨hbx1, hby1, hxy1⟩ := bitwiseTable_extract h1
  obtain ⟨hbx2, hby2, hxy2⟩ := bitwiseTable_extract h2
  obtain ⟨hbx3, hby3, hxy3⟩ := bitwiseTable_extract h3
  exact ⟨isByte_of_aluLimb hcase hbx0 hby0 hxy0 rfl rfl rfl,
    isByte_of_aluLimb hcase hbx1 hby1 hxy1 rfl rfl rfl,
    isByte_of_aluLimb hcase hbx2 hby2 hxy2 rfl rfl rfl,
    isByte_of_aluLimb hcase hbx3 hby3 hxy3 rfl rfl rfl⟩

set_option maxRecDepth 32000 in
/-- **Instr `1`'s write is byte-valued.** -/
theorem unoptWriteIsByte_1 {asg : ChipAssignment babyBear}
    (halg : unoptChained.satisfiesAlgebraic asg)
    (hacc : unoptChained.satisfiesStateless apcRules asg) :
    isByte (asg ⟨"a__0_1", some 55⟩) ∧ isByte (asg ⟨"a__1_1", some 56⟩) ∧
      isByte (asg ⟨"a__2_1", some 57⟩) ∧ isByte (asg ⟨"a__3_1", some 58⟩) := by
  have hgate := (unoptPins halg).2.1
  have hcase := unoptAluCase1 halg
  have h0 := accepts_congr_mult6 (m2 := 1)
    (acceptsAt hacc 20 (by decide) _ rfl rfl (sum5_eq1_ne_zero hgate))
  have h1 := accepts_congr_mult6 (m2 := 1)
    (acceptsAt hacc 21 (by decide) _ rfl rfl (sum5_eq1_ne_zero hgate))
  have h2 := accepts_congr_mult6 (m2 := 1)
    (acceptsAt hacc 22 (by decide) _ rfl rfl (sum5_eq1_ne_zero hgate))
  have h3 := accepts_congr_mult6 (m2 := 1)
    (acceptsAt hacc 23 (by decide) _ rfl rfl (sum5_eq1_ne_zero hgate))
  simp only [Expression.eval] at h0 h1 h2 h3
  obtain ⟨hbx0, hby0, hxy0⟩ := bitwiseTable_extract h0
  obtain ⟨hbx1, hby1, hxy1⟩ := bitwiseTable_extract h1
  obtain ⟨hbx2, hby2, hxy2⟩ := bitwiseTable_extract h2
  obtain ⟨hbx3, hby3, hxy3⟩ := bitwiseTable_extract h3
  exact ⟨isByte_of_aluLimb hcase hbx0 hby0 hxy0 rfl rfl rfl,
    isByte_of_aluLimb hcase hbx1 hby1 hxy1 rfl rfl rfl,
    isByte_of_aluLimb hcase hbx2 hby2 hxy2 rfl rfl rfl,
    isByte_of_aluLimb hcase hbx3 hby3 hxy3 rfl rfl rfl⟩

set_option maxRecDepth 32000 in
/-- **Instr `2`'s write is byte-valued.** -/
theorem unoptWriteIsByte_2 {asg : ChipAssignment babyBear}
    (halg : unoptChained.satisfiesAlgebraic asg)
    (hacc : unoptChained.satisfiesStateless apcRules asg) :
    isByte (asg ⟨"a__0_2", some 91⟩) ∧ isByte (asg ⟨"a__1_2", some 92⟩) ∧
      isByte (asg ⟨"a__2_2", some 93⟩) ∧ isByte (asg ⟨"a__3_2", some 94⟩) := by
  have hgate := (unoptPins halg).2.2.1
  have hcase := unoptAluCase2 halg
  have h0 := accepts_congr_mult6 (m2 := 1)
    (acceptsAt hacc 40 (by decide) _ rfl rfl (sum5_eq1_ne_zero hgate))
  have h1 := accepts_congr_mult6 (m2 := 1)
    (acceptsAt hacc 41 (by decide) _ rfl rfl (sum5_eq1_ne_zero hgate))
  have h2 := accepts_congr_mult6 (m2 := 1)
    (acceptsAt hacc 42 (by decide) _ rfl rfl (sum5_eq1_ne_zero hgate))
  have h3 := accepts_congr_mult6 (m2 := 1)
    (acceptsAt hacc 43 (by decide) _ rfl rfl (sum5_eq1_ne_zero hgate))
  simp only [Expression.eval] at h0 h1 h2 h3
  obtain ⟨hbx0, hby0, hxy0⟩ := bitwiseTable_extract h0
  obtain ⟨hbx1, hby1, hxy1⟩ := bitwiseTable_extract h1
  obtain ⟨hbx2, hby2, hxy2⟩ := bitwiseTable_extract h2
  obtain ⟨hbx3, hby3, hxy3⟩ := bitwiseTable_extract h3
  exact ⟨isByte_of_aluLimb hcase hbx0 hby0 hxy0 rfl rfl rfl,
    isByte_of_aluLimb hcase hbx1 hby1 hxy1 rfl rfl rfl,
    isByte_of_aluLimb hcase hbx2 hby2 hxy2 rfl rfl rfl,
    isByte_of_aluLimb hcase hbx3 hby3 hxy3 rfl rfl rfl⟩

/-- The variables `unoptChained`'s echoed memory sends and their preceding receives
    mention: each instruction's `rs1` pointer, the four limbs it reads back, its own base
    timestamp and lookback record, and (for the branch) the same for `rs2`. -/
def unoptByteVars : List Variable :=
  [⟨"rs1_ptr_0", some 3⟩, ⟨"b__0_0", some 23⟩, ⟨"b__1_0", some 24⟩, ⟨"b__2_0", some 25⟩,
   ⟨"b__3_0", some 26⟩, ⟨"reads_aux__0__base__prev_timestamp_0", some 6⟩,
   ⟨"from_state__timestamp_0", some 1⟩,
   ⟨"rs1_ptr_1", some 39⟩, ⟨"b__0_1", some 59⟩, ⟨"b__1_1", some 60⟩, ⟨"b__2_1", some 61⟩,
   ⟨"b__3_1", some 62⟩, ⟨"reads_aux__0__base__prev_timestamp_1", some 42⟩,
   ⟨"from_state__timestamp_1", some 37⟩,
   ⟨"rs1_ptr_2", some 75⟩, ⟨"b__0_2", some 95⟩, ⟨"b__1_2", some 96⟩, ⟨"b__2_2", some 97⟩,
   ⟨"b__3_2", some 98⟩, ⟨"reads_aux__0__base__prev_timestamp_2", some 78⟩,
   ⟨"from_state__timestamp_2", some 73⟩,
   ⟨"rs1_ptr_3", some 110⟩, ⟨"a__0_3", some 118⟩, ⟨"a__1_3", some 119⟩, ⟨"a__2_3", some 120⟩,
   ⟨"a__3_3", some 121⟩, ⟨"reads_aux__0__base__prev_timestamp_3", some 112⟩,
   ⟨"from_state__timestamp_3", some 109⟩,
   ⟨"rs2_ptr_3", some 111⟩, ⟨"b__0_3", some 122⟩, ⟨"b__1_3", some 123⟩, ⟨"b__2_3", some 124⟩,
   ⟨"b__3_3", some 125⟩, ⟨"reads_aux__1__base__prev_timestamp_3", some 115⟩]

/-- One fused instruction's twenty stateful/lookup interactions: four `bitwiseLookup` rows for the
    ALU result's limbs, a range check for the immediate, the `rs1` gadget and its receive/echo, the
    (structurally inactive, since `rs2_as_i = 0`) `rs2` gadget and receive/send, the write gadget
    and its receive, the write itself (`external` — the ALU result, justified by the caller), the
    register-file lookup, and the bridge receive/send. -/
def unoptInstrWitnesses (base : ℕ) : List ByteWitness :=
  [.notSend, .notSend, .notSend, .notSend, .notSend, .notSend, .notSend, .notSend,
   .echo (base + 7), .notSend, .notSend, .notSend, .notSend, .notSend, .notSend, .notSend,
   .external, .notSend, .notSend, .notMemory]

/-- The branch instruction's eleven: the `rs1` and `rs2` gadgets and their receive/echo, the
    register-file lookup, and the bridge receive/send — no write, so no `external`. -/
def unoptBranchWitnesses (base : ℕ) : List ByteWitness :=
  [.notSend, .notSend, .notSend, .echo (base + 2), .notSend, .notSend, .notSend,
   .echo (base + 6), .notSend, .notSend, .notMemory]

/-- The witness for each of `unoptChained`'s `71` interactions: three fused-instruction
    blocks of `20` (indices `0`, `20`, `40`) and the branch's `11` (index `60`). -/
def unoptWitnesses : List ByteWitness :=
  unoptInstrWitnesses 0 ++ unoptInstrWitnesses 20 ++ unoptInstrWitnesses 40 ++
    unoptBranchWitnesses 60

theorem unoptByteCheck :
    byteCheckAll unoptByteVars unoptPinRules unoptChained.busInteractions unoptWitnesses
      = true := by decide

/-- **`StepLayout.memSendsOk`, by static analysis.** `byteCheckAll` accounts for every echoed
    read and every interaction that isn't a genuine memory send; the three ALU writes are left to
    the caller, closed by `unoptWriteIsByte_0/1/2`. -/
theorem unoptChained_memSendsOk {asg : ChipAssignment babyBear}
    (halg : unoptChained.satisfiesAlgebraic asg)
    (hacc : unoptChained.satisfiesStateless apcRules asg) :
    ∀ i : Fin unoptChained.busInteractions.length,
      unoptChained.memSend apcRules asg i →
      (∀ j : Fin unoptChained.busInteractions.length, j < i →
        unoptChained.activeMem apcRules asg j →
        apcRules.payloadOk (unoptChained.msgAt asg j)) →
      apcRules.payloadOk (unoptChained.msgAt asg i) := by
  haveI : Fact (1 < babyBear) := ⟨by decide⟩
  refine memSendsOk_of_sendsOk (byteCheck_sendsOk (unoptPinRules_hold asg halg) unoptByteCheck ?_)
  intro i hi hsend hlow
  fin_cases i
  all_goals try exact absurd hi (by decide)
  · obtain ⟨h0, h1, h2, h3⟩ := unoptWriteIsByte_0 halg hacc
    show openVmPayloadOk defaultBusMap ((1 : ℕ), [(1 : ZMod babyBear), asg ⟨"rd_ptr_0", some 2⟩,
      asg ⟨"a__0_0", some 19⟩, asg ⟨"a__1_0", some 20⟩, asg ⟨"a__2_0", some 21⟩,
      asg ⟨"a__3_0", some 22⟩, asg ⟨"from_state__timestamp_0", some 1⟩ + 2])
    exact (openVmPayloadOk_mem_iff _ _ _ _ _ _).mpr ⟨h0, h1, h2, h3⟩
  · obtain ⟨h0, h1, h2, h3⟩ := unoptWriteIsByte_1 halg hacc
    show openVmPayloadOk defaultBusMap ((1 : ℕ), [(1 : ZMod babyBear), asg ⟨"rd_ptr_1", some 38⟩,
      asg ⟨"a__0_1", some 55⟩, asg ⟨"a__1_1", some 56⟩, asg ⟨"a__2_1", some 57⟩,
      asg ⟨"a__3_1", some 58⟩, asg ⟨"from_state__timestamp_1", some 37⟩ + 2])
    exact (openVmPayloadOk_mem_iff _ _ _ _ _ _).mpr ⟨h0, h1, h2, h3⟩
  · obtain ⟨h0, h1, h2, h3⟩ := unoptWriteIsByte_2 halg hacc
    show openVmPayloadOk defaultBusMap ((1 : ℕ), [(1 : ZMod babyBear), asg ⟨"rd_ptr_2", some 74⟩,
      asg ⟨"a__0_2", some 91⟩, asg ⟨"a__1_2", some 92⟩, asg ⟨"a__2_2", some 93⟩,
      asg ⟨"a__3_2", some 94⟩, asg ⟨"from_state__timestamp_2", some 73⟩ + 2])
    exact (openVmPayloadOk_mem_iff _ _ _ _ _ _).mpr ⟨h0, h1, h2, h3⟩

/-- Where each of `unoptChained`'s `71` interactions sits, as an upper bound on its
    offset from `from_state__timestamp_0`: the four fused steps' local offsets (one memory
    gadget's receive/send pair per instruction, two for the branch's `rs1`/`rs2`), shifted by
    each instruction's own `3`-tick advance
    (`chainedTimes`). Stateless positions, and the inactive `rs2` gadgets `rs2_as_i = 0` disables,
    get a placeholder far below every real offset — the domination check below never reads
    them for anything but a `<`, and they are never `activeStateful` either way. -/
def unoptOffsetUb : List ℤ :=
  -- instr 0 (shift 0)
  [-1000, -1000, -1000, -1000, -1000, -1000, -1000, -1, 0, -1000, -1000, -1000, -1000, -1000,
   -1000, 1, 2, -1000, -1000, -1000] ++
  -- instr 1 (shift 3)
  [-1000, -1000, -1000, -1000, -1000, -1000, -1000, 2, 3, -1000, -1000, -1000, -1000, -1000,
   -1000, 4, 5, -1000, -1000, -1000] ++
  -- instr 2 (shift 6)
  [-1000, -1000, -1000, -1000, -1000, -1000, -1000, 5, 6, -1000, -1000, -1000, -1000, -1000,
   -1000, 7, 8, -1000, -1000, -1000] ++
  -- instr 3 / branch (shift 9)
  [-1000, -1000, 8, 9, -1000, -1000, 9, 10, -1000, -1000, -1000]

/-- Each of `unoptChained`'s eight memory sends dominates every position before it —
    the ordering fact `memSendsOk` needs for this circuit, `decide` over `71` positions. Unlike
    `opt`, several sends share an upper bound with an *earlier, different* send's own
    predecessor (e.g. positions `36` and `47` both cap out at `5`) — harmless, since domination is
    only ever asked of a send against what precedes *it*, never between two unrelated positions. -/
theorem unoptOffsetUb_dominates :
    ∀ b ∈ [8, 16, 28, 36, 48, 56, 63, 67], ∀ k < b, unoptOffsetUb.getD k 0 < unoptOffsetUb.getD b 0 := by
  decide

/-- The exact offset each of `unoptChained`'s `71` interactions sits at, mirroring
    `unoptOffsetUb`'s shape but with each memory receive's real lookback (`δ - n`, from the eight
    `unoptLookback_*` lemmas) rather than its upper bound `δ`, and the bridge's own literal offsets
    filled in (the upper-bound table leaves those `-1000`, since ordering never reads them). -/
def unoptOffsets (nr10 nw0 nr11 nw1 nr12 nw2 nr13 nr23 : ℕ) : List ℤ :=
  -- instr 0 (shift 0)
  [-1000, -1000, -1000, -1000, -1000, -1000, -1000, -1 - (nr10 : ℤ), 0, -1000, -1000, -1000,
   -1000, -1000, -1000, 1 - (nw0 : ℤ), 2, -1000, 0, 3] ++
  -- instr 1 (shift 3)
  [-1000, -1000, -1000, -1000, -1000, -1000, -1000, 2 - (nr11 : ℤ), 3, -1000, -1000, -1000,
   -1000, -1000, -1000, 4 - (nw1 : ℤ), 5, -1000, 3, 6] ++
  -- instr 2 (shift 6)
  [-1000, -1000, -1000, -1000, -1000, -1000, -1000, 5 - (nr12 : ℤ), 6, -1000, -1000, -1000,
   -1000, -1000, -1000, 7 - (nw2 : ℤ), 8, -1000, 6, 9] ++
  -- instr 3 / branch (shift 9)
  [-1000, -1000, 8 - (nr13 : ℤ), 9, -1000, -1000, 9 - (nr23 : ℤ), 10, -1000, 9, 11]

set_option maxRecDepth 20000 in
set_option linter.unnecessarySeqFocus false in
/-- **A chained-but-unoptimized APC has a step layout.** `d = 11`, matching `opt`'s own
    arc: the four fused instructions' local `3`/`3`/`3`/`2`-tick advances, chained by
    `unoptChained_bridge`. Every one of the `71` interactions is placed by
    `unoptOffsets`, the eight memory sends dominate what precedes them (`unoptOffsetUb_dominates`),
    and `unoptChained_memSendsOk` closes the byte invariant.

    This is what `memSendsOk`'s restriction to the memory bus buys over the old cross-bus
    `ordered`: the bridge-round-trip-vs-echo timestamp collision that made this circuit fail the
    old `ordered` (two unrelated instructions' own bookkeeping landing on the same field
    timestamp) never enters a memory-vs-memory comparison, so it is not a counterexample here. -/
theorem unoptChained_hasStepLayout {maxWindow : ℕ} (hw : 11 < maxWindow) :
    unoptChained.hasStepLayout apcRules maxWindow openVmTimestampBound := by
  haveI : Fact (1 < babyBear) := ⟨by decide⟩
  intro asg halg hacc
  obtain ⟨nr10, hnr10, htr10⟩ := unoptLookback_r1_0 halg hacc
  obtain ⟨nw0, hnw0, htw0⟩ := unoptLookback_w_0 halg hacc
  obtain ⟨nr11, hnr11, htr11⟩ := unoptLookback_r1_1 halg hacc
  obtain ⟨nw1, hnw1, htw1⟩ := unoptLookback_w_1 halg hacc
  obtain ⟨nr12, hnr12, htr12⟩ := unoptLookback_r1_2 halg hacc
  obtain ⟨nw2, hnw2, htw2⟩ := unoptLookback_w_2 halg hacc
  obtain ⟨nr13, hnr13, htr13⟩ := unoptLookback_r1_3 halg hacc
  obtain ⟨nr23, hnr23, htr23⟩ := unoptLookback_r2_3 halg hacc
  obtain ⟨hs0, hs1, hs2, hs3, -, -, -, -, hrs0, hrs1, hrs2⟩ := unoptPins halg
  obtain ⟨ht01, ht12, ht23⟩ := chainedTimes halg
  obtain ⟨hrecv, hsend, hother⟩ := unoptChained_bridge halg
  have hub : ∀ i : Fin unoptChained.busInteractions.length,
      apcRules.isStateful (unoptChained.busInteractions.get i).busId = true →
      (unoptChained.busInteractions.get i).busId = apcRules.memBusId →
      ((unoptChained.busInteractions.get i).eval asg).multiplicity ≠ 0 →
      (unoptOffsets nr10 nw0 nr11 nw1 nr12 nw2 nr13 nr23).getD i.val 0
        ≤ unoptOffsetUb.getD i.val 0 := by
    intro i hst hbmem _
    fin_cases i <;>
      simp [unoptOffsets, unoptOffsetUb, unoptChained, unopt, apcRules,
        openVmGuestRules, openVmIsStateful, defaultBusMap, openVmMemBusId,
        OpenVmBusType.isStateful] at hst hbmem ⊢
  have hsendIdx : ∀ i : Fin unoptChained.busInteractions.length,
      apcRules.isStateful (unoptChained.busInteractions.get i).busId = true →
      (unoptChained.busInteractions.get i).busId = apcRules.memBusId →
      ((unoptChained.busInteractions.get i).eval asg).multiplicity = 1 →
      i.val ∈ [8, 16, 28, 36, 48, 56, 63, 67] ∧
      (unoptOffsets nr10 nw0 nr11 nw1 nr12 nw2 nr13 nr23).getD i.val 0
        = unoptOffsetUb.getD i.val 0 := by
    intro i hst hbmem hm
    fin_cases i <;>
      simp_all [unoptOffsets, unoptOffsetUb, unoptChained, unopt, apcRules,
        openVmGuestRules, openVmIsStateful, defaultBusMap, openVmMemBusId,
        OpenVmBusType.isStateful, BusInteraction.eval, Expression.eval, babyBear_negOne_ne_one]
  refine ⟨_, _, _, 11, by norm_num, hw, hrecv, hsend, hother,
    fun i => (unoptOffsets nr10 nw0 nr11 nw1 nr12 nw2 nr13 nr23).getD i.val 0, ?_, ?_⟩
  · -- The placement, offset by offset: `30` genuinely stateful positions (memory or bridge),
    -- read off directly; every other position is either stateless or a structurally inactive
    -- `rs2` gadget (`rs2_as_i = 0`, so its multiplicity can never be nonzero).
    rintro i ⟨hst, hm⟩
    fin_cases i <;>
      simp [unoptChained, unopt, apcRules, openVmGuestRules,
        openVmIsStateful, defaultBusMap, OpenVmBusType.isStateful] at hst
    · exact ⟨by simp [unoptOffsets, openVmTimestampBound, openVmTimestampBits]<;> omega,
        by simp [unoptOffsets]<;> omega,
        by simpa [unoptOffsets, unoptChained, unopt, BusInteraction.eval,
          Expression.eval, apcRules, openVmGuestRules, openVmTimestamp, Circuit.msgAt] using htr10⟩
    · exact ⟨by simp [unoptOffsets, openVmTimestampBound, openVmTimestampBits],
        by simp [unoptOffsets],
        by simp [unoptOffsets, unoptChained, unopt, BusInteraction.eval,
          Expression.eval, apcRules, openVmGuestRules, openVmTimestamp, Circuit.msgAt]⟩
    · exact absurd (by simp [unoptChained, unopt, Circuit.multAt, BusInteraction.eval,
        Expression.eval, hrs0]) hm
    · exact absurd (by simp [unoptChained, unopt, Circuit.multAt, BusInteraction.eval,
        Expression.eval, hrs0]) hm
    · exact ⟨by simp [unoptOffsets, openVmTimestampBound, openVmTimestampBits]<;> omega,
        by simp [unoptOffsets]<;> omega,
        by simpa [unoptOffsets, unoptChained, unopt, BusInteraction.eval,
          Expression.eval, apcRules, openVmGuestRules, openVmTimestamp, Circuit.msgAt] using htw0⟩
    · exact ⟨by simp [unoptOffsets, openVmTimestampBound, openVmTimestampBits],
        by simp [unoptOffsets],
        by simp [unoptOffsets, unoptChained, unopt, BusInteraction.eval,
          Expression.eval, apcRules, openVmGuestRules, openVmTimestamp, Circuit.msgAt]⟩
    · exact ⟨by simp [unoptOffsets, openVmTimestampBound, openVmTimestampBits],
        by simp [unoptOffsets],
        by simp [unoptOffsets, unoptChained, unopt, BusInteraction.eval,
          Expression.eval, apcRules, openVmGuestRules, openVmTimestamp, Circuit.msgAt,
          openVmMemBusId, openVmExecBusId]⟩
    · exact ⟨by simp [unoptOffsets, openVmTimestampBound, openVmTimestampBits],
        by simp [unoptOffsets],
        by simp [unoptOffsets, unoptChained, unopt, BusInteraction.eval,
          Expression.eval, apcRules, openVmGuestRules, openVmTimestamp, Circuit.msgAt,
          openVmMemBusId, openVmExecBusId]⟩
    · exact ⟨by simp [unoptOffsets, openVmTimestampBound, openVmTimestampBits]<;> omega,
        by simp [unoptOffsets]<;> omega,
        by have h := htr11
           simp [unoptOffsets, unoptChained, unopt, BusInteraction.eval,
             Expression.eval, apcRules, openVmGuestRules, openVmTimestamp, Circuit.msgAt,
             ht01] at h ⊢
           linear_combination h⟩
    · exact ⟨by simp [unoptOffsets, openVmTimestampBound, openVmTimestampBits],
        by simp [unoptOffsets],
        by simp [unoptOffsets, unoptChained, unopt, BusInteraction.eval,
          Expression.eval, apcRules, openVmGuestRules, openVmTimestamp, Circuit.msgAt, ht01]⟩
    · exact absurd (by simp [unoptChained, unopt, Circuit.multAt, BusInteraction.eval,
        Expression.eval, hrs1]) hm
    · exact absurd (by simp [unoptChained, unopt, Circuit.multAt, BusInteraction.eval,
        Expression.eval, hrs1]) hm
    · exact ⟨by simp [unoptOffsets, openVmTimestampBound, openVmTimestampBits]<;> omega,
        by simp [unoptOffsets]<;> omega,
        by have h := htw1
           simp [unoptOffsets, unoptChained, unopt, BusInteraction.eval,
             Expression.eval, apcRules, openVmGuestRules, openVmTimestamp, Circuit.msgAt,
             ht01] at h ⊢
           linear_combination h⟩
    · exact ⟨by simp [unoptOffsets, openVmTimestampBound, openVmTimestampBits],
        by simp [unoptOffsets],
        by simp [unoptOffsets, unoptChained, unopt, BusInteraction.eval,
          Expression.eval, apcRules, openVmGuestRules, openVmTimestamp, Circuit.msgAt, ht01] <;> ring⟩
    · exact ⟨by simp [unoptOffsets, openVmTimestampBound, openVmTimestampBits],
        by simp [unoptOffsets],
        by simp [unoptOffsets, unoptChained, unopt, BusInteraction.eval,
          Expression.eval, apcRules, openVmGuestRules, openVmTimestamp, Circuit.msgAt,
          openVmMemBusId, openVmExecBusId, ht01]⟩
    · exact ⟨by simp [unoptOffsets, openVmTimestampBound, openVmTimestampBits],
        by simp [unoptOffsets],
        by simp [unoptOffsets, unoptChained, unopt, BusInteraction.eval,
          Expression.eval, apcRules, openVmGuestRules, openVmTimestamp, Circuit.msgAt,
          openVmMemBusId, openVmExecBusId, ht01] <;> ring⟩
    · exact ⟨by simp [unoptOffsets, openVmTimestampBound, openVmTimestampBits]<;> omega,
        by simp [unoptOffsets]<;> omega,
        by have h := htr12
           simp [unoptOffsets, unoptChained, unopt, BusInteraction.eval,
             Expression.eval, apcRules, openVmGuestRules, openVmTimestamp, Circuit.msgAt,
             ht01, ht12] at h ⊢
           linear_combination h⟩
    · exact ⟨by simp [unoptOffsets, openVmTimestampBound, openVmTimestampBits],
        by simp [unoptOffsets],
        by simp [unoptOffsets, unoptChained, unopt, BusInteraction.eval,
          Expression.eval, apcRules, openVmGuestRules, openVmTimestamp, Circuit.msgAt, ht01, ht12] <;> ring⟩
    · exact absurd (by simp [unoptChained, unopt, Circuit.multAt, BusInteraction.eval,
        Expression.eval, hrs2]) hm
    · exact absurd (by simp [unoptChained, unopt, Circuit.multAt, BusInteraction.eval,
        Expression.eval, hrs2]) hm
    · exact ⟨by simp [unoptOffsets, openVmTimestampBound, openVmTimestampBits]<;> omega,
        by simp [unoptOffsets]<;> omega,
        by have h := htw2
           simp [unoptOffsets, unoptChained, unopt, BusInteraction.eval,
             Expression.eval, apcRules, openVmGuestRules, openVmTimestamp, Circuit.msgAt,
             ht01, ht12] at h ⊢
           linear_combination h⟩
    · exact ⟨by simp [unoptOffsets, openVmTimestampBound, openVmTimestampBits],
        by simp [unoptOffsets],
        by simp [unoptOffsets, unoptChained, unopt, BusInteraction.eval,
          Expression.eval, apcRules, openVmGuestRules, openVmTimestamp, Circuit.msgAt, ht01, ht12] <;> ring⟩
    · exact ⟨by simp [unoptOffsets, openVmTimestampBound, openVmTimestampBits],
        by simp [unoptOffsets],
        by simp [unoptOffsets, unoptChained, unopt, BusInteraction.eval,
          Expression.eval, apcRules, openVmGuestRules, openVmTimestamp, Circuit.msgAt,
          openVmMemBusId, openVmExecBusId, ht01, ht12] <;> ring⟩
    · exact ⟨by simp [unoptOffsets, openVmTimestampBound, openVmTimestampBits],
        by simp [unoptOffsets],
        by simp [unoptOffsets, unoptChained, unopt, BusInteraction.eval,
          Expression.eval, apcRules, openVmGuestRules, openVmTimestamp, Circuit.msgAt,
          openVmMemBusId, openVmExecBusId, ht01, ht12] <;> ring⟩
    · exact ⟨by simp [unoptOffsets, openVmTimestampBound, openVmTimestampBits]<;> omega,
        by simp [unoptOffsets]<;> omega,
        by have h := htr13
           simp [unoptOffsets, unoptChained, unopt, BusInteraction.eval,
             Expression.eval, apcRules, openVmGuestRules, openVmTimestamp, Circuit.msgAt,
             ht01, ht12, ht23] at h ⊢
           linear_combination h⟩
    · exact ⟨by simp [unoptOffsets, openVmTimestampBound, openVmTimestampBits],
        by simp [unoptOffsets],
        by simp [unoptOffsets, unoptChained, unopt, BusInteraction.eval,
          Expression.eval, apcRules, openVmGuestRules, openVmTimestamp, Circuit.msgAt, ht01, ht12, ht23] <;> ring⟩
    · exact ⟨by simp [unoptOffsets, openVmTimestampBound, openVmTimestampBits]<;> omega,
        by simp [unoptOffsets]<;> omega,
        by have h := htr23
           simp [unoptOffsets, unoptChained, unopt, BusInteraction.eval,
             Expression.eval, apcRules, openVmGuestRules, openVmTimestamp, Circuit.msgAt,
             ht01, ht12, ht23] at h ⊢
           linear_combination h⟩
    · exact ⟨by simp [unoptOffsets, openVmTimestampBound, openVmTimestampBits],
        by simp [unoptOffsets],
        by simp [unoptOffsets, unoptChained, unopt, BusInteraction.eval,
          Expression.eval, apcRules, openVmGuestRules, openVmTimestamp, Circuit.msgAt, ht01, ht12, ht23] <;> ring⟩
    · exact ⟨by simp [unoptOffsets, openVmTimestampBound, openVmTimestampBits],
        by simp [unoptOffsets],
        by simp [unoptOffsets, unoptChained, unopt, BusInteraction.eval,
          Expression.eval, apcRules, openVmGuestRules, openVmTimestamp, Circuit.msgAt,
          openVmMemBusId, openVmExecBusId, ht01, ht12, ht23] <;> ring⟩
    · exact ⟨by simp [unoptOffsets, openVmTimestampBound, openVmTimestampBits],
        by simp [unoptOffsets],
        by simp [unoptOffsets, unoptChained, unopt, BusInteraction.eval,
          Expression.eval, apcRules, openVmGuestRules, openVmTimestamp, Circuit.msgAt,
          openVmMemBusId, openVmExecBusId, ht01, ht12, ht23] <;> ring⟩
  · -- The byte invariant: `unoptChained_memSendsOk`, by static analysis. What used to be
    -- `memOrdered` (`unoptOffsetUb_dominates`) is inlined here, converting the caller's
    -- `place`-ordered hypothesis into the index order that theorem expects.
    intro i hsend hlow
    refine unoptChained_memSendsOk halg hacc i hsend (fun j hji hactj => ?_)
    obtain ⟨hmem, heq⟩ := hsendIdx i hsend.1.1 hsend.2 hsend.1.2
    refine hlow j ?_ hactj
    show (unoptOffsets nr10 nw0 nr11 nw1 nr12 nw2 nr13 nr23).getD j.val 0
      < (unoptOffsets nr10 nw0 nr11 nw1 nr12 nw2 nr13 nr23).getD i.val 0
    rw [heq]
    exact lt_of_le_of_lt (hub j hactj.1.1 hactj.2 hactj.1.2)
      (unoptOffsetUb_dominates i.val hmem j.val (Fin.lt_def.mp hji))

theorem unoptChained_legalGuest {maxWindow maxInteractions : ℕ} (hw : 11 < maxWindow)
    (hi : 71 ≤ maxInteractions) :
    unoptChained.legalGuest apcRules maxWindow openVmTimestampBound
      maxInteractions where
  sendOnly := unoptChained_legalMultiplicities.1
  polarity := unoptChained_legalMultiplicities.2
  stepLayout := unoptChained_hasStepLayout hw
  size := by simpa [unoptChained, unopt] using hi

end ApcOptimizer.OpenVM.Keccak2105000
