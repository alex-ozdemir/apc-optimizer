import ApcOptimizer.VmSpec.Audit.Apcs.SingleXor.Layout

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

/-! **The unoptimized stage: `Circuit.legalGuest` in full.** Its multiplicities are opcode-flag
    sums rather than literals, so they need the constant-propagation tier; powdr has not run its
    substitution pass yet, so each memory receive's offset comes from the *raw* lt gadget
    (`gadgetLookback_raw`); and the write's limbs are bytes only through a one-hot decomposition of
    the opcode selector (`isByte_of_aluLimb`), since at this stage the circuit still admits all
    five ALU operations.

    Unlike `Keccak2105000`, this stage already has a step layout: it is one instruction, so there
    are no intermediate bridge states to cancel and nothing to chain. It reuses `Layout.lean`'s
    `baseE` but needs its own variable list — the unoptimized circuit still carries the register
    pointers and the opcode flags the optimizer later folds away. -/

namespace ApcOptimizer.OpenVM.SingleXor

/-- **The strengthened check passes on the unoptimized APC.** Its multiplicities are not literals —
    each is this instruction's opcode-flag sum, or the second operand's address space — so
    `checkMultiplicities` cannot see them. `checkMultiplicitiesWith` reads pin rules off the
    constraints, among them `1 - (add + sub + xor + or + and) = 0` and `rs2_as_0 - 1 = 0`, and
    every one of the 20 multiplicities folds against them. -/
theorem unopt_checkMultiplicitiesWith :
    checkMultiplicitiesWith apcRules.isStateful unopt = true := by decide

/-- **Both multiplicity clauses for the unoptimized APC**, again from the `Bool` rather than from a
    proof about this circuit. With `opt_legalMultiplicities` this says the two clauses survive
    powdr's optimizer on this instruction. -/
theorem unopt_legalMultiplicities :
    unopt.statelessSendOnly apcRules ∧ unopt.statefulPolarity apcRules :=
  checkMultiplicitiesWith_sound unopt_checkMultiplicitiesWith rfl

/-- **The unoptimized APC has no padding row either**: it pins the opcode-flag sum to `1`
    (`1 - (add + sub + xor + or + and) = 0`), which the all-zero assignment violates. -/
theorem unopt_zero_not_satisfiesAlgebraic :
    ¬ unopt.satisfiesAlgebraic (fun _ => 0) := by
  intro h
  have := h
    (.add (.mul (.const 2013265920)
        (.add (.add (.add (.add (.add (.const 0) (.var ⟨"opcode_add_flag_0", some 31⟩))
          (.var ⟨"opcode_sub_flag_0", some 32⟩)) (.var ⟨"opcode_xor_flag_0", some 33⟩))
          (.var ⟨"opcode_or_flag_0", some 34⟩)) (.var ⟨"opcode_and_flag_0", some 35⟩)))
      (.const 1))
    (by simp [unopt])
  simp only [Expression.eval] at this
  exact absurd this (by decide)

--------- The step layout ---------

/-- The pins `unopt`'s own constraints supply that the placement needs: its opcode-flag sum is `1`
    (constraint `22`) and its second operand is a register rather than an immediate (constraint
    `29`, `rs2_as_0 - 1 = 0`), so the second read is live. Constraints are addressed by index
    rather than restated. -/
theorem unoptPins {asg : ChipAssignment babyBear} (halg : unopt.satisfiesAlgebraic asg) :
    (asg ⟨"opcode_add_flag_0", some 31⟩ + asg ⟨"opcode_sub_flag_0", some 32⟩
        + asg ⟨"opcode_xor_flag_0", some 33⟩ + asg ⟨"opcode_or_flag_0", some 34⟩
        + asg ⟨"opcode_and_flag_0", some 35⟩ = 1) ∧
    asg ⟨"rs2_as_0", some 5⟩ = 1 := by
  have hfs := halg _ (List.getElem_mem (show 22 < unopt.algebraicConstraints.length by decide))
  have hrs := halg _ (List.getElem_mem (show 29 < unopt.algebraicConstraints.length by decide))
  simp only [unopt, List.getElem_cons_succ, List.getElem_cons_zero, Expression.eval] at hfs hrs
  rw [babyBear_negOne] at hfs hrs
  exact ⟨by linear_combination -hfs, by linear_combination hrs⟩

/-- The `rs1` read, whose echo sends at offset `0`: constraint `18` is the gadget's own equation,
    which powdr's substitution pass has not yet removed. -/
theorem unoptLookback_r1 {asg : ChipAssignment babyBear}
    (halg : unopt.satisfiesAlgebraic asg) (hacc : unopt.satisfiesStateless apcRules asg) :
    ∃ n : ℕ, n < 2 ^ 29 ∧
      asg ⟨"reads_aux__0__base__prev_timestamp_0", some 6⟩
        = asg ⟨"from_state__timestamp_0", some 1⟩ + ((((-1) - (n : ℤ)) : ℤ) : ZMod babyBear) := by
  have hgate := (unoptPins halg).1
  have hcon := halg _ (List.getElem_mem (show 18 < unopt.algebraicConstraints.length by decide))
  simp only [unopt, List.getElem_cons_succ, List.getElem_cons_zero, Expression.eval] at hcon
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
    (asg ⟨"from_state__timestamp_0", some 1⟩) hlo hhi
    (by push_cast at heq ⊢; linear_combination heq)
  exact ⟨n, hn29, hplace⟩

/-- The `rs2` read, whose echo sends at offset `1`: constraint `20`, gated on `rs2_as_0` rather
    than on the flag sum — this read happens only because the operand is a register. -/
theorem unoptLookback_r2 {asg : ChipAssignment babyBear}
    (halg : unopt.satisfiesAlgebraic asg) (hacc : unopt.satisfiesStateless apcRules asg) :
    ∃ n : ℕ, n < 2 ^ 29 ∧
      asg ⟨"reads_aux__1__base__prev_timestamp_0", some 9⟩
        = asg ⟨"from_state__timestamp_0", some 1⟩ + (((0 - (n : ℤ)) : ℤ) : ZMod babyBear) := by
  have hgate := (unoptPins halg).2
  have hne : asg ⟨"rs2_as_0", some 5⟩ ≠ 0 := by rw [hgate]; decide
  have hcon := halg _ (List.getElem_mem (show 20 < unopt.algebraicConstraints.length by decide))
  simp only [unopt, List.getElem_cons_succ, List.getElem_cons_zero, Expression.eval] at hcon
  rw [babyBear_negOne] at hcon
  have heq := gadgetLookback_raw (δ := 1)
    (ts := asg ⟨"from_state__timestamp_0", some 1⟩)
    (prev := asg ⟨"reads_aux__1__base__prev_timestamp_0", some 9⟩)
    (lo := asg ⟨"reads_aux__1__base__timestamp_lt_aux__lower_decomp__0_0", some 10⟩)
    (hi := asg ⟨"reads_aux__1__base__timestamp_lt_aux__lower_decomp__1_0", some 11⟩)
    hgate (by linear_combination hcon)
  have hlo := accepts_congr_mult3 (m2 := 1) (acceptsAt hacc 9 (by decide) _ rfl rfl hne)
  have hhi := accepts_congr_mult3 (m2 := 1) (acceptsAt hacc 10 (by decide) _ rfl rfl hne)
  simp only [Expression.eval] at hlo hhi
  obtain ⟨n, -, hn29, hplace⟩ := lt_gadget_offset 0
    (asg ⟨"reads_aux__1__base__prev_timestamp_0", some 9⟩)
    (asg ⟨"from_state__timestamp_0", some 1⟩) hlo hhi
    (by push_cast at heq ⊢; linear_combination heq)
  exact ⟨n, hn29, hplace⟩

/-- The write, whose send sits at offset `2`: constraint `21`. -/
theorem unoptLookback_w {asg : ChipAssignment babyBear}
    (halg : unopt.satisfiesAlgebraic asg) (hacc : unopt.satisfiesStateless apcRules asg) :
    ∃ n : ℕ, n < 2 ^ 29 ∧
      asg ⟨"writes_aux__base__prev_timestamp_0", some 12⟩
        = asg ⟨"from_state__timestamp_0", some 1⟩ + (((1 - (n : ℤ)) : ℤ) : ZMod babyBear) := by
  have hgate := (unoptPins halg).1
  have hcon := halg _ (List.getElem_mem (show 21 < unopt.algebraicConstraints.length by decide))
  simp only [unopt, List.getElem_cons_succ, List.getElem_cons_zero, Expression.eval] at hcon
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
  obtain ⟨n, -, hn29, hplace⟩ := lt_gadget_offset 1
    (asg ⟨"writes_aux__base__prev_timestamp_0", some 12⟩)
    (asg ⟨"from_state__timestamp_0", some 1⟩) hlo hhi
    (by push_cast at heq ⊢; linear_combination heq)
  exact ⟨n, hn29, hplace⟩

/-- The opcode selector is one-hot, from its five booleanity constraints (`0`–`4`) and
    `unoptPins`'s flag sum. -/
theorem unoptAluCase {asg : ChipAssignment babyBear} (halg : unopt.satisfiesAlgebraic asg) :
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
  have hb_add := halg _ (List.getElem_mem (show 0 < unopt.algebraicConstraints.length by decide))
  have hb_sub := halg _ (List.getElem_mem (show 1 < unopt.algebraicConstraints.length by decide))
  have hb_xor := halg _ (List.getElem_mem (show 2 < unopt.algebraicConstraints.length by decide))
  have hb_or := halg _ (List.getElem_mem (show 3 < unopt.algebraicConstraints.length by decide))
  have hb_and := halg _ (List.getElem_mem (show 4 < unopt.algebraicConstraints.length by decide))
  simp only [unopt, List.getElem_cons_succ, List.getElem_cons_zero, Expression.eval]
    at hb_add hb_sub hb_xor hb_or hb_and
  exact aluOneHot (unoptPins halg).1 hb_add hb_sub hb_xor hb_or hb_and

/-- **The write's four limbs are bytes**, whichever of the five ALU operations is active: each
    limb has its own `bitwiseLookup` row (`0`–`3`), and `isByte_of_aluLimb` reads the limb out of
    it in every one-hot case. This is the one thing a decidable byte check cannot settle. -/
theorem unoptWriteIsByte {asg : ChipAssignment babyBear}
    (halg : unopt.satisfiesAlgebraic asg) (hacc : unopt.satisfiesStateless apcRules asg) :
    isByte (asg ⟨"a__0_0", some 19⟩) ∧ isByte (asg ⟨"a__1_0", some 20⟩) ∧
      isByte (asg ⟨"a__2_0", some 21⟩) ∧ isByte (asg ⟨"a__3_0", some 22⟩) := by
  have hgate := (unoptPins halg).1
  have hcase := unoptAluCase halg
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

/-- The variables the unoptimized APC's stateful payloads mention: the optimized stage's list plus
    the register pointers, the second operand's address space and the `pc`, none of which powdr has
    folded away yet. -/
def unoptVars : List Variable :=
  layoutVars ++
  [⟨"from_state__pc_0", some 0⟩, ⟨"rd_ptr_0", some 2⟩, ⟨"rs1_ptr_0", some 3⟩,
   ⟨"rs2_0", some 4⟩, ⟨"rs2_as_0", some 5⟩]

def unoptBaseF : LinForm babyBear := LinForm.varF unoptVars ⟨"from_state__timestamp_0", some 1⟩

def unoptPinRules : List (PinRule babyBear) :=
  unopt.algebraicConstraints.filterMap pinRuleOf

theorem unoptPinRules_hold (asg : ChipAssignment babyBear)
    (halg : unopt.satisfiesAlgebraic asg) : ∀ q ∈ unoptPinRules, q.1.eval asg = q.2 := by
  intro q hq
  obtain ⟨con, hcon, hpin⟩ := List.mem_filterMap.mp hq
  exact pinRuleOf_eval (by rw [hpin]) (halg con hcon)

theorem unoptBaseLin : Expression.toLin unoptVars unoptPinRules baseE = some unoptBaseF := by
  decide

theorem unoptBridgeCheck :
    bridgeCheck unoptVars unoptPinRules 0 unopt 3 1 (.const 0) baseE (.const 4) = true := by decide

/-- Where each of the unoptimized APC's eight stateful interactions sits. powdr emits each lt
    gadget's range checks just before the access they date, and the bridge last, so the order is
    not the optimized stage's. -/
def unoptOffsets (nr0 nr1 nw : ℕ) : List ℤ :=
  [0, 0, 0, 0, 0, 0, 0, -1 - (nr0 : ℤ), 0, 0, 0, -(nr1 : ℤ), 1, 0, 0, 1 - (nw : ℤ), 2, 0, 0, 3]

/-- As in `Layout.lean`, only the memory bus is read off this table, so the lookups and the two
    bridge entries are free to sit below every memory send. -/
def unoptOffsetUb : List ℤ :=
  [-2, -2, -2, -2, -2, -2, -2, -1, 0, -2, -2, 0, 1, 0, 0, 1, 2, 0, 0, 3]

theorem unoptOffsetUb_dominates :
    ∀ b ∈ [8, 12, 16], ∀ k < b, unoptOffsetUb.getD k 0 < unoptOffsetUb.getD b 0 := by decide

/-- Both register reads are echoed straight back; the write at position `16` is left to the caller
    (`unoptWriteIsByte`). The bitwise and range lookups and the register-file lookup on bus `2` are
    not stateful, and the bridge send is not memory. -/
def unoptWitnesses : List ByteWitness :=
  [.notSend, .notSend, .notSend, .notSend, .notSend, .notSend, .notSend, .notSend,
   .echo 7, .notSend, .notSend, .notSend, .echo 11, .notSend, .notSend, .notSend,
   .external, .notSend, .notSend, .notMemory]

theorem unoptByteCheck :
    byteCheckAll unoptVars unoptPinRules unopt.busInteractions unoptWitnesses = true := by decide

/-- **The unoptimized APC already has a step layout.** One instruction is one step: there are no
    intermediate bridge states to cancel, so unlike `Keccak2105000.unopt` this needs no chaining
    modification, and `Circuit.legalGuest` holds at every stage of this APC's pipeline except the
    gated output. -/
theorem unopt_hasStepLayout {maxWindow : ℕ} (hw : 3 < maxWindow) :
    unopt.hasStepLayout apcRules maxWindow openVmTimestampBound := by
  haveI : Fact (1 < babyBear) := ⟨by decide⟩
  intro asg halg hacc
  have hgate := (unoptPins halg).1
  have hrs2 := (unoptPins halg).2
  obtain ⟨nr0, hnr0, htr0⟩ := unoptLookback_r1 halg hacc
  obtain ⟨nr1, hnr1, htr1⟩ := unoptLookback_r2 halg hacc
  obtain ⟨nw, hnw, htw⟩ := unoptLookback_w halg hacc
  obtain ⟨ha0, ha1, ha2, ha3⟩ := unoptWriteIsByte halg hacc
  have hub : ∀ i : Fin unopt.busInteractions.length, unopt.activeMem apcRules asg i →
      (unoptOffsets nr0 nr1 nw).getD i.val 0 ≤ unoptOffsetUb.getD i.val 0 := by
    intro i hi
    obtain ⟨⟨hst, -⟩, hmem⟩ := hi
    fin_cases i <;>
      simp [unoptOffsets, unoptOffsetUb, unopt, apcRules, openVmGuestRules, openVmIsStateful,
        defaultBusMap, OpenVmBusType.isStateful, openVmMemBusId] at hst hmem ⊢
  have hsendIdx : ∀ i : Fin unopt.busInteractions.length, unopt.memSend apcRules asg i →
      i.val ∈ [8, 12, 16] ∧
        (unoptOffsets nr0 nr1 nw).getD i.val 0 = unoptOffsetUb.getD i.val 0 := by
    intro i hi
    obtain ⟨⟨hst, hm⟩, hmem⟩ := hi
    fin_cases i <;>
      simp_all [unoptOffsets, unoptOffsetUb, unopt, apcRules, openVmGuestRules, openVmIsStateful,
        defaultBusMap, OpenVmBusType.isStateful, openVmMemBusId, Circuit.multAt,
        BusInteraction.eval, Expression.eval, babyBear_negOne_ne_one]
  obtain ⟨hrecv, hsend, hother⟩ :=
    bridgeCheck_sound unoptBridgeCheck (unoptPinRules_hold asg halg)
  refine ⟨_, _, _, 3, by norm_num, hw, hrecv, hsend, hother,
    fun i => (unoptOffsets nr0 nr1 nw).getD i.val 0, ?_, ?_⟩
  · -- The placement, offset by offset.
    rintro i ⟨hst, hm⟩
    fin_cases i
    case «7» =>
      exact ⟨by simp [unoptOffsets, openVmTimestampBound, openVmTimestampBits]; omega,
        by simp [unoptOffsets]; omega,
        by simpa [unoptOffsets, baseE, unopt, BusInteraction.eval, Expression.eval, apcRules,
          openVmGuestRules, openVmTimestamp, Circuit.msgAt] using htr0⟩
    case «11» =>
      exact ⟨by simp [unoptOffsets, openVmTimestampBound, openVmTimestampBits]; omega,
        by simp [unoptOffsets],
        by simpa [unoptOffsets, baseE, unopt, BusInteraction.eval, Expression.eval, apcRules,
          openVmGuestRules, openVmTimestamp, Circuit.msgAt] using htr1⟩
    case «15» =>
      exact ⟨by simp [unoptOffsets, openVmTimestampBound, openVmTimestampBits]; omega,
        by simp [unoptOffsets]; omega,
        by simpa [unoptOffsets, baseE, unopt, BusInteraction.eval, Expression.eval, apcRules,
          openVmGuestRules, openVmTimestamp, Circuit.msgAt] using htw⟩
    case «8» | «12» | «16» =>
      all_goals
        exact ⟨by simp [unoptOffsets, openVmTimestampBound, openVmTimestampBits],
          by simp [unoptOffsets],
          by simp [unoptOffsets, baseE, unopt, BusInteraction.eval, Expression.eval, apcRules,
            openVmGuestRules, openVmTimestamp, Circuit.msgAt]⟩
    case «18» | «19» =>
      all_goals
        exact ⟨by simp [unoptOffsets, openVmTimestampBound, openVmTimestampBits],
          by simp [unoptOffsets],
          by simp [unoptOffsets, baseE, unopt, BusInteraction.eval, Expression.eval, apcRules,
            openVmGuestRules, openVmTimestamp, Circuit.msgAt, openVmMemBusId, openVmExecBusId]⟩
    all_goals
      simp [unopt, apcRules, openVmGuestRules, openVmIsStateful, defaultBusMap,
        OpenVmBusType.isStateful] at hst
  · -- The byte invariant: the two echoes are decided, the ALU write is `unoptWriteIsByte`.
    intro i hsend hlow
    have hordered : ∀ j : Fin unopt.busInteractions.length, j < i →
        unopt.activeMem apcRules asg j →
        apcRules.payloadOk (unopt.msgAt asg j) := by
      intro j hji hactj
      obtain ⟨hmem, heq⟩ := hsendIdx i hsend
      refine hlow j ?_ hactj
      show (unoptOffsets nr0 nr1 nw).getD j.val 0 < (unoptOffsets nr0 nr1 nw).getD i.val 0
      rw [heq]
      exact lt_of_le_of_lt (hub j hactj)
        (unoptOffsetUb_dominates i.val hmem j.val (Fin.lt_def.mp hji))
    refine memSendsOk_of_sendsOk
      (byteCheck_sendsOk (unoptPinRules_hold asg halg) unoptByteCheck ?_) i hsend hordered
    intro i hi hsend hlow
    fin_cases i
    all_goals try exact absurd hi (by decide)
    show openVmPayloadOk defaultBusMap ((1 : ℕ), [(1 : ZMod babyBear), asg ⟨"rd_ptr_0", some 2⟩,
      asg ⟨"a__0_0", some 19⟩, asg ⟨"a__1_0", some 20⟩, asg ⟨"a__2_0", some 21⟩,
      asg ⟨"a__3_0", some 22⟩, asg ⟨"from_state__timestamp_0", some 1⟩ + 2])
    exact (openVmPayloadOk_mem_iff _ _ _ _ _ _).mpr ⟨ha0, ha1, ha2, ha3⟩

theorem unopt_legalGuest {maxWindow maxInteractions : ℕ} (hw : 3 < maxWindow)
    (hi : 20 ≤ maxInteractions) :
    unopt.legalGuest apcRules maxWindow openVmTimestampBound maxInteractions where
  sendOnly := unopt_legalMultiplicities.1
  polarity := unopt_legalMultiplicities.2
  stepLayout := unopt_hasStepLayout hw
  size := by simpa [unopt] using hi

end ApcOptimizer.OpenVM.SingleXor
