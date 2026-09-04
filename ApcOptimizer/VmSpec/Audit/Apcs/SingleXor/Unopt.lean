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
    ¬ unopt.satisfiesAlgebraic (fun _ => 0) :=
  not_satisfiesAlgebraic_of_not_forall (by decide)

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

/-- Where each interaction sits, as a `Recipe`. powdr emits each lt gadget's range checks just
    before the access they date, and the bridge last, so the order is not the optimized stage's. -/
def unoptRecipes : List (Recipe babyBear) :=
  [.fixed 0, .fixed 0, .fixed 0, .fixed 0, .fixed 0, .fixed 0, .fixed 0,
   .lookback (-1) 131072 (.var ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_0", some 7⟩)
     (.var ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__1_0", some 8⟩),
   .fixed 0, .fixed 0, .fixed 0,
   .lookback 0 131072 (.var ⟨"reads_aux__1__base__timestamp_lt_aux__lower_decomp__0_0", some 10⟩)
     (.var ⟨"reads_aux__1__base__timestamp_lt_aux__lower_decomp__1_0", some 11⟩),
   .fixed 1, .fixed 0, .fixed 0,
   .lookback 1 131072 (.var ⟨"writes_aux__base__timestamp_lt_aux__lower_decomp__0_0", some 13⟩)
     (.var ⟨"writes_aux__base__timestamp_lt_aux__lower_decomp__1_0", some 14⟩),
   .fixed 2, .fixed 0, .fixed 0, .fixed 3]

theorem unoptPlaceCheck :
    placeCheckAll unoptVars unoptPinRules apcRules.isStateful openVmTsPos unoptBaseF
      unopt.busInteractions unoptRecipes = true := by decide

theorem unoptOrderCheck :
    memOrderCheck unoptPinRules openVmMemBusId openVmTimestampBound unopt.busInteractions
      unoptRecipes = true := by decide

theorem unoptFitsCheck :
    (List.range unopt.busInteractions.length).all
      (fun i => (unoptRecipes.getD i (.fixed 0)).fits openVmTimestampBound 3) = true := by decide

/-- Both register reads are echoed straight back; the write at position `16` is left to the caller
    (`unoptWriteIsByte`). The bitwise and range lookups and the register-file lookup on bus `2` are
    not stateful, and the bridge send is not memory. -/
def unoptWitnesses : List ByteWitness :=
  [.notSend, .notSend, .notSend, .notSend, .notSend, .notSend, .notSend, .notSend,
   .echo 7, .notSend, .notSend, .notSend, .echo 11, .notSend, .notSend, .notSend,
   .external, .notSend, .notSend, .notMemory]

theorem unoptByteCheck :
    byteCheckAll unoptVars unoptPinRules unopt.busInteractions unoptWitnesses = true := by decide

/-- Where each memory receive reaches back to. powdr's substitution pass has not run, so the
    offsets come off the *raw* gadget constraint (`gadgetLookback_raw`) rather than off a surviving
    range-check payload. Constraints are addressed by index rather than restated. -/
theorem unoptLookbacks {asg : ChipAssignment babyBear}
    (halg : unopt.satisfiesAlgebraic asg) (hacc : unopt.satisfiesStateless apcRules asg)
    (i : Fin unopt.busInteractions.length) (k : ℤ) (radix : ℕ) (loE hiE : Expression babyBear)
    (hrc : unoptRecipes.getD i.val (.fixed 0) = .lookback k radix loE hiE) :
    (unoptRecipes.getD i.val (.fixed 0)).back asg < openVmTimestampBound ∧
      apcRules.getTimestamp (unopt.msgAt asg i)
        = baseE.eval asg
          + (((unoptRecipes.getD i.val (.fixed 0)).place asg : ℤ) : ZMod babyBear) := by
  have hgate := (unoptPins halg).1
  have hrs2 : asg ⟨"rs2_as_0", some 5⟩ ≠ 0 := by rw [(unoptPins halg).2]; decide
  fin_cases i
  case «7» =>
    have hcon := halg _ (List.getElem_mem (show 18 < unopt.algebraicConstraints.length by decide))
    simp only [unopt, List.getElem_cons_succ, List.getElem_cons_zero, Expression.eval] at hcon
    rw [babyBear_negOne] at hcon
    have heq := gadgetLookback_raw (δ := 0)
      (ts := asg ⟨"from_state__timestamp_0", some 1⟩)
      (prev := asg ⟨"reads_aux__0__base__prev_timestamp_0", some 6⟩)
      (lo := asg ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_0", some 7⟩) (hi := asg ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__1_0", some 8⟩)
      hgate (by linear_combination hcon)
    have hlo := accepts_congr_mult3 (m2 := 1) (acceptsAt hacc 5 (by decide) _ rfl rfl (sum5_eq1_ne_zero hgate))
    have hhi := accepts_congr_mult3 (m2 := 1) (acceptsAt hacc 6 (by decide) _ rfl rfl (sum5_eq1_ne_zero hgate))
    simp only [Expression.eval] at hlo hhi
    exact lookback_of_limbs (k := (-1)) (baseE := baseE)
      (tsE := .var ⟨"reads_aux__0__base__prev_timestamp_0", some 6⟩)
      (loE := .var ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_0", some 7⟩) (hiE := .var ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__1_0", some 8⟩)
      hlo hhi (by simp only [baseE, Expression.eval]; push_cast at heq ⊢; linear_combination heq)
  case «11» =>
    have hcon := halg _ (List.getElem_mem (show 20 < unopt.algebraicConstraints.length by decide))
    simp only [unopt, List.getElem_cons_succ, List.getElem_cons_zero, Expression.eval] at hcon
    rw [babyBear_negOne] at hcon
    have heq := gadgetLookback_raw (δ := 1)
      (ts := asg ⟨"from_state__timestamp_0", some 1⟩)
      (prev := asg ⟨"reads_aux__1__base__prev_timestamp_0", some 9⟩)
      (lo := asg ⟨"reads_aux__1__base__timestamp_lt_aux__lower_decomp__0_0", some 10⟩) (hi := asg ⟨"reads_aux__1__base__timestamp_lt_aux__lower_decomp__1_0", some 11⟩)
      (unoptPins halg).2 (by linear_combination hcon)
    have hlo := accepts_congr_mult3 (m2 := 1) (acceptsAt hacc 9 (by decide) _ rfl rfl hrs2)
    have hhi := accepts_congr_mult3 (m2 := 1) (acceptsAt hacc 10 (by decide) _ rfl rfl hrs2)
    simp only [Expression.eval] at hlo hhi
    exact lookback_of_limbs (k := 0) (baseE := baseE)
      (tsE := .var ⟨"reads_aux__1__base__prev_timestamp_0", some 9⟩)
      (loE := .var ⟨"reads_aux__1__base__timestamp_lt_aux__lower_decomp__0_0", some 10⟩) (hiE := .var ⟨"reads_aux__1__base__timestamp_lt_aux__lower_decomp__1_0", some 11⟩)
      hlo hhi (by simp only [baseE, Expression.eval]; push_cast at heq ⊢; linear_combination heq)
  case «15» =>
    have hcon := halg _ (List.getElem_mem (show 21 < unopt.algebraicConstraints.length by decide))
    simp only [unopt, List.getElem_cons_succ, List.getElem_cons_zero, Expression.eval] at hcon
    rw [babyBear_negOne] at hcon
    have heq := gadgetLookback_raw (δ := 2)
      (ts := asg ⟨"from_state__timestamp_0", some 1⟩)
      (prev := asg ⟨"writes_aux__base__prev_timestamp_0", some 12⟩)
      (lo := asg ⟨"writes_aux__base__timestamp_lt_aux__lower_decomp__0_0", some 13⟩) (hi := asg ⟨"writes_aux__base__timestamp_lt_aux__lower_decomp__1_0", some 14⟩)
      hgate (by linear_combination hcon)
    have hlo := accepts_congr_mult3 (m2 := 1) (acceptsAt hacc 13 (by decide) _ rfl rfl (sum5_eq1_ne_zero hgate))
    have hhi := accepts_congr_mult3 (m2 := 1) (acceptsAt hacc 14 (by decide) _ rfl rfl (sum5_eq1_ne_zero hgate))
    simp only [Expression.eval] at hlo hhi
    exact lookback_of_limbs (k := 1) (baseE := baseE)
      (tsE := .var ⟨"writes_aux__base__prev_timestamp_0", some 12⟩)
      (loE := .var ⟨"writes_aux__base__timestamp_lt_aux__lower_decomp__0_0", some 13⟩) (hiE := .var ⟨"writes_aux__base__timestamp_lt_aux__lower_decomp__1_0", some 14⟩)
      hlo hhi (by simp only [baseE, Expression.eval]; push_cast at heq ⊢; linear_combination heq)
  all_goals simp [unoptRecipes] at hrc

/-- The ALU write at position `16`, the one send a decidable check cannot vouch for. -/
theorem unoptWriteOk {asg : ChipAssignment babyBear}
    (halg : unopt.satisfiesAlgebraic asg) (hacc : unopt.satisfiesStateless apcRules asg)
    (i : Fin unopt.busInteractions.length)
    (hwit : unoptWitnesses.getD i.val .notSend = .external) :
    apcRules.payloadOk (unopt.msgAt asg i) := by
  haveI : Fact (1 < babyBear) := ⟨by decide⟩
  obtain ⟨ha0, ha1, ha2, ha3⟩ := unoptWriteIsByte halg hacc
  fin_cases i
  all_goals try exact absurd hwit (by decide)
  show openVmPayloadOk defaultBusMap ((1 : ℕ), [(1 : ZMod babyBear), asg ⟨"rd_ptr_0", some 2⟩,
    asg ⟨"a__0_0", some 19⟩, asg ⟨"a__1_0", some 20⟩, asg ⟨"a__2_0", some 21⟩,
    asg ⟨"a__3_0", some 22⟩, asg ⟨"from_state__timestamp_0", some 1⟩ + 2])
  exact (openVmPayloadOk_mem_iff _ _ _ _ _ _).mpr ⟨ha0, ha1, ha2, ha3⟩

/-- **The unoptimized APC already has a step layout.** One instruction is one step: there are no
    intermediate bridge states to cancel, so unlike `Keccak2105000.unopt` this needs no chaining
    modification, and `Circuit.legalGuest` holds at every stage of this APC's pipeline except the
    gated output. -/
theorem unopt_hasStepLayout {maxWindow : ℕ} (hw : 3 < maxWindow) :
    unopt.hasStepLayout apcRules maxWindow openVmTimestampBound :=
  hasStepLayout_of_checks (by norm_num) hw (fun _ halg => unoptPinRules_hold _ halg) unoptBaseLin
    (fun asg halg => bridgeCheck_sound unoptBridgeCheck (unoptPinRules_hold asg halg))
    unoptPlaceCheck unoptOrderCheck unoptFitsCheck unoptByteCheck
    (fun _ halg hacc => unoptLookbacks halg hacc)
    (fun _ halg hacc i hwit _ _ => unoptWriteOk halg hacc i hwit)

theorem unopt_legalGuest {maxWindow maxInteractions : ℕ} (hw : 3 < maxWindow)
    (hi : 20 ≤ maxInteractions) :
    unopt.legalGuest apcRules maxWindow openVmTimestampBound maxInteractions where
  sendOnly := unopt_legalMultiplicities.1
  polarity := unopt_legalMultiplicities.2
  stepLayout := unopt_hasStepLayout hw
  size := by simpa [unopt] using hi

end ApcOptimizer.OpenVM.SingleXor
