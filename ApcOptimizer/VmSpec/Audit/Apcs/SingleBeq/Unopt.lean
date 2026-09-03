import ApcOptimizer.VmSpec.Audit.Apcs.SingleBeq.Layout

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

/-! **The unoptimized stage: `Circuit.legalGuest` in full.** Its multiplicities are opcode-flag
    sums rather than literals, so they need the constant-propagation tier, and powdr has not run
    its substitution pass yet, so each memory receive's offset comes from the *raw* lt gadget
    (`gadgetLookback_raw`) rather than from the range check the optimizer leaves behind.

    Unlike `Keccak2105000`, this stage already has a step layout: it is one instruction, so there
    are no intermediate bridge states to cancel and nothing to chain. It reuses `Layout.lean`'s
    `baseE` but needs its own variable list — the unoptimized circuit still carries the register
    pointers and the opcode flags the optimizer later folds away. -/

namespace ApcOptimizer.OpenVM.SingleBeq

/-- **The strengthened check passes on the unoptimized APC.** Every multiplicity is this
    instruction's two-flag opcode sum, which `checkMultiplicities` cannot see;
    `checkMultiplicitiesWith` reads `1 - (beq + bne) = 0` off the constraints and every one of the
    11 multiplicities folds against it. -/
theorem unopt_checkMultiplicitiesWith :
    checkMultiplicitiesWith apcRules.isStateful unopt = true := by decide

theorem unopt_legalMultiplicities :
    unopt.statelessSendOnly apcRules ∧ unopt.statefulPolarity apcRules :=
  checkMultiplicitiesWith_sound unopt_checkMultiplicitiesWith rfl

/-- **The unoptimized APC has no padding row either**: it pins the opcode-flag sum to `1`
    (`1 - (beq + bne) = 0`), which the all-zero assignment violates. -/
theorem unopt_zero_not_satisfiesAlgebraic :
    ¬ unopt.satisfiesAlgebraic (fun _ => 0) :=
  not_satisfiesAlgebraic_of_not_forall (by decide)

--------- The step layout ---------

/-- The pin `unopt`'s own constraints supply that `pinRuleOf` cannot use as a *variable* pin: its
    opcode-flag sum is `1` (constraint `11`, `1 - (beq + bne) = 0`). Constraints are addressed by
    index rather than restated. -/
theorem unoptFlagSum {asg : ChipAssignment babyBear} (halg : unopt.satisfiesAlgebraic asg) :
    asg ⟨"opcode_beq_flag_0", some 20⟩ + asg ⟨"opcode_bne_flag_0", some 21⟩ = 1 := by
  have h := halg _ (List.getElem_mem (show 11 < unopt.algebraicConstraints.length by decide))
  simp only [unopt, List.getElem_cons_succ, List.getElem_cons_zero, Expression.eval] at h
  rw [babyBear_negOne] at h
  linear_combination -h

/-- The variables the unoptimized APC's stateful payloads mention: the optimized stage's list plus
    the register pointers, the branch immediate and the `pc`, none of which powdr has folded away
    yet. -/
def unoptVars : List Variable :=
  layoutVars ++
  [⟨"from_state__pc_0", some 0⟩, ⟨"rs1_ptr_0", some 2⟩, ⟨"rs2_ptr_0", some 3⟩,
   ⟨"imm_0", some 19⟩]

def unoptBaseF : LinForm babyBear := LinForm.varF unoptVars ⟨"from_state__timestamp_0", some 1⟩

def unoptPinRules : List (PinRule babyBear) :=
  unopt.algebraicConstraints.filterMap pinRuleOf

theorem unoptPinRules_hold (asg : ChipAssignment babyBear)
    (halg : unopt.satisfiesAlgebraic asg) : ∀ q ∈ unoptPinRules, q.1.eval asg = q.2 := by
  intro q hq
  obtain ⟨con, hcon, hpin⟩ := List.mem_filterMap.mp hq
  exact pinRuleOf_eval (by rw [hpin]) (halg con hcon)

/-- **The bridge, by static analysis.** The unoptimized outgoing `pc` is
    `from_state__pc_0 + cmp * imm_0 + (1 - cmp) * 4`; the pins `from_state__pc_0 = 0` and
    `imm_0 = 2` collapse it to the same `4 - 2 * cmp` the optimized stage writes literally, which
    is exactly what normalizing to `LinForm` decides. -/
theorem unoptBaseLin : Expression.toLin unoptVars unoptPinRules baseE = some unoptBaseF := by
  decide

theorem unoptBridgeCheck :
    bridgeCheck unoptVars unoptPinRules 0 unopt 2 1 (.const 0) baseE
        (.add (.const 4) (.mul (.const 2013265920)
          (.mul (.const 2) (.var ⟨"cmp_result_0", some 18⟩))))
      = true := by decide

/-- Where each interaction sits, as a `Recipe`. powdr emits each lt gadget's range checks *before*
    the access they date and the bridge last, so the order is not the optimized stage's. -/
def unoptRecipes : List (Recipe babyBear) :=
  [.fixed 0, .fixed 0,
   .lookback (-1) 131072 (.var ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_0", some 5⟩)
     (.var ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__1_0", some 6⟩),
   .fixed 0, .fixed 0, .fixed 0,
   .lookback 0 131072 (.var ⟨"reads_aux__1__base__timestamp_lt_aux__lower_decomp__0_0", some 8⟩)
     (.var ⟨"reads_aux__1__base__timestamp_lt_aux__lower_decomp__1_0", some 9⟩),
   .fixed 1, .fixed 0, .fixed 0, .fixed 2]

theorem unoptPlaceCheck :
    placeCheckAll unoptVars unoptPinRules apcRules.isStateful openVmTsPos unoptBaseF
      unopt.busInteractions unoptRecipes = true := by decide

theorem unoptOrderCheck :
    memOrderCheck unoptPinRules openVmMemBusId openVmTimestampBound unopt.busInteractions
      unoptRecipes = true := by decide

theorem unoptFitsCheck :
    (List.range unopt.busInteractions.length).all
      (fun i => (unoptRecipes.getD i (.fixed 0)).fits openVmTimestampBound 2) = true := by decide

/-- Both memory sends echo the read that preceded them; the register-file lookup on bus `2` and
    the four range checks are not stateful, and the bridge send is not memory. -/
def unoptWitnesses : List ByteWitness :=
  [.notSend, .notSend, .notSend, .echo 2, .notSend, .notSend, .notSend, .echo 6,
   .notSend, .notSend, .notMemory]

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
  have hgate := unoptFlagSum halg
  fin_cases i
  case «2» =>
    have hcon := halg _ (List.getElem_mem (show 9 < unopt.algebraicConstraints.length by decide))
    simp only [unopt, List.getElem_cons_succ, List.getElem_cons_zero, Expression.eval] at hcon
    rw [babyBear_negOne] at hcon
    have heq := gadgetLookback_raw (δ := 0)
      (ts := asg ⟨"from_state__timestamp_0", some 1⟩)
      (prev := asg ⟨"reads_aux__0__base__prev_timestamp_0", some 4⟩)
      (lo := asg ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_0", some 5⟩) (hi := asg ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__1_0", some 6⟩)
      hgate (by linear_combination hcon)
    have hlo := accepts_congr_mult3 (m2 := 1)
      (acceptsAt hacc 0 (by decide) _ rfl rfl (sum2_eq1_ne_zero hgate))
    have hhi := accepts_congr_mult3 (m2 := 1)
      (acceptsAt hacc 1 (by decide) _ rfl rfl (sum2_eq1_ne_zero hgate))
    simp only [Expression.eval] at hlo hhi
    exact lookback_of_limbs (k := (-1)) (baseE := baseE)
      (tsE := .var ⟨"reads_aux__0__base__prev_timestamp_0", some 4⟩)
      (loE := .var ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_0", some 5⟩) (hiE := .var ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__1_0", some 6⟩)
      hlo hhi (by simp only [baseE, Expression.eval]; push_cast at heq ⊢; linear_combination heq)
  case «6» =>
    have hcon := halg _ (List.getElem_mem (show 10 < unopt.algebraicConstraints.length by decide))
    simp only [unopt, List.getElem_cons_succ, List.getElem_cons_zero, Expression.eval] at hcon
    rw [babyBear_negOne] at hcon
    have heq := gadgetLookback_raw (δ := 1)
      (ts := asg ⟨"from_state__timestamp_0", some 1⟩)
      (prev := asg ⟨"reads_aux__1__base__prev_timestamp_0", some 7⟩)
      (lo := asg ⟨"reads_aux__1__base__timestamp_lt_aux__lower_decomp__0_0", some 8⟩) (hi := asg ⟨"reads_aux__1__base__timestamp_lt_aux__lower_decomp__1_0", some 9⟩)
      hgate (by linear_combination hcon)
    have hlo := accepts_congr_mult3 (m2 := 1)
      (acceptsAt hacc 4 (by decide) _ rfl rfl (sum2_eq1_ne_zero hgate))
    have hhi := accepts_congr_mult3 (m2 := 1)
      (acceptsAt hacc 5 (by decide) _ rfl rfl (sum2_eq1_ne_zero hgate))
    simp only [Expression.eval] at hlo hhi
    exact lookback_of_limbs (k := 0) (baseE := baseE)
      (tsE := .var ⟨"reads_aux__1__base__prev_timestamp_0", some 7⟩)
      (loE := .var ⟨"reads_aux__1__base__timestamp_lt_aux__lower_decomp__0_0", some 8⟩) (hiE := .var ⟨"reads_aux__1__base__timestamp_lt_aux__lower_decomp__1_0", some 9⟩)
      hlo hhi (by simp only [baseE, Expression.eval]; push_cast at heq ⊢; linear_combination heq)
  all_goals simp [unoptRecipes] at hrc

/-- **The unoptimized APC already has a step layout.** One instruction is one step: there are no
    intermediate bridge states to cancel, so unlike `Keccak2105000.unopt` this needs no chaining
    modification, and `Circuit.legalGuest` holds at *every* stage of this APC's pipeline except the
    gated output. -/
theorem unopt_hasStepLayout {maxWindow : ℕ} (hw : 2 < maxWindow) :
    unopt.hasStepLayout apcRules maxWindow openVmTimestampBound :=
  hasStepLayout_of_checks (by norm_num) hw (fun _ halg => unoptPinRules_hold _ halg) unoptBaseLin
    (fun asg halg => bridgeCheck_sound unoptBridgeCheck (unoptPinRules_hold asg halg))
    unoptPlaceCheck unoptOrderCheck unoptFitsCheck unoptByteCheck
    (fun _ halg hacc => unoptLookbacks halg hacc)
    (fun _ _ _ i hi _ _ => by fin_cases i <;> exact absurd hi (by decide))

theorem unopt_legalGuest {maxWindow maxInteractions : ℕ} (hw : 2 < maxWindow)
    (hi : 11 ≤ maxInteractions) :
    unopt.legalGuest apcRules maxWindow openVmTimestampBound maxInteractions where
  sendOnly := unopt_legalMultiplicities.1
  polarity := unopt_legalMultiplicities.2
  stepLayout := unopt_hasStepLayout hw
  size := by simpa [unopt] using hi

end ApcOptimizer.OpenVM.SingleBeq
