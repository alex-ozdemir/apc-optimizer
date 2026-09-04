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

/-- The same placement as the preceding stage — the gate changes multiplicities, not payloads. -/
def gatedRecipes : List (Recipe babyBear) :=
  [.lookback (-1) 131072 (payloadOf gatedPinned 13 0) (payloadOf gatedPinned 14 0), .fixed 0,
   .lookback 1 131072 (payloadOf gatedPinned 15 0) (payloadOf gatedPinned 16 0), .fixed 0,
   .lookback 2 131072 (payloadOf gatedPinned 17 0) (payloadOf gatedPinned 18 0),
   .lookback 4 131072 (payloadOf gatedPinned 19 0) (payloadOf gatedPinned 20 0),
   .fixed 5, .fixed 0, .fixed 6, .fixed 9,
   .lookback 9 131072 (payloadOf gatedPinned 21 0) (payloadOf gatedPinned 22 0),
   .fixed 10, .fixed 11] ++ List.replicate 10 (.fixed 0)

theorem gatedPlaceCheck :
    placeCheckAll layoutVars gatedPinRules apcRules.isStateful openVmTsPos baseF
      gatedPinned.busInteractions gatedRecipes = true := by decide

theorem gatedOrderCheck :
    memOrderCheck gatedPinRules openVmMemBusId openVmTimestampBound gatedPinned.busInteractions
      gatedRecipes = true := by decide

theorem gatedFitsCheck :
    (List.range gatedPinned.busInteractions.length).all
      (fun i => (gatedRecipes.getD i (.fixed 0)).fits openVmTimestampBound 11) = true := by decide

/-- Where each of the five memory receives reaches back to. The range checks now carry `is_valid`
    rather than the literal `1`, which `accepts` on bus `3` does not look at. -/
theorem gatedLookbacks {asg : ChipAssignment babyBear}
    (halg : gatedPinned.satisfiesAlgebraic asg)
    (hacc : gatedPinned.satisfiesStateless apcRules asg)
    (i : Fin gatedPinned.busInteractions.length) (k : ℤ) (radix : ℕ)
    (loE hiE : Expression babyBear)
    (hrc : gatedRecipes.getD i.val (.fixed 0) = .lookback k radix loE hiE) :
    (gatedRecipes.getD i.val (.fixed 0)).back asg < openVmTimestampBound ∧
      apcRules.getTimestamp (gatedPinned.msgAt asg i)
        = baseE.eval asg
          + (((gatedRecipes.getD i.val (.fixed 0)).place asg : ℤ) : ZMod babyBear) := by
  have hivne := gatedIsValid_ne_zero halg
  fin_cases i
  case «0» =>
    have haccL := acceptsAt hacc 13 (by decide) _ rfl rfl
      (show asg ⟨"is_valid", some 137⟩ ≠ 0 from hivne)
    have haccH := acceptsAt hacc 14 (by decide) _ rfl rfl
      (show asg ⟨"is_valid", some 137⟩ ≠ 0 from hivne)
    simp only [gatedPinned, gated, BusInteraction.eval] at haccL haccH
    exact lookback_of_gadget (vs := layoutVars) (rules := gatedPinRules)
      (baseE := baseE) (baseF := baseF) (k := (-1))
      (tsE := .var ⟨"reads_aux__0__base__prev_timestamp_0", some 6⟩)
      (loE := payloadOf gatedPinned 13 0) (hiE := payloadOf gatedPinned 14 0)
      (gatedPinRules_hold asg halg) gatedBaseLin (by decide) haccL haccH
  case «2» =>
    have haccL := acceptsAt hacc 15 (by decide) _ rfl rfl
      (show asg ⟨"is_valid", some 137⟩ ≠ 0 from hivne)
    have haccH := acceptsAt hacc 16 (by decide) _ rfl rfl
      (show asg ⟨"is_valid", some 137⟩ ≠ 0 from hivne)
    simp only [gatedPinned, gated, BusInteraction.eval] at haccL haccH
    exact lookback_of_gadget (vs := layoutVars) (rules := gatedPinRules)
      (baseE := baseE) (baseF := baseF) (k := 1)
      (tsE := .var ⟨"writes_aux__base__prev_timestamp_0", some 12⟩)
      (loE := payloadOf gatedPinned 15 0) (hiE := payloadOf gatedPinned 16 0)
      (gatedPinRules_hold asg halg) gatedBaseLin (by decide) haccL haccH
  case «4» =>
    have haccL := acceptsAt hacc 17 (by decide) _ rfl rfl
      (show asg ⟨"is_valid", some 137⟩ ≠ 0 from hivne)
    have haccH := acceptsAt hacc 18 (by decide) _ rfl rfl
      (show asg ⟨"is_valid", some 137⟩ ≠ 0 from hivne)
    simp only [gatedPinned, gated, BusInteraction.eval] at haccL haccH
    exact lookback_of_gadget (vs := layoutVars) (rules := gatedPinRules)
      (baseE := baseE) (baseF := baseF) (k := 2)
      (tsE := .var ⟨"reads_aux__0__base__prev_timestamp_1", some 42⟩)
      (loE := payloadOf gatedPinned 17 0) (hiE := payloadOf gatedPinned 18 0)
      (gatedPinRules_hold asg halg) gatedBaseLin (by decide) haccL haccH
  case «5» =>
    have haccL := acceptsAt hacc 19 (by decide) _ rfl rfl
      (show asg ⟨"is_valid", some 137⟩ ≠ 0 from hivne)
    have haccH := acceptsAt hacc 20 (by decide) _ rfl rfl
      (show asg ⟨"is_valid", some 137⟩ ≠ 0 from hivne)
    simp only [gatedPinned, gated, BusInteraction.eval] at haccL haccH
    exact lookback_of_gadget (vs := layoutVars) (rules := gatedPinRules)
      (baseE := baseE) (baseF := baseF) (k := 4)
      (tsE := .var ⟨"writes_aux__base__prev_timestamp_1", some 48⟩)
      (loE := payloadOf gatedPinned 19 0) (hiE := payloadOf gatedPinned 20 0)
      (gatedPinRules_hold asg halg) gatedBaseLin (by decide) haccL haccH
  case «10» =>
    have haccL := acceptsAt hacc 21 (by decide) _ rfl rfl
      (show asg ⟨"is_valid", some 137⟩ ≠ 0 from hivne)
    have haccH := acceptsAt hacc 22 (by decide) _ rfl rfl
      (show asg ⟨"is_valid", some 137⟩ ≠ 0 from hivne)
    simp only [gatedPinned, gated, BusInteraction.eval] at haccL haccH
    exact lookback_of_gadget (vs := layoutVars) (rules := gatedPinRules)
      (baseE := baseE) (baseF := baseF) (k := 9)
      (tsE := .var ⟨"reads_aux__1__base__prev_timestamp_3", some 115⟩)
      (loE := payloadOf gatedPinned 21 0) (hiE := payloadOf gatedPinned 22 0)
      (gatedPinRules_hold asg halg) gatedBaseLin (by decide) haccL haccH
  all_goals simp [gatedRecipes] at hrc

/-- The masked write at position `9`, as at the preceding stage (`isByte_of_xorThree`). -/
theorem gatedWriteOk {asg : ChipAssignment babyBear}
    (halg : gatedPinned.satisfiesAlgebraic asg)
    (hacc : gatedPinned.satisfiesStateless apcRules asg)
    (i : Fin gatedPinned.busInteractions.length)
    (hwit : witnesses.getD i.val .notSend = .external) :
    apcRules.payloadOk (gatedPinned.msgAt asg i) := by
  haveI : Fact (1 < babyBear) := ⟨by decide⟩
  have hiv := gatedIsValid halg
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
  fin_cases i
  all_goals try exact absurd hwit (by decide)
  show openVmPayloadOk defaultBusMap ((1 : ℕ), [(1 : ZMod babyBear), 44,
    asg ⟨"a__0_2", some 91⟩, 0, 0, 0, asg ⟨"from_state__timestamp_0", some 1⟩ + 9])
  exact (openVmPayloadOk_mem_iff _ _ _ _ _ _).mpr ⟨ha02, isByte_zero, isByte_zero, isByte_zero⟩

/-- **A pinned gated APC has a step layout.** Identical in shape to `opt_hasStepLayout` — same
    recipes, same gadgets, same byte witnesses — since pinning `is_valid` is exactly what collapses
    `gatedPinned` back to `opt`'s multiplicities. -/
theorem gatedPinned_hasStepLayout {maxWindow : ℕ} (hw : 11 < maxWindow) :
    gatedPinned.hasStepLayout apcRules maxWindow openVmTimestampBound :=
  hasStepLayout_of_checks (by norm_num) hw (fun _ halg => gatedPinRules_hold _ halg) gatedBaseLin
    (fun asg halg => bridgeCheck_sound gatedBridgeCheck (gatedPinRules_hold asg halg))
    gatedPlaceCheck gatedOrderCheck gatedFitsCheck gatedByteCheck
    (fun _ halg hacc => gatedLookbacks halg hacc)
    (fun _ halg hacc i hwit _ _ => gatedWriteOk halg hacc i hwit)

theorem gatedPinned_legalGuest {maxWindow maxInteractions : ℕ} (hw : 11 < maxWindow)
    (hi : 23 ≤ maxInteractions) :
    gatedPinned.legalGuest apcRules maxWindow openVmTimestampBound maxInteractions where
  sendOnly := gatedPinned_legalMultiplicities.1
  polarity := gatedPinned_legalMultiplicities.2
  stepLayout := gatedPinned_hasStepLayout hw
  size := by simpa [gatedPinned, gated] using hi

end ApcOptimizer.OpenVM.Keccak2105000
