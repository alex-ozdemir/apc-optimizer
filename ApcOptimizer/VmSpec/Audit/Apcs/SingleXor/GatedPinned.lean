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

/-- The same placement as the preceding stage — the gate changes multiplicities, not payloads. -/
def gatedRecipes : List (Recipe babyBear) :=
  [.fixed 0, .fixed 0, .fixed 0, .fixed 0,
   .lookback (-1) 131072 (payloadOf gatedPinned 12 0) (payloadOf gatedPinned 13 0), .fixed 0,
   .lookback 0 131072 (payloadOf gatedPinned 14 0) (payloadOf gatedPinned 15 0), .fixed 1,
   .lookback 1 131072 (payloadOf gatedPinned 16 0) (payloadOf gatedPinned 17 0), .fixed 2,
   .fixed 0, .fixed 3,
   .fixed 0, .fixed 0, .fixed 0, .fixed 0, .fixed 0, .fixed 0]

theorem gatedPlaceCheck :
    placeCheckAll layoutVars gatedPinRules apcRules.isStateful openVmTsPos baseF
      gatedPinned.busInteractions gatedRecipes = true := by decide

theorem gatedOrderCheck :
    memOrderCheck gatedPinRules openVmMemBusId openVmTimestampBound gatedPinned.busInteractions
      gatedRecipes = true := by decide

theorem gatedFitsCheck :
    (List.range gatedPinned.busInteractions.length).all
      (fun i => (gatedRecipes.getD i (.fixed 0)).fits openVmTimestampBound 3) = true := by decide

/-- Where each memory receive reaches back to. The range checks now carry `is_valid` rather than
    the literal `1`, which `accepts` on bus `3` does not look at. -/
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
  case «4» =>
    have haccL := acceptsAt hacc 12 (by decide) _ rfl rfl
      (show asg ⟨"is_valid", some 36⟩ ≠ 0 from hivne)
    have haccH := acceptsAt hacc 13 (by decide) _ rfl rfl
      (show asg ⟨"is_valid", some 36⟩ ≠ 0 from hivne)
    simp only [gatedPinned, gated, BusInteraction.eval] at haccL haccH
    exact lookback_of_gadget (vs := layoutVars) (rules := gatedPinRules)
      (baseE := baseE) (baseF := baseF) (k := (-1))
      (tsE := .var ⟨"reads_aux__0__base__prev_timestamp_0", some 6⟩)
      (loE := payloadOf gatedPinned 12 0) (hiE := payloadOf gatedPinned 13 0)
      (gatedPinRules_hold asg halg) gatedBaseLin (by decide) haccL haccH
  case «6» =>
    have haccL := acceptsAt hacc 14 (by decide) _ rfl rfl
      (show asg ⟨"is_valid", some 36⟩ ≠ 0 from hivne)
    have haccH := acceptsAt hacc 15 (by decide) _ rfl rfl
      (show asg ⟨"is_valid", some 36⟩ ≠ 0 from hivne)
    simp only [gatedPinned, gated, BusInteraction.eval] at haccL haccH
    exact lookback_of_gadget (vs := layoutVars) (rules := gatedPinRules)
      (baseE := baseE) (baseF := baseF) (k := 0)
      (tsE := .var ⟨"reads_aux__1__base__prev_timestamp_0", some 9⟩)
      (loE := payloadOf gatedPinned 14 0) (hiE := payloadOf gatedPinned 15 0)
      (gatedPinRules_hold asg halg) gatedBaseLin (by decide) haccL haccH
  case «8» =>
    have haccL := acceptsAt hacc 16 (by decide) _ rfl rfl
      (show asg ⟨"is_valid", some 36⟩ ≠ 0 from hivne)
    have haccH := acceptsAt hacc 17 (by decide) _ rfl rfl
      (show asg ⟨"is_valid", some 36⟩ ≠ 0 from hivne)
    simp only [gatedPinned, gated, BusInteraction.eval] at haccL haccH
    exact lookback_of_gadget (vs := layoutVars) (rules := gatedPinRules)
      (baseE := baseE) (baseF := baseF) (k := 1)
      (tsE := .var ⟨"writes_aux__base__prev_timestamp_0", some 12⟩)
      (loE := payloadOf gatedPinned 16 0) (hiE := payloadOf gatedPinned 17 0)
      (gatedPinRules_hold asg halg) gatedBaseLin (by decide) haccL haccH
  all_goals simp [gatedRecipes] at hrc

/-- The write at position `9` sends the `xor` the bitwise table computes, so its four limbs are
    bytes (`isByte_of_xorEq`). -/
theorem gatedWriteOk {asg : ChipAssignment babyBear}
    (halg : gatedPinned.satisfiesAlgebraic asg)
    (hacc : gatedPinned.satisfiesStateless apcRules asg)
    (i : Fin gatedPinned.busInteractions.length)
    (hwit : witnesses.getD i.val .notSend = .external) :
    apcRules.payloadOk (gatedPinned.msgAt asg i) := by
  haveI : Fact (1 < babyBear) := ⟨by decide⟩
  have hivne := gatedIsValid_ne_zero halg
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
  fin_cases i
  all_goals try exact absurd hwit (by decide)
  show openVmPayloadOk defaultBusMap ((1 : ℕ), [(1 : ZMod babyBear), 8,
    asg ⟨"a__0_0", some 19⟩, asg ⟨"a__1_0", some 20⟩, asg ⟨"a__2_0", some 21⟩,
    asg ⟨"a__3_0", some 22⟩, asg ⟨"from_state__timestamp_0", some 1⟩ + 2])
  exact (openVmPayloadOk_mem_iff _ _ _ _ _ _).mpr ⟨ha0, ha1, ha2, ha3⟩

/-- **A pinned gated APC has a step layout.** Identical in shape to `opt_hasStepLayout`: pinning
    `is_valid` is exactly what collapses this circuit back to the preceding stage's
    multiplicities. -/
theorem gatedPinned_hasStepLayout {maxWindow : ℕ} (hw : 3 < maxWindow) :
    gatedPinned.hasStepLayout apcRules maxWindow openVmTimestampBound :=
  hasStepLayout_of_checks (by norm_num) hw (fun _ halg => gatedPinRules_hold _ halg) gatedBaseLin
    (fun asg halg => bridgeCheck_sound gatedBridgeCheck (gatedPinRules_hold asg halg))
    gatedPlaceCheck gatedOrderCheck gatedFitsCheck gatedByteCheck
    (fun _ halg hacc => gatedLookbacks halg hacc)
    (fun _ halg hacc i hwit _ _ => gatedWriteOk halg hacc i hwit)

theorem gatedPinned_legalGuest {maxWindow maxInteractions : ℕ} (hw : 3 < maxWindow)
    (hi : 18 ≤ maxInteractions) :
    gatedPinned.legalGuest apcRules maxWindow openVmTimestampBound maxInteractions where
  sendOnly := gatedPinned_legalMultiplicities.1
  polarity := gatedPinned_legalMultiplicities.2
  stepLayout := gatedPinned_hasStepLayout hw
  size := by simpa [gatedPinned, gated] using hi

end ApcOptimizer.OpenVM.SingleXor
