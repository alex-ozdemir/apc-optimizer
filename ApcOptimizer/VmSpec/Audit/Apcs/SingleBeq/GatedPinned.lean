import ApcOptimizer.VmSpec.Audit.Apcs.SingleBeq.Layout

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

/-! **The pipeline's output with `is_valid` pinned to `1`: `Circuit.legalGuest` in full.** Every
    clause the checkers prove for the preceding stage carries over -- the circuits differ only by
    the `is_valid` factor on each multiplicity and on the comparison constraint's right side, both
    of which fold away against the pin. -/

namespace ApcOptimizer.OpenVM.SingleBeq

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
    asg ⟨"is_valid", some 31⟩ = 1 :=
  gatedPinRules_hold asg halg (.var ⟨"is_valid", some 31⟩, 1) (by decide)

theorem gatedIsValid_ne_zero {asg : ChipAssignment babyBear}
    (halg : gatedPinned.satisfiesAlgebraic asg) :
    asg ⟨"is_valid", some 31⟩ ≠ 0 := by
  rw [gatedIsValid halg]; exact (show (1 : ZMod babyBear) ≠ 0 by decide)

/-- **The strengthened check passes, `is_valid` pinned**: every multiplicity is a literal times
    `is_valid`, legal only because the pin says `is_valid = 1`. -/
theorem gatedPinned_checkMultiplicitiesWith :
    checkMultiplicitiesWith apcRules.isStateful gatedPinned = true := by decide

theorem gatedPinned_legalMultiplicities :
    gatedPinned.statelessSendOnly apcRules ∧ gatedPinned.statefulPolarity apcRules :=
  checkMultiplicitiesWith_sound gatedPinned_checkMultiplicitiesWith rfl

/-- **The bridge half of the layout, by static analysis.** The outgoing `pc` is not a literal here
    but `4 - 2 * cmp_result_0`: `bridgeCheck` normalizes it like any other payload and separates
    the two endpoints at position `1`, where they differ by the constant `d = 2`. -/
theorem gatedBaseLin : Expression.toLin layoutVars gatedPinRules baseE = some baseF := by decide

theorem gatedBridgeCheck :
    bridgeCheck layoutVars gatedPinRules 0 gatedPinned 2 1 (.const 0) baseE
        (.add (.const 4) (.mul (.const 2013265920)
          (.mul (.const 2) (.var ⟨"cmp_result_0", some 18⟩))))
      = true := by decide

theorem gatedByteCheck :
    byteCheckAll layoutVars gatedPinRules gatedPinned.busInteractions witnesses = true := by decide

/-- The same placement as the preceding stage — the gate changes multiplicities, not payloads. -/
def gatedRecipes : List (Recipe babyBear) :=
  [.lookback (-1) 131072 (payloadOf gatedPinned 6 0) (payloadOf gatedPinned 7 0), .fixed 0,
   .lookback 0 131072 (payloadOf gatedPinned 8 0) (payloadOf gatedPinned 9 0), .fixed 1,
   .fixed 0, .fixed 2, .fixed 0, .fixed 0, .fixed 0, .fixed 0]

theorem gatedPlaceCheck :
    placeCheckAll layoutVars gatedPinRules apcRules.isStateful openVmTsPos baseF
      gatedPinned.busInteractions gatedRecipes = true := by decide

theorem gatedOrderCheck :
    memOrderCheck gatedPinRules openVmMemBusId openVmTimestampBound gatedPinned.busInteractions
      gatedRecipes = true := by decide

theorem gatedFitsCheck :
    (List.range gatedPinned.busInteractions.length).all
      (fun i => (gatedRecipes.getD i (.fixed 0)).fits openVmTimestampBound 2) = true := by decide

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
  case «0» =>
    have hacc6 := acceptsAt hacc 6 (by decide) _ rfl rfl
      (show asg ⟨"is_valid", some 31⟩ ≠ 0 from hivne)
    have hacc7 := acceptsAt hacc 7 (by decide) _ rfl rfl
      (show asg ⟨"is_valid", some 31⟩ ≠ 0 from hivne)
    simp only [gatedPinned, gated, BusInteraction.eval] at hacc6 hacc7
    exact lookback_of_gadget (vs := layoutVars) (rules := gatedPinRules)
      (baseE := baseE) (baseF := baseF) (k := (-1))
      (tsE := .var ⟨"reads_aux__0__base__prev_timestamp_0", some 4⟩)
      (loE := payloadOf gatedPinned 6 0) (hiE := payloadOf gatedPinned 7 0)
      (gatedPinRules_hold asg halg) gatedBaseLin (by decide) hacc6 hacc7
  case «2» =>
    have hacc8 := acceptsAt hacc 8 (by decide) _ rfl rfl
      (show asg ⟨"is_valid", some 31⟩ ≠ 0 from hivne)
    have hacc9 := acceptsAt hacc 9 (by decide) _ rfl rfl
      (show asg ⟨"is_valid", some 31⟩ ≠ 0 from hivne)
    simp only [gatedPinned, gated, BusInteraction.eval] at hacc8 hacc9
    exact lookback_of_gadget (vs := layoutVars) (rules := gatedPinRules)
      (baseE := baseE) (baseF := baseF) (k := 0)
      (tsE := .var ⟨"reads_aux__1__base__prev_timestamp_0", some 7⟩)
      (loE := payloadOf gatedPinned 8 0) (hiE := payloadOf gatedPinned 9 0)
      (gatedPinRules_hold asg halg) gatedBaseLin (by decide) hacc8 hacc9
  all_goals simp [gatedRecipes] at hrc

/-- **A pinned gated branch APC has a step layout.** Identical in shape to `opt_hasStepLayout`:
    pinning `is_valid` is exactly what collapses this circuit back to the preceding stage's
    multiplicities. -/
theorem gatedPinned_hasStepLayout {maxWindow : ℕ} (hw : 2 < maxWindow) :
    gatedPinned.hasStepLayout apcRules maxWindow openVmTimestampBound :=
  hasStepLayout_of_checks (by norm_num) hw (fun _ halg => gatedPinRules_hold _ halg) gatedBaseLin
    (fun asg halg => bridgeCheck_sound gatedBridgeCheck (gatedPinRules_hold asg halg))
    gatedPlaceCheck gatedOrderCheck gatedFitsCheck gatedByteCheck
    (fun _ halg hacc => gatedLookbacks halg hacc)
    (fun _ _ _ i hi _ _ => by fin_cases i <;> exact absurd hi (by decide))

theorem gatedPinned_legalGuest {maxWindow maxInteractions : ℕ} (hw : 2 < maxWindow)
    (hi : 10 ≤ maxInteractions) :
    gatedPinned.legalGuest apcRules maxWindow openVmTimestampBound maxInteractions where
  sendOnly := gatedPinned_legalMultiplicities.1
  polarity := gatedPinned_legalMultiplicities.2
  stepLayout := gatedPinned_hasStepLayout hw
  size := by simpa [gatedPinned, gated] using hi

end ApcOptimizer.OpenVM.SingleBeq
