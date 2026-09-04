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

/-- Where each interaction sits, as a `Recipe`: the two memory receives reach back by their own lt
    gadget's `n`, everything else sits at a literal tick of the step. Positions `6`–`9` are the
    range lookups, which no clause reads. -/
def recipes : List (Recipe babyBear) :=
  [.lookback (-1) 131072 (payloadOf opt 6 0) (payloadOf opt 7 0), .fixed 0,
   .lookback 0 131072 (payloadOf opt 8 0) (payloadOf opt 9 0), .fixed 1,
   .fixed 0, .fixed 2, .fixed 0, .fixed 0, .fixed 0, .fixed 0]

theorem optPlaceCheck :
    placeCheckAll layoutVars optPinRules apcRules.isStateful openVmTsPos baseF
      opt.busInteractions recipes = true := by decide

theorem optOrderCheck :
    memOrderCheck optPinRules openVmMemBusId openVmTimestampBound opt.busInteractions recipes
      = true := by decide

theorem optFitsCheck :
    (List.range opt.busInteractions.length).all
      (fun i => (recipes.getD i (.fixed 0)).fits openVmTimestampBound 2) = true := by decide

/-- The one thing the checkers cannot see: where each memory receive reaches back to. Both come
    off the lt gadget powdr's optimizer leaves behind (`lookback_of_gadget`). -/
theorem optLookbacks {asg : ChipAssignment babyBear}
    (halg : opt.satisfiesAlgebraic asg) (hacc : opt.satisfiesStateless apcRules asg)
    (i : Fin opt.busInteractions.length) (k : ℤ) (radix : ℕ) (loE hiE : Expression babyBear)
    (hrc : recipes.getD i.val (.fixed 0) = .lookback k radix loE hiE) :
    (recipes.getD i.val (.fixed 0)).back asg < openVmTimestampBound ∧
      apcRules.getTimestamp (opt.msgAt asg i)
        = baseE.eval asg + (((recipes.getD i.val (.fixed 0)).place asg : ℤ) : ZMod babyBear) := by
  fin_cases i
  case «0» =>
    exact lookback_of_gadget (vs := layoutVars) (rules := optPinRules)
      (baseE := baseE) (baseF := baseF) (k := (-1))
      (tsE := .var ⟨"reads_aux__0__base__prev_timestamp_0", some 4⟩)
      (loE := payloadOf opt 6 0) (hiE := payloadOf opt 7 0)
      (optPinRules_hold asg halg) optBaseLin (by decide)
      (acceptsAt hacc 6 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
      (acceptsAt hacc 7 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
  case «2» =>
    exact lookback_of_gadget (vs := layoutVars) (rules := optPinRules)
      (baseE := baseE) (baseF := baseF) (k := 0)
      (tsE := .var ⟨"reads_aux__1__base__prev_timestamp_0", some 7⟩)
      (loE := payloadOf opt 8 0) (hiE := payloadOf opt 9 0)
      (optPinRules_hold asg halg) optBaseLin (by decide)
      (acceptsAt hacc 8 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
      (acceptsAt hacc 9 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
  all_goals simp [recipes] at hrc

/-- **A real optimized branch APC has a step layout.** One arc — `(0, t) → (4 - 2·cmp, t + 2)` —
    and the six stateful interactions placed at `recipes`. Both memory sends echo the read that
    preceded them, so the byte invariant is entirely decidable: a branch computes nothing it
    sends, and `hasStepLayout_of_checks` is left with only the two gadget facts. -/
theorem opt_hasStepLayout {maxWindow : ℕ} (hw : 2 < maxWindow) :
    opt.hasStepLayout apcRules maxWindow openVmTimestampBound :=
  hasStepLayout_of_checks (by norm_num) hw (fun _ halg => optPinRules_hold _ halg) optBaseLin
    (fun asg halg => bridgeCheck_sound optBridgeCheck (optPinRules_hold asg halg))
    optPlaceCheck optOrderCheck optFitsCheck optByteCheck
    (fun _ halg hacc => optLookbacks halg hacc)
    (fun _ _ _ i hi _ _ => by fin_cases i <;> exact absurd hi (by decide))

theorem opt_legalGuest {maxWindow maxInteractions : ℕ} (hw : 2 < maxWindow)
    (hi : 10 ≤ maxInteractions) :
    opt.legalGuest apcRules maxWindow openVmTimestampBound maxInteractions where
  sendOnly := opt_legalMultiplicities.1
  polarity := opt_legalMultiplicities.2
  stepLayout := opt_hasStepLayout hw
  size := by simpa [opt] using hi

end ApcOptimizer.OpenVM.SingleBeq
