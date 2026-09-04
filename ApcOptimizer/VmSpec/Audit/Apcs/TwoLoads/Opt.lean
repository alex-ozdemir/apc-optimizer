import ApcOptimizer.VmSpec.Audit.Apcs.TwoLoads.Layout

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

/-! **How far `Circuit.legalGuest` gets on the optimized two-`loadb` block, and where it stops.**

    Both multiplicity clauses hold, and so does every part of the step layout that does not have to
    read a main-memory *address*. `hasStepLayout` itself is out of reach, and for a reason that is a
    property of the checkers rather than of the block: a **byte** load's pointer is quadratic in its
    own `flags__*` selector, and `Audit/LinForm.lean` normalizes to a *linear* form, so
    `payloadLin` returns `none` on the two main-memory accesses (`optMemPayload_notLinear`) and both
    `placeCheckAll` and `byteCheckAll` reject.

    This is the same kind of gap as the gated stage's padding row: a real APC that the audit's
    decidable layer cannot see, recorded rather than papered over. Closing it means giving `LinForm`
    a way to carry a non-linear subterm as an opaque atom -- a change to a soundness-critical
    checker, not to this file. `LoadBranch`, a *word* load, has the linear pointer
    (`mem_ptr_limbs__0_0 + 65536 * mem_ptr_limbs__1_0`) the checkers do handle. -/

namespace ApcOptimizer.OpenVM.TwoLoads

/-- **The static multiplicity check passes.** Every multiplicity this stage carries is a field
    literal, so `Expression.foldConst` resolves all 30 of them. -/
theorem opt_checkMultiplicities :
    checkMultiplicities apcRules.isStateful opt = true := by decide

theorem opt_legalMultiplicities :
    opt.statelessSendOnly apcRules ∧ opt.statefulPolarity apcRules :=
  checkMultiplicities_sound opt_checkMultiplicities rfl

/-- The pin rules this stage's own constraints supply. -/
def optPinRules : List (PinRule babyBear) :=
  opt.algebraicConstraints.filterMap pinRuleOf

theorem optPinRules_hold (asg : ChipAssignment babyBear)
    (halg : opt.satisfiesAlgebraic asg) : ∀ q ∈ optPinRules, q.1.eval asg = q.2 := by
  intro q hq
  obtain ⟨con, hcon, hpin⟩ := List.mem_filterMap.mp hq
  exact pinRuleOf_eval (by rw [hpin]) (halg con hcon)

theorem optBaseLin : Expression.toLin layoutVars optPinRules baseE = some baseF := by decide

/-- **The bridge half of the layout still goes through.** The block spans `d = 8` ticks, from
    `5164104` to `5164116 + 24 * cmp_result_2` — the bridge payload is linear, so the checker
    reaches it. -/
theorem optBridgeCheck :
    bridgeCheck layoutVars optPinRules 0 opt 8 1 (.const 5164104) baseE (payloadOf opt 13 0)
      = true := by decide

/-- Where each interaction sits: the six memory receives reach back by their own lt gadget's `n`,
    every send at a literal tick of the step. -/
def recipes : List (Recipe babyBear) :=
  [.lookback (-1) 131072 (payloadOf opt 14 0) (payloadOf opt 15 0), .fixed 0,
   .lookback 0 131072 (payloadOf opt 17 0) (payloadOf opt 18 0), .fixed 1,
   .lookback 1 131072 (payloadOf opt 19 0) (payloadOf opt 20 0), .fixed 0,
   .lookback 2 131072 (payloadOf opt 21 0) (payloadOf opt 22 0), .fixed 3,
   .lookback 3 131072 (payloadOf opt 24 0) (payloadOf opt 25 0), .fixed 4,
   .lookback 4 131072 (payloadOf opt 26 0) (payloadOf opt 27 0), .fixed 6,
   .fixed 7, .fixed 8,
   .fixed 0, .fixed 0, .fixed 0, .fixed 0, .fixed 0, .fixed 0, .fixed 0, .fixed 0,
   .fixed 0, .fixed 0, .fixed 0, .fixed 0, .fixed 0, .fixed 0, .fixed 0, .fixed 0]

/-- **The memory ordering and the window both check out.** Neither reads an address. -/
theorem optOrderCheck :
    memOrderCheck optPinRules openVmMemBusId openVmTimestampBound opt.busInteractions recipes
      = true := by decide

theorem optFitsCheck :
    (List.range opt.busInteractions.length).all
      (fun i => (recipes.getD i (.fixed 0)).fits openVmTimestampBound 8) = true := by decide

--------- Where the decidable layer stops ---------

/-- **The root cause.** Interaction `2` is the first load's main-memory access, whose pointer is
    `flags__*_0`-quadratic; `Expression.toLin` is linear-only, so the whole payload fails to
    normalize. Interaction `0`, a register access at a literal pointer, normalizes fine. -/
theorem optMemPayload_notLinear :
    payloadLin layoutVars optPinRules
      (opt.busInteractions.get ⟨2, by decide⟩).payload = none := by decide

theorem optRegPayload_isLinear :
    (payloadLin layoutVars optPinRules
      (opt.busInteractions.get ⟨0, by decide⟩).payload).isSome = true := by decide

/-- **So the placement check rejects** — at exactly the four address-space-`2` interactions
    (`2`, `3`, `8`, `9`), and nowhere else. -/
theorem optPlaceCheck_fails :
    placeCheckAll layoutVars optPinRules apcRules.isStateful openVmTsPos baseF
      opt.busInteractions recipes = false := by decide

/-- **And so does the byte check**, at the two main-memory sends (`3`, `9`): an `.echo` witness
    compares normalized payloads, and these do not normalize. -/
theorem optByteCheck_fails :
    byteCheckAll layoutVars optPinRules opt.busInteractions witnesses = false := by decide

end ApcOptimizer.OpenVM.TwoLoads
