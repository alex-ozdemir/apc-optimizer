import ApcOptimizer.VmSpec.Audit.Apcs.Common
import ApcOptimizer.VmSpec.Audit.Apcs.SingleXor.Stages

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

/-! **The pipeline's output: out of the checker's reach, and no step layout.** The last pass mints
    a fresh `is_valid` column and scales every multiplicity by it, which both defeats the
    constant-folding tier and admits an all-zero padding row. `GatedPinned.lean` pins `is_valid`
    and recovers everything. -/

namespace ApcOptimizer.OpenVM.SingleXor

/-- **The checker does not reach the pipeline's final output.** `gated`'s multiplicities are
    `±is_valid`, and `Expression.foldConst` returns `none` on a bare variable, so the check fails
    on a circuit whose clauses are in fact true — reachable only through the booleanity constraint
    `is_valid * (is_valid - 1) = 0`, the second tier `Audit/SendOnlyPolarity.lean` names and does
    not attempt. -/
theorem gated_checkMultiplicities_fails :
    checkMultiplicities apcRules.isStateful gated = false := by decide

/-- **The padding row.** Every column zero satisfies this stage's single constraint,
    `is_valid * (is_valid - 1)`. Nothing pins `is_valid` to `1`. -/
theorem gated_satisfiesAlgebraic_zero :
    gated.satisfiesAlgebraic (fun _ => 0) := by
  intro c hc
  simp only [gated, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp [Expression.eval]

/-- On that row the gated APC is silent: every multiplicity is `±is_valid`, which is `0`. -/
theorem gated_mults_zero_on_padding :
    ∀ bi ∈ gated.busInteractions, (bi.eval (fun _ => 0)).multiplicity = 0 := by
  intro bi hbi
  simp only [gated, List.mem_cons, List.not_mem_nil, or_false] at hbi
  rcases hbi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [BusInteraction.eval, Expression.eval]

/-- **The padding row has no step layout**, exactly as for the fused APC
    (`Keccak2105000.gated_not_hasStepLayout`): the all-zero assignment is algebraically satisfying
    and nets `0` on every message of every bus, where `StepLayout` asks for a bridge receive
    netting `-1` on *every* algebraically-satisfying assignment.

    The unoptimized APC has no such row (`unopt_zero_not_satisfiesAlgebraic`) — same instruction,
    same semantics, so **the optimization is what breaks legality**. That this reproduces on a
    single-instruction APC as well as on a fused block says the gap is powdr's gating pass, not
    anything about fusion. -/
theorem gated_not_hasStepLayout {maxWindow maxLookback : ℕ} :
    ¬ gated.hasStepLayout apcRules maxWindow maxLookback := by
  intro h
  obtain ⟨L⟩ := h (fun _ => 0) gated_satisfiesAlgebraic_zero
    (fun bi hbi _ hmult => absurd (gated_mults_zero_on_padding bi hbi) hmult)
  exact babyBear_negOne_ne_zero
    (L.bridgeRecv.symm.trans (allEffects_eq_zero_of_mults_zero gated_mults_zero_on_padding _))

end ApcOptimizer.OpenVM.SingleXor
