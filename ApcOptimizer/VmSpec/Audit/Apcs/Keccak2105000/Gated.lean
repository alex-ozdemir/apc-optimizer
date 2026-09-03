import ApcOptimizer.VmSpec.Audit.Apcs.Common
import ApcOptimizer.VmSpec.Audit.Apcs.Keccak2105000.Stages

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

/-! **Stage `040`, the pipeline's output: out of the checker's reach, and no step layout.** The
    last pass mints a fresh `is_valid` column and scales every multiplicity by it, which both
    defeats the constant-folding tier and admits an all-zero padding row. `GatedPinned.lean` pins
    `is_valid` and recovers everything. -/

namespace ApcOptimizer.OpenVM.Keccak2105000

/-- **The checker does not reach the pipeline's final output.** `gated`'s multiplicities
    are `±is_valid`, and `Expression.foldConst` returns `none` on a bare variable, so the check
    fails on a circuit whose clauses are in fact true — reachable only through the booleanity
    constraint `is_valid * (is_valid - 1) = 0`. That is precisely the second tier
    `Audit/SendOnlyPolarity.lean`'s docstring names and does not attempt, and powdr's last pass is
    what moves the circuit out of the first tier's reach. -/
theorem gated_checkMultiplicities_fails :
    checkMultiplicities apcRules.isStateful gated = false := by decide

/-- **The padding row.** Every column zero satisfies the gated APC's four constraints: they are
    `cmp * (cmp - 1)`, `(1 - cmp) * a`, `free * a - cmp`, and `is_valid * (is_valid - 1)`, each of
    which vanishes at `0`. Nothing pins `is_valid` to `1`. -/
theorem gated_satisfiesAlgebraic_zero :
    gated.satisfiesAlgebraic (fun _ => 0) := by
  intro c hc
  simp only [gated, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> simp [Expression.eval]

/-- On that row the gated APC is silent: every multiplicity is `±is_valid`, which is `0`. -/
theorem gated_mults_zero_on_padding :
    ∀ bi ∈ gated.busInteractions,
      (bi.eval (fun _ => 0)).multiplicity = 0 := by
  intro bi hbi
  simp only [gated, List.mem_cons, List.not_mem_nil, or_false] at hbi
  rcases hbi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [BusInteraction.eval, Expression.eval]

/-- **Finding G1, still open: the padding row has no step layout.** powdr's optimizer replaces each
    fused instruction's pinned opcode-flag sum with one fresh `is_valid` column carrying only
    `is_valid * (is_valid - 1) = 0`, so the all-zero assignment is algebraically satisfying and the
    circuit nets `0` on every message of every bus. `StepLayout` asks for a bridge receive netting
    `-1` on *every* algebraically-satisfying assignment, and this row cannot supply one.

    The unoptimized APC has no such row (`unopt_zero_not_satisfiesAlgebraic`) — same
    block, same semantics, so **the optimization is what breaks legality**, which makes this the
    legality-preservation gap of `agent-docs/vm-spec.md` observed in the wild rather than
    constructed. Closing it is a change to the *circuit* (pin `is_valid`), not to the clause. -/
theorem gated_not_hasStepLayout {maxWindow maxLookback : ℕ} :
    ¬ gated.hasStepLayout apcRules maxWindow maxLookback := by
  intro h
  obtain ⟨L⟩ := h (fun _ => 0) gated_satisfiesAlgebraic_zero
    (fun bi hbi _ hmult => absurd (gated_mults_zero_on_padding bi hbi) hmult)
  exact babyBear_negOne_ne_zero
    (L.bridgeRecv.symm.trans (allEffects_eq_zero_of_mults_zero gated_mults_zero_on_padding _))

end ApcOptimizer.OpenVM.Keccak2105000
