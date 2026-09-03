import ApcOptimizer.VmSpec.Audit.Apcs.Common
import ApcOptimizer.VmSpec.Audit.Apcs.Keccak2105000.Stages

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

/-! **Stage `000_unopt`: both multiplicity clauses, and no padding row.** Its multiplicities are
    opcode-flag sums rather than literals, so they need the constant-propagation tier. Its four
    fused instructions' bridge states do not cancel until their timestamps are chained --
    `UnoptChained.lean` adds those three equations and gets a step layout. -/

namespace ApcOptimizer.OpenVM.Keccak2105000

/-- **The strengthened check passes on the unoptimized APC.** Its multiplicities are not literals —
    each is a sum of that instruction's opcode flags, or an operand's address space — so
    `checkMultiplicities` cannot see them. `checkMultiplicitiesWith` reads 27 pin rules off the
    constraints, among them `1 - (add + sub + xor + or + and) = 0` (the flag sum is `1`) and
    `rs2_as_i - 0 = 0` (that operand is an immediate), and every one of the 71 multiplicities folds
    against them. -/
theorem unopt_checkMultiplicitiesWith :
    checkMultiplicitiesWith apcRules.isStateful unopt = true := by decide

/-- **Both multiplicity clauses for the unoptimized APC**, again from the `Bool` rather than from a
    proof about this circuit. With `opt_legalMultiplicities` this says the two clauses
    survive powdr's optimizer on this block — the interesting direction for `PreservesLegality`. -/
theorem unopt_legalMultiplicities :
    unopt.statelessSendOnly apcRules ∧ unopt.statefulPolarity apcRules :=
  checkMultiplicitiesWith_sound unopt_checkMultiplicitiesWith rfl

/-- **The unoptimized APC has no padding row either**: it pins each fused instruction's opcode-flag
    sum to `1` (`1 - (add + sub + xor + or + and) = 0`, one per instruction). -/
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

end ApcOptimizer.OpenVM.Keccak2105000
