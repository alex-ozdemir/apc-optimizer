import ApcOptimizer.VmSpec.Audit.Apcs.Common
import ApcOptimizer.VmSpec.Audit.Apcs.SingleXor.Stages

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

/-! **The unoptimized stage: both multiplicity clauses, and no padding row.** Its multiplicities
    are opcode-flag sums rather than literals, so they need the constant-propagation tier. -/

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

end ApcOptimizer.OpenVM.SingleXor
