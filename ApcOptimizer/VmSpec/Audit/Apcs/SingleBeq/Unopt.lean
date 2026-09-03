import ApcOptimizer.VmSpec.Audit.Apcs.Common
import ApcOptimizer.VmSpec.Audit.Apcs.SingleBeq.Stages

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

/-! **The unoptimized stage: both multiplicity clauses, and no padding row.** Its multiplicities
    are opcode-flag sums rather than literals, so they need the constant-propagation tier. -/

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
    ¬ unopt.satisfiesAlgebraic (fun _ => 0) := by
  intro h
  have := h
    (.add (.mul (.const 2013265920)
        (.add (.add (.const 0) (.var ⟨"opcode_beq_flag_0", some 20⟩))
          (.var ⟨"opcode_bne_flag_0", some 21⟩)))
      (.const 1))
    (by simp [unopt])
  simp only [Expression.eval] at this
  exact absurd this (by decide)

end ApcOptimizer.OpenVM.SingleBeq
