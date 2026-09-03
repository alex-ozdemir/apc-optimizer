import ApcOptimizer.VmSpec.Audit.Apcs.Common
import ApcOptimizer.VmSpec.Audit.Apcs.SingleBeq.Stages

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

/-! **Where this APC's step puts its stateful traffic.** The optimized stage and the pinned gated
    stage have the same bus interactions in the same order -- the gate only scales each
    multiplicity by `is_valid` -- so they place them identically and share everything here. -/

namespace ApcOptimizer.OpenVM.SingleBeq

/-- Where each of the optimized APC's six stateful interactions sits, as an offset from the step's
    `from_state__timestamp_0`. Positions `6`–`9` are the range lookups and are never read. The two
    memory receives look back by their own gadget's `n`; the two echoes and the bridge sit at
    literal offsets. -/
def offsets (nr0 nr1 : ℕ) : List ℤ :=
  [-1 - (nr0 : ℤ), 0, -(nr1 : ℤ), 1, 0, 2, 0, 0, 0, 0]

/-- The largest offset each position can hold: a receive's is `δ - n` for a lookback `n ≥ 0`, so
    `δ` bounds it; the two memory sends attain their entry exactly. Only the memory bus is read off
    this table (`StepLayout.memOrdered` orders memory sends among memory interactions), so the two
    bridge entries are never consulted. -/
def offsetUb : List ℤ := [-1, 0, 0, 1, 0, 2, 0, 0, 0, 0]

/-- Each of the two memory sends dominates every position before it — a `decide` over positions. -/
theorem offsetUb_dominates :
    ∀ b ∈ [1, 3], ∀ k < b, offsetUb.getD k 0 < offsetUb.getD b 0 := by decide

/-- The variables the optimized APC's stateful payloads and lt gadgets mention: the step's base,
    the comparison flag the outgoing `pc` depends on, each gadget's `prev_timestamp` and low
    decomposition limb, and the two reads' data limbs. -/
def layoutVars : List Variable :=
  [⟨"from_state__timestamp_0", some 1⟩, ⟨"cmp_result_0", some 18⟩,
   ⟨"reads_aux__0__base__prev_timestamp_0", some 4⟩,
   ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_0", some 5⟩,
   ⟨"reads_aux__1__base__prev_timestamp_0", some 7⟩,
   ⟨"reads_aux__1__base__timestamp_lt_aux__lower_decomp__0_0", some 8⟩,
   ⟨"a__0_0", some 10⟩, ⟨"a__1_0", some 11⟩, ⟨"a__2_0", some 12⟩, ⟨"a__3_0", some 13⟩,
   ⟨"b__0_0", some 14⟩, ⟨"b__1_0", some 15⟩, ⟨"b__2_0", some 16⟩, ⟨"b__3_0", some 17⟩]

/-- The step's base, as an expression and as a normal form. -/
def baseE : Expression babyBear := .var ⟨"from_state__timestamp_0", some 1⟩

def baseF : LinForm babyBear := LinForm.varF layoutVars ⟨"from_state__timestamp_0", some 1⟩

/-- Why each interaction is `payloadOk`, position by position: the two memory receives and the
    bridge receive are not sends; both memory sends echo the read that preceded them; the bridge
    send is not on the memory bus; the four lookups are not stateful. A branch writes nothing, so
    unlike `SingleXor` nothing is left to the caller. -/
def witnesses : List ByteWitness :=
  [.notSend, .echo 0, .notSend, .echo 2, .notSend, .notMemory,
   .notSend, .notSend, .notSend, .notSend]

end ApcOptimizer.OpenVM.SingleBeq
