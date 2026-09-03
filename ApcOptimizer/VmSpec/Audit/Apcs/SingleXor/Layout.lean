import ApcOptimizer.VmSpec.Audit.Apcs.Common
import ApcOptimizer.VmSpec.Audit.Apcs.SingleXor.Stages

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

/-! **Where this APC's step puts its stateful traffic.** The optimized stage and the pinned gated
    stage have the same bus interactions in the same order -- the gate only scales each
    multiplicity by `is_valid` -- so they place them identically and share everything here. -/

namespace ApcOptimizer.OpenVM.SingleXor

/-- Where each of the optimized APC's six stateful interactions sits, as an offset from the step's
    `from_state__timestamp_0`. Positions `0`–`3` and `12`–`17` are the bitwise and range lookups
    and are never read. The three receives look back by their own gadget's `n`; the two memory
    sends and the bridge sit at literal offsets. -/
def offsets (nr0 nr1 nw : ℕ) : List ℤ :=
  [0, 0, 0, 0, -1 - (nr0 : ℤ), 0, -(nr1 : ℤ), 1, 1 - (nw : ℤ), 2, 0, 3, 0, 0, 0, 0, 0, 0]

/-- The largest offset each position can hold: a receive's is `δ - n` for a lookback `n ≥ 0`, so
    `δ` bounds it; the three sends attain their entry exactly. The lookups are never placed, so
    their entries only have to sit below every send that follows them. -/
def offsetUb : List ℤ :=
  [-2, -2, -2, -2, -1, 0, 0, 1, 1, 2, 0, 3, 0, 0, 0, 0, 0, 0]

/-- Each of the three sends dominates every position before it. With `offsetUb` this is the whole
    of `StepLayout.ordered` for this circuit — a `decide` over positions. -/
theorem offsetUb_dominates :
    ∀ b ∈ [5, 7, 9, 11], ∀ k < b, offsetUb.getD k 0 < offsetUb.getD b 0 := by decide

/-- The variables the optimized APC's stateful payloads and lt gadgets mention: the step's base,
    each gadget's `prev_timestamp` and low decomposition limb, and the four data limbs of each of
    the two reads, the write, and the record the write displaces. -/
def layoutVars : List Variable :=
  [⟨"from_state__timestamp_0", some 1⟩,
   ⟨"reads_aux__0__base__prev_timestamp_0", some 6⟩,
   ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_0", some 7⟩,
   ⟨"reads_aux__1__base__prev_timestamp_0", some 9⟩,
   ⟨"reads_aux__1__base__timestamp_lt_aux__lower_decomp__0_0", some 10⟩,
   ⟨"writes_aux__base__prev_timestamp_0", some 12⟩,
   ⟨"writes_aux__base__timestamp_lt_aux__lower_decomp__0_0", some 13⟩,
   ⟨"writes_aux__prev_data__0_0", some 15⟩, ⟨"writes_aux__prev_data__1_0", some 16⟩,
   ⟨"writes_aux__prev_data__2_0", some 17⟩, ⟨"writes_aux__prev_data__3_0", some 18⟩,
   ⟨"a__0_0", some 19⟩, ⟨"a__1_0", some 20⟩, ⟨"a__2_0", some 21⟩, ⟨"a__3_0", some 22⟩,
   ⟨"b__0_0", some 23⟩, ⟨"b__1_0", some 24⟩, ⟨"b__2_0", some 25⟩, ⟨"b__3_0", some 26⟩,
   ⟨"c__0_0", some 27⟩, ⟨"c__1_0", some 28⟩, ⟨"c__2_0", some 29⟩, ⟨"c__3_0", some 30⟩]

/-- The step's base, as an expression and as a normal form. -/
def baseE : Expression babyBear := .var ⟨"from_state__timestamp_0", some 1⟩

def baseF : LinForm babyBear := LinForm.varF layoutVars ⟨"from_state__timestamp_0", some 1⟩

/-- Why each interaction is `payloadOk`, position by position: the three memory receives and the
    bridge receive are not sends; the two register reads are echoed straight back; the bridge send
    is not on the memory bus; the ten lookups are not stateful. Only the write at position `9` is
    left to the caller — its limbs are bytes because the bitwise table says so. -/
def witnesses : List ByteWitness :=
  [.notSend, .notSend, .notSend, .notSend, .notSend, .echo 4, .notSend, .echo 6, .notSend,
   .external, .notSend, .notMemory] ++ List.replicate 6 .notSend

end ApcOptimizer.OpenVM.SingleXor
