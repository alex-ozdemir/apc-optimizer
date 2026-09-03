import ApcOptimizer.VmSpec.Audit.Apcs.Common
import ApcOptimizer.VmSpec.Audit.Apcs.Keccak2105000.Stages

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

/-! **Where this APC's step puts its stateful traffic.** Stage `039` and the pinned stage `040`
    have the same bus interactions in the same order -- `040` only scales each multiplicity by
    `is_valid` -- so they place them identically, and `Opt.lean` and `GatedPinned.lean` share
    everything here. -/

namespace ApcOptimizer.OpenVM.Keccak2105000

/-- Where each of `opt`'s twelve stateful interactions sits, as an offset from the step's
    `from_state__timestamp_0`. Positions `7` and `13`–`22` are the stateless lookups and never read.
    The five receives look back by their own gadget's `n`; the six sends and the bridge receive sit
    at literal offsets. -/
def offsets (n0 nw0 nr1 nw1 nr3 : ℕ) : List ℤ :=
  [-1 - (n0 : ℤ), 0, 1 - nw0, 0, 2 - nr1, 4 - nw1, 5, 0, 6, 9, 9 - nr3, 10, 11]

/-- The largest offset each position can hold: a receive's is `δ - n` for a lookback `n ≥ 0`, so
    `δ` bounds it; the six sends attain their entry exactly. -/
def offsetUb : List ℤ := [-1, 0, 1, 0, 2, 4, 5, 0, 6, 9, 9, 10, 11]

/-- Each of the six sends dominates every position before it. With `offsetUb` this is the whole
    of `StepLayout.ordered` for this circuit — a `decide` over positions, which is what stating the
    layout in integer offsets rather than field timestamps buys. -/
theorem offsetUb_dominates :
    ∀ b ∈ [1, 6, 8, 9, 11, 12], ∀ k < b, offsetUb.getD k 0 < offsetUb.getD b 0 := by decide

/-- The variables the optimized APC's stateful payloads and lt gadgets mention: the step's base,
    the branch flag the outgoing `pc` depends on, and each gadget's `prev_timestamp` and low
    decomposition limb. -/
def layoutVars : List Variable :=
  [⟨"from_state__timestamp_0", some 1⟩, ⟨"cmp_result_3", some 126⟩,
   ⟨"reads_aux__0__base__prev_timestamp_0", some 6⟩,
   ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_0", some 7⟩,
   ⟨"writes_aux__base__prev_timestamp_0", some 12⟩,
   ⟨"writes_aux__base__timestamp_lt_aux__lower_decomp__0_0", some 13⟩,
   ⟨"reads_aux__0__base__prev_timestamp_1", some 42⟩,
   ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_1", some 43⟩,
   ⟨"writes_aux__base__prev_timestamp_1", some 48⟩,
   ⟨"writes_aux__base__timestamp_lt_aux__lower_decomp__0_1", some 49⟩,
   ⟨"reads_aux__1__base__prev_timestamp_3", some 115⟩,
   ⟨"reads_aux__1__base__timestamp_lt_aux__lower_decomp__0_3", some 116⟩,
   ⟨"a__0_0", some 19⟩, ⟨"a__1_0", some 20⟩, ⟨"a__2_0", some 21⟩, ⟨"a__3_0", some 22⟩,
   ⟨"a__0_1", some 55⟩, ⟨"a__1_1", some 56⟩, ⟨"a__2_1", some 57⟩, ⟨"a__3_1", some 58⟩,
   ⟨"a__0_2", some 91⟩]

/-- The step's base, as an expression and as a normal form. -/
def baseE : Expression babyBear := .var ⟨"from_state__timestamp_0", some 1⟩

def baseF : LinForm babyBear := LinForm.varF layoutVars ⟨"from_state__timestamp_0", some 1⟩

/-- Why each of `opt`'s interactions is `payloadOk`, position by position: six memory
    receives and the bridge receive are not sends; three memory sends echo the read that preceded
    them; one writes literal zeros; the bridge send is not on the memory bus; ten lookups are not
    stateful. Only the masked write at position `9` is left to the caller — it is a byte because
    the bitwise table says so, which is where a decidable check stops. -/
def witnesses : List ByteWitness :=
  [.notSend, .echo 0, .notSend, .notSend, .notSend, .notSend, .echo 4, .notSend,
   .echo 0, .external, .notSend, .limbs, .notMemory] ++ List.replicate 10 .notSend

end ApcOptimizer.OpenVM.Keccak2105000
