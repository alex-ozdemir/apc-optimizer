import ApcOptimizer.VmSpec.Audit.Apcs.SingleXor.Unopt
import ApcOptimizer.VmSpec.Audit.Apcs.SingleXor.Opt
import ApcOptimizer.VmSpec.Audit.Apcs.SingleXor.Gated
import ApcOptimizer.VmSpec.Audit.Apcs.SingleXor.GatedPinned
import ApcOptimizer.VmSpec.Audit.Apcs.SingleBeq.Unopt
import ApcOptimizer.VmSpec.Audit.Apcs.SingleBeq.Opt
import ApcOptimizer.VmSpec.Audit.Apcs.SingleBeq.Gated
import ApcOptimizer.VmSpec.Audit.Apcs.SingleBeq.GatedPinned
import ApcOptimizer.VmSpec.Audit.Apcs.Keccak2105000.Unopt
import ApcOptimizer.VmSpec.Audit.Apcs.Keccak2105000.UnoptChained
import ApcOptimizer.VmSpec.Audit.Apcs.Keccak2105000.Opt
import ApcOptimizer.VmSpec.Audit.Apcs.Keccak2105000.Gated
import ApcOptimizer.VmSpec.Audit.Apcs.Keccak2105000.GatedPinned
import ApcOptimizer.VmSpec.Audit.Apcs.AndBranch.Opt
import ApcOptimizer.VmSpec.Audit.Apcs.LoadBranch.Opt
import ApcOptimizer.VmSpec.Audit.Apcs.TwoLoads.Opt

/-! **`Circuit.legalGuest` measured against real APCs.**

    `Audit/OpenVmLegalAudit.lean` checks the legality clauses against hand-written chips in the
    shape a real OpenVM AIR has. `Audit/Apcs/` does the same against circuits nobody wrote by
    hand: whole APCs as powdr emits them, each at several points of powdr's own optimizer
    pipeline, so a difference between two results is a statement about the optimizer, not about
    the block.

    This file imports every per-APC audit and states nothing itself; it is the index.

    ## Layout

    `Apcs/Common.lean` holds what no APC owns: the bus rules they are all measured against, the
    BabyBear facts powdr's encoding forces, and the OpenVM gadgets a `StepLayout` is read off.
    Then one directory per APC, in its own namespace, with the same member names throughout:

    * `Stages.lean` — the circuit at each point of the pipeline (`unopt`, `opt`, `gated`), emitted
      by `Scripts/emit-apc-lean.py`, plus the modifications a proof needs (`gatedPinned`, and for a
      fused block `unoptChained`), each defined by appending to a stage rather than restating it.
    * `Layout.lean` — the placement data `opt` and `gatedPinned` share (they have the same
      interactions in the same order).
    * one file per stage — `Unopt.lean`, `Opt.lean`, `Gated.lean`, `GatedPinned.lean`,
      `UnoptChained.lean` — carrying that stage's proofs. Split because they are slow: each stage's
      `hasStepLayout` is a large `decide`, and this way they compile in parallel and one edit does
      not rebuild the others.

    ## The APCs

    | | what it is | why it is here |
    | --- | --- | --- |
    | `Keccak2105000` | a keccak basic block, four fused instructions | the real thing: a big block, a branch at the end, a masked write |
    | `SingleXor` | `[x8] = [x7] ^ [x5]` | one instruction: a fresh write whose byte-ness comes from the bitwise table |
    | `SingleBeq` | `if [x8] == [x5] jump +2` | a *branching* step: `pc` out is `4 - 2·cmp`, and nothing is written |
    | `AndBranch` | `andi` then branch-if-nonzero, two fused instructions | a masked write, whose byte-ness the bitwise table gives *by lookup* (`isByte_of_andEq`) rather than by constraint |
    | `LoadBranch` | `loadw` then `beq`, two fused instructions | *main memory*: an access in address space `2`, at a pointer the circuit computes, echoed on into a register |
    | `TwoLoads` | two `loadb`s then a branch, three fused instructions | the first circuit here the decidable layer *cannot* reach: a byte load's pointer is quadratic in its own selector flags, and `LinForm` is linear-only |

    The last two come straight out of the shipped benchmark corpus
    (`Benchmarks/OpenVM/openvm-eth/apc_056_pc0x200bd4` and `apc_072_pc0x391014`), which ships two
    stages per APC: the unoptimized block and the pre-gate `.powdr_opt`. The latter is the `opt`
    column below, the stage at which legality is actually claimed, and the only one they carry —
    the `unopt` and `gated` columns' story is about powdr's passes, and the three APCs above
    already tell it at both ends.

    ## What is checked, per stage

    | | `unopt` (`000`) | `opt` (last `trivial_simp`) | `gated` (final) |
    | --- | --- | --- | --- |
    | `statelessSendOnly` | **true** | **true** | true, out of checker reach |
    | `statefulPolarity` | **true** | **true** | true, out of checker reach |
    | `hasStepLayout` | fused: **false**; single: **true** | **true** | **false**, padding row |

    `AndBranch`, `LoadBranch` and `TwoLoads` fill the `opt` column only; the other three fill all
    of it. `TwoLoads` fills it only in part, and deliberately: it reaches `statelessSendOnly`,
    `statefulPolarity`, the bridge, the memory ordering and the window, then stops at
    `hasStepLayout` because `payloadLin` cannot normalize a *quadratic* memory address
    (`optMemPayload_notLinear`). Both failures are recorded as `decide`d theorems
    (`optPlaceCheck_fails`, `optByteCheck_fails`) naming exactly the four interactions responsible,
    in the same spirit as `gated_not_hasStepLayout`.

    **Why `TwoLoads` is audited at all.** Its two main-memory accesses sit at independently
    computed pointers, so they *may alias* — and when they do, `Circuit.admissible`
    (`MemoryBus.lean`) demands the second access's previous record equal the first's new one.
    Every other APC here is free of that obligation: their memory addresses are literal register
    numbers, or (in `LoadBranch`) a single main-memory access with nothing to alias with, so
    `admissibleMemoryBus` is vacuous on them. That makes the first four *unrepresentative* of the
    corpus for anything that rests on `admissible` — VM-level completeness above all — where
    79 of the 100 `openvm-eth` APCs do carry a genuine aliasing pair. `TwoLoads` is the smallest
    circuit in the shipped corpus with the shape; that the checkers cannot yet reach it is the
    finding, not a reason to leave the shape unaudited.

    The two falsities split cleanly. The gated stage's padding row reproduces on a
    single-instruction APC exactly as on a fused block, so *that* gap is powdr's gating pass, not
    fusion. The unoptimized stage's failure is the opposite: it is entirely about fusion — a
    single-instruction `unopt` is already one step, has nothing to chain, and reaches `legalGuest`
    as it stands (`SingleXor.unopt_legalGuest`, `SingleBeq.unopt_legalGuest`).

    Every "true" is discharged by `Audit/SendOnlyPolarity.lean`'s decidable checker and its
    soundness theorem — a `Bool` and a `rfl`, with no case analysis over the circuit written by
    hand. An optimized APC needs only the constant-folding tier; an unoptimized one needs the
    constant-propagation tier, since its multiplicities are opcode-flag sums that are legal only
    because a constraint pins them.

    **Why the last `trivial_simp` stage and not the pipeline's output.** The last pass introduces a
    fresh `is_valid` column and multiplies every multiplicity by it, which puts the circuit out of
    the multiplicity checker's reach (`gated_checkMultiplicities_fails`): `Expression.foldConst`
    returns `none` on a bare variable, and the booleanity constraint `is_valid * (is_valid - 1) = 0`
    is not linear, so no pin rule comes off it either. The preceding stage is that same circuit one
    pass earlier — identical bus interactions and constraints, multiplicities the literal `±1`.

    The padding row that gate introduces also makes the final stage fail `hasStepLayout` outright
    (`gated_not_hasStepLayout`): the all-zero assignment is algebraically satisfying and nets `0`
    on the bridge, where a step's receive must net `-1`. Closing that is a change to the circuit —
    pin `is_valid` (`gatedPinned`) — not to the clause.

    A *fused* `unopt` fails for an unrelated reason: it is several instruction steps whose
    intermediate bridge states do not cancel, because powdr leaves `from_state__timestamp_0..n`
    algebraically unrelated until its substitution pass runs. Adding
    `from_state__timestamp_{i+1} = from_state__timestamp_i + d_i` collapses it to the one step the
    optimized stage already has (`unoptChained`). A single-instruction APC has one step to begin
    with and needs no such modification.

    **What a real APC's memory traffic looks like, and why the clause admits it.** Every memory
    *receive* sits at a free `*_prev_timestamp_*` column — the record an earlier instruction left,
    which the AssertLt gadget constrains only to be *less than* the access — and the first memory
    *send* sits at `from_state__timestamp_0 + 0`, i.e. exactly at the step's base. Neither fits
    the old `Circuit.advancesClock`, which demanded that memory sit strictly inside
    `(base, base + d)`; both fit `StepLayout`, which places an interaction at any integer offset
    in `[-maxLookback, d]` and orders only the sends. That is what every `opt_hasStepLayout` here
    exhibits, and it closes the memory half of finding G.

    See `agent-docs/vm-spec.md`. -/
