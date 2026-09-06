import ApcOptimizer.VmSpec.Audit.OF.SingleBeq
import ApcOptimizer.VmSpec.Audit.OF.SingleXor
import ApcOptimizer.VmSpec.Audit.OF.AndBranch
import ApcOptimizer.VmSpec.Audit.OF.LoadBranch
import ApcOptimizer.VmSpec.Audit.OF.TwoLoads
import ApcOptimizer.VmSpec.Audit.OF.Keccak2105000

/-! **`Circuit.legalGuestOF` measured against real APCs.**

    `Audit/RealApcLegality.lean` is the index for `Circuit.legalGuest`; this is the index for the
    *order-free* strengthening (`VmSpec/LegalOF.lean`) that VM-level completeness needs. Every APC
    in the corpus satisfies it, at the stage powdr's optimizer actually emits:

    | APC | interactions | `d` | accesses |
    | --- | --- | --- | --- |
    | `SingleBeq` | 10 | 2 | `0 ↔ 1`, `2 ↔ 3` |
    | `AndBranch` | 15 | 5 | `1 ↔ 2`, `3 ↔ 5`, `6 ↔ 7` |
    | `SingleXor` | 18 | 3 | `4 ↔ 5`, `6 ↔ 7`, `8 ↔ 9` |
    | `LoadBranch` | 20 | 5 | `0 ↔ 1`, `2 ↔ 3`, `4 ↔ 8`, `6 ↔ 7` |
    | `Keccak2105000` | 23 | 11 | `0 ↔ 1`, `2 ↔ 8`, `4 ↔ 9`, `5 ↔ 6`, `10 ↔ 11` |
    | `TwoLoads` | 30 | 8 | `0 ↔ 1`, `2 ↔ 3`, `4 ↔ 11`, `6 ↔ 7`, `8 ↔ 9`, `10 ↔ 12` |

    Each file is the same twenty-odd lines: a pairing list, one `ofCheckAll … = true` settled by a
    kernel `decide`, and two applications of `Audit/OF/Check.lean`'s soundness theorems. Nothing
    case-splits on an interaction index, which is what makes the thirty-interaction blocks
    tractable — an earlier `fin_cases` treatment went through for `SingleBeq` alone and exhausted
    the heartbeat budget on every other APC.

    **What the corpus rules out.** These are not vacuous passes; three of `legalGuestOF`'s clauses
    were shaped by them. `sendInWindow` is half-open because `SingleBeq`'s first register read
    commits at offset `0`, refuting the strict form §4.2 states. `sendTimesDistinct` is per
    *address* because `LoadBranch`, `AndBranch` and `Keccak2105000` each carry two or three
    interactions at tick `0`. And `sameAddr` compares linear forms with a syntactic fallback
    because `TwoLoads` addresses computed pointers, whose expressions mention variables outside
    the layout's own list. -/
