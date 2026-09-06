import ApcOptimizer.VmSpec.Audit.Apcs.Keccak2105000.Opt
import ApcOptimizer.VmSpec.Audit.OF.Check

set_option autoImplicit false

/-! **`Keccak2105000`'s `opt` against `Circuit.legalGuestOF`**, by one `decide`.

    The largest block audited: `d = 11`, five access pairs `0 ↔ 1`, `2 ↔ 8`, `4 ↔ 9`, `5 ↔ 6`,
    `10 ↔ 11`. -/

namespace ApcOptimizer.OpenVM.Keccak2105000

open ApcOptimizer.OpenVM ApcOptimizer.OpenVM.OFCheck

def optPartnerList : List ℕ :=
  [1, 0, 8, 3, 9, 6, 5, 7, 2, 4, 11, 10, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

theorem optOFCheck :
    ofCheckAll layoutVars optPinRules openVmMemBusId openVmTimestampBound 11
      opt.busInteractions recipes optPartnerList = true := by decide

theorem opt_hasStepLayoutOF {maxWindow : ℕ} (hw : 11 < maxWindow) :
    opt.hasStepLayoutOF apcRules openVmMemAddress maxWindow openVmTimestampBound :=
  hasStepLayoutOF_of_ofCheck (by norm_num) hw (fun _ halg => optPinRules_hold _ halg) optBaseLin
    (fun asg halg => bridgeCheck_sound optBridgeCheck (optPinRules_hold asg halg))
    optPlaceCheck optOrderCheck optFitsCheck optByteCheck
    (fun _ halg hacc => optLookbacks halg hacc)
    (fun _ _ hacc i hwit _ _ => optWriteOk hacc i hwit)
    optOFCheck

theorem opt_legalGuestOF {maxWindow maxInteractions : ℕ} (hw : 11 < maxWindow)
    (hi : 23 ≤ maxInteractions) :
    opt.legalGuestOF apcRules openVmMemAddress maxWindow openVmTimestampBound maxInteractions where
  sendOnly := opt_legalMultiplicities.1
  polarity := opt_legalMultiplicities.2
  stepLayout := opt_hasStepLayoutOF hw
  size := by simpa [opt] using hi
  x0Zero := x0Zero_of_ofCheck (fun _ halg => optPinRules_hold _ halg) optOFCheck

end ApcOptimizer.OpenVM.Keccak2105000
