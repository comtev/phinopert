import OriginalRootCoverage
import OriginalRootRange000To432
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
namespace Phinopert
theorem actual_phinopert_no_proper_shadow_fit : NoProperShadowFit := by
  apply original_roots_imply_no_proper_shadow_fit
  intro i s t r hb hd
  exact originalrootrange000to432_excludes i (Nat.zero_le _) i.isLt s t r hb hd
end Phinopert
#print axioms Phinopert.actual_phinopert_no_proper_shadow_fit
