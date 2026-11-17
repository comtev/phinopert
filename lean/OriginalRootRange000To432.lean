import OriginalRootCoverage
import OriginalRootRange000To208
import OriginalRootRange208To432
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
namespace Phinopert
theorem originalrootrange000to432_excludes
    (i : Fin 432) (hlo : 0 ≤ i.val) (hhi : i.val < 432)
    (s t : ℝ) (r : Point) (hb : InClosedBox (originalRootBox i) s t r) (hd : InIcoDomain s t r) :
    ¬ StrictShadowFit s t r 0 := by
  by_cases h : i.val < 208
  · exact originalrootrange000to208_excludes i hlo h s t r hb hd
  · exact originalrootrange208to432_excludes i (Nat.le_of_not_gt h) hhi s t r hb hd
end Phinopert
#print axioms Phinopert.originalrootrange000to432_excludes
