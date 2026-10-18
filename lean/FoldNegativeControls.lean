import FoldBox

namespace Phinopert

/-- Squared positivity at both ends does not by itself cover the interval. -/
theorem fold_unsigned_corner_counterexample :
    (-2:ℝ)^2 > 1 ∧ (2:ℝ)^2 > 1 ∧ ¬ ((0:ℝ)^2 > 1) := by norm_num

theorem fold_wrong_sign_rejected : ¬ FoldSafe (-2) (0,0,1) := by
  norm_num [FoldSafe,dot]

theorem fold_zero_margin_rejected : ¬ FoldSafe 1 (0,0,1) := by
  norm_num [FoldSafe,dot]

theorem fold_negative_branch_valid : FoldSafe (-(-2)) (0,0,1) := by
  norm_num [FoldSafe,dot]

theorem fold_singleton_interval (f : ℝ → ℝ) (g : ℝ → Point) (a x : ℝ)
    (hx : a ≤ x ∧ x ≤ a) (h : FoldSafe (f a) (g a)) : FoldSafe (f x) (g x) := by
  have : x=a := by linarith
  simpa [this] using h

end Phinopert
#print axioms Phinopert.fold_unsigned_corner_counterexample
#print axioms Phinopert.fold_wrong_sign_rejected
#print axioms Phinopert.fold_zero_margin_rejected
#print axioms Phinopert.fold_negative_branch_valid
#print axioms Phinopert.fold_singleton_interval
