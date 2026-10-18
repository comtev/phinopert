import SupportGeometry
namespace Phinopert
theorem support_zero_sign_valid : ZNonneg (0,0) := by decide
theorem support_negative_cancellation_rejected : ¬ ZNonneg (2,-1) := by decide
theorem support_positive_cancellation_valid : ZNonneg (-2,1) := by decide
theorem support_bernstein_interior_counterexample :
    (1-8*(0:ℝ)*(1-0)=1) ∧ (1-8*(1:ℝ)*(1-1)=1) ∧ (1-8*(1/2:ℝ)*(1-1/2)<0) := by norm_num
theorem support_zero_normal_rejected : ¬ ((0,0,0):Point) ≠ 0 := by simp
theorem support_false_identity_rejected : ¬ (∀ x : ℝ, x^2+1=x^2+2) := by
  intro h
  have := h 0
  norm_num at this
end Phinopert
#print axioms Phinopert.support_zero_sign_valid
#print axioms Phinopert.support_negative_cancellation_rejected
#print axioms Phinopert.support_positive_cancellation_valid
#print axioms Phinopert.support_bernstein_interior_counterexample
#print axioms Phinopert.support_zero_normal_rejected
#print axioms Phinopert.support_false_identity_rejected
