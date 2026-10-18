import QuaternionAlgebra

namespace Phinopert

theorem qAction_scale (a : ℝ) (q : QuaternionCoords) (p : Point) :
    qAction (a • q) p = (a*a) • qAction q p := by
  ext <;> simp [qAction] <;> ring

theorem qAction_one_scalar (r p : Point) : qAction (1,r) p = numerator r p := by
  ext <;> dsimp [qAction,numerator] <;> ring

theorem qNormSq_normalised (a : ℝ) (r : Point) :
    qNormSq (a • (1,r)) = (a*a)*denom r := by
  simp [qNormSq,denom,dot]; ring

/-- Once a unit quaternion has a nonzero scalar, its normalised action is
exactly the Cayley rotation already used by the support certificates. -/
theorem quaternion_action_eq_cayley (a : ℝ) (r p : Point)
    (hunit : qNormSq (a • (1,r))=1) :
    qAction (a • (1,r)) p = cayley r p := by
  have hn : (a*a)*denom r=1 := by rwa [qNormSq_normalised] at hunit
  rw [qAction_scale,qAction_one_scalar]
  have hd := ne_of_gt (denom_positive r)
  have scalar : ∀ x : ℝ, (a*a)*x = x/denom r := by
    intro x
    apply (eq_div_iff hd).mpr
    calc
      (a*a*x)*denom r = ((a*a)*denom r)*x := by ring
      _ = x := by rw [hn,one_mul]
  ext <;> simp only [Prod.smul_fst,Prod.smul_snd,smul_eq_mul,cayley] <;> exact scalar _

theorem normalise_nonzero_scalar (q : QuaternionCoords) (ha : q.1 ≠ 0) :
    q = q.1 • (1,(q.2.1/q.1,q.2.2.1/q.1,q.2.2.2/q.1)) := by
  ext <;> simp [mul_div_cancel₀ _ ha]

end Phinopert
#print axioms Phinopert.qAction_scale
#print axioms Phinopert.qAction_one_scalar
#print axioms Phinopert.qNormSq_normalised
#print axioms Phinopert.quaternion_action_eq_cayley
#print axioms Phinopert.normalise_nonzero_scalar
