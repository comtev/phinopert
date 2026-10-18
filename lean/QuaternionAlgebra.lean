import Symmetry

/-!
Scalar-first Hamilton quaternion algebra in real coordinates. The homogeneous
action matrix agrees with `matrix` in `proofs/domain_core.py`; it is a rotation
when the quaternion has squared norm one. These algebraic primitives do not
establish finite-group closure, representative coverage, or containment symmetry.
-/
namespace Phinopert

abbrev QuaternionCoords := ℝ × Point

/-- The oriented cross product on the existing three-coordinate `Point`. -/
noncomputable def cross3 (u v : Point) : Point :=
  (u.2.1 * v.2.2 - u.2.2 * v.2.1,
   u.2.2 * v.1 - u.1 * v.2.2,
   u.1 * v.2.1 - u.2.1 * v.1)

/-- Standard scalar-first Hamilton multiplication, with explicit coordinates. -/
noncomputable def qProduct (p q : QuaternionCoords) : QuaternionCoords :=
  (p.1 * q.1 - p.2.1 * q.2.1 - p.2.2.1 * q.2.2.1 - p.2.2.2 * q.2.2.2,
   p.1 * q.2.1 + p.2.1 * q.1 + p.2.2.1 * q.2.2.2 - p.2.2.2 * q.2.2.1,
   p.1 * q.2.2.1 - p.2.1 * q.2.2.2 + p.2.2.1 * q.1 + p.2.2.2 * q.2.1,
   p.1 * q.2.2.2 + p.2.1 * q.2.2.1 - p.2.2.1 * q.2.1 + p.2.2.2 * q.1)

noncomputable def qNormSq (q : QuaternionCoords) : ℝ :=
  q.1 ^ 2 + q.2.1 ^ 2 + q.2.2.1 ^ 2 + q.2.2.2 ^ 2

/-- Homogeneous quaternion action; no implicit normalization is performed. -/
noncomputable def qAction (q : QuaternionCoords) (u : Point) : Point :=
  ((q.1*q.1 + q.2.1*q.2.1 - q.2.2.1*q.2.2.1 - q.2.2.2*q.2.2.2)*u.1
      + 2*(q.2.1*q.2.2.1 - q.1*q.2.2.2)*u.2.1
      + 2*(q.2.1*q.2.2.2 + q.1*q.2.2.1)*u.2.2,
   2*(q.2.1*q.2.2.1 + q.1*q.2.2.2)*u.1
      + (q.1*q.1 - q.2.1*q.2.1 + q.2.2.1*q.2.2.1 - q.2.2.2*q.2.2.2)*u.2.1
      + 2*(q.2.2.1*q.2.2.2 - q.1*q.2.1)*u.2.2,
   2*(q.2.1*q.2.2.2 - q.1*q.2.2.1)*u.1
      + 2*(q.2.2.1*q.2.2.2 + q.1*q.2.1)*u.2.1
      + (q.1*q.1 - q.2.1*q.2.1 - q.2.2.1*q.2.2.1 + q.2.2.2*q.2.2.2)*u.2.2)

theorem qProduct_scalar (p q : QuaternionCoords) :
    (qProduct p q).1 = p.1 * q.1 - dot p.2 q.2 := by
  dsimp [qProduct, dot]
  ring

theorem qProduct_vector (p q : QuaternionCoords) :
    (qProduct p q).2 = p.1 • q.2 + q.1 • p.2 + cross3 p.2 q.2 := by
  ext <;> simp [qProduct, cross3] <;> ring

theorem qProduct_assoc (p q r : QuaternionCoords) :
    qProduct (qProduct p q) r = qProduct p (qProduct q r) := by
  ext <;> dsimp [qProduct] <;> ring

theorem qProduct_one_left (q : QuaternionCoords) :
    qProduct (1, (0 : Point)) q = q := by
  ext <;> simp [qProduct]

theorem qProduct_one_right (q : QuaternionCoords) :
    qProduct q (1, (0 : Point)) = q := by
  ext <;> simp [qProduct]

theorem qProduct_neg_left (p q : QuaternionCoords) :
    qProduct (-p) q = -(qProduct p q) := by
  ext <;> simp [qProduct] <;> ring

theorem qProduct_neg_right (p q : QuaternionCoords) :
    qProduct p (-q) = -(qProduct p q) := by
  ext <;> simp [qProduct] <;> ring

theorem qNormSq_nonneg (q : QuaternionCoords) : 0 ≤ qNormSq q := by
  dsimp [qNormSq]
  positivity

theorem qNormSq_one : qNormSq (1, (0 : Point)) = 1 := by
  norm_num [qNormSq]

theorem qNormSq_neg (q : QuaternionCoords) : qNormSq (-q) = qNormSq q := by
  simp [qNormSq]

theorem qNormSq_product (p q : QuaternionCoords) :
    qNormSq (qProduct p q) = qNormSq p * qNormSq q := by
  dsimp [qNormSq, qProduct]
  ring

theorem qProduct_unit (p q : QuaternionCoords)
    (hp : qNormSq p = 1) (hq : qNormSq q = 1) :
    qNormSq (qProduct p q) = 1 := by
  rw [qNormSq_product, hp, hq, one_mul]

theorem qAction_one (u : Point) : qAction (1, (0 : Point)) u = u := by
  ext <;> simp [qAction]

theorem qAction_neg (q : QuaternionCoords) (u : Point) :
    qAction (-q) u = qAction q u := by
  ext <;> simp [qAction]

set_option maxHeartbeats 800000 in
/-- The right factor acts first, matching Hamilton multiplication. -/
theorem qAction_product (p q : QuaternionCoords) (u : Point) :
    qAction (qProduct p q) u = qAction p (qAction q u) := by
  ext <;> dsimp [qAction, qProduct] <;> ring

set_option maxHeartbeats 800000 in
theorem qAction_dot (q : QuaternionCoords) (u v : Point) :
    dot (qAction q u) (qAction q v) = qNormSq q ^ 2 * dot u v := by
  dsimp [qAction, qNormSq, dot]
  ring

theorem qAction_dot_of_unit (q : QuaternionCoords) (hq : qNormSq q = 1)
    (u v : Point) : dot (qAction q u) (qAction q v) = dot u v := by
  rw [qAction_dot, hq, one_pow, one_mul]

/-- Squared Euclidean length preservation for unit quaternions. -/
theorem qAction_normSq_of_unit (q : QuaternionCoords) (hq : qNormSq q = 1)
    (u : Point) : dot (qAction q u) (qAction q u) = dot u u :=
  qAction_dot_of_unit q hq u u

/-- Scalar part of the left-associated Hamilton product `(0,u) * (1,r) * g`.
No unit or nonzero hypotheses are needed. -/
theorem qProduct_scalar_fold (u r : Point) (g : QuaternionCoords) :
    (qProduct (qProduct (0, u) (1, r)) g).1 =
      -g.1 * dot u r - dot g.2 (u + cross3 u r) := by
  simp [qProduct, dot, cross3]
  ring

end Phinopert

#print axioms Phinopert.qProduct_scalar
#print axioms Phinopert.qProduct_vector
#print axioms Phinopert.qProduct_assoc
#print axioms Phinopert.qProduct_one_left
#print axioms Phinopert.qProduct_one_right
#print axioms Phinopert.qProduct_neg_left
#print axioms Phinopert.qProduct_neg_right
#print axioms Phinopert.qNormSq_nonneg
#print axioms Phinopert.qNormSq_one
#print axioms Phinopert.qNormSq_neg
#print axioms Phinopert.qNormSq_product
#print axioms Phinopert.qProduct_unit
#print axioms Phinopert.qAction_one
#print axioms Phinopert.qAction_neg
#print axioms Phinopert.qAction_product
#print axioms Phinopert.qAction_dot
#print axioms Phinopert.qAction_dot_of_unit
#print axioms Phinopert.qAction_normSq_of_unit
#print axioms Phinopert.qProduct_scalar_fold
