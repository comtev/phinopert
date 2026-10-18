import OrthogonalShadow
import IcosahedralInvariance

/-! Changing viewing direction by a proper unit-quaternion action. A nonzero
signed scale on the normal changes neither the shadow plane nor the plug's
orientation. No arbitrary SO(3) representation theorem is asserted here. -/
namespace Phinopert
open Set

noncomputable def qConjugate (q : QuaternionCoords) : QuaternionCoords := (q.1,-q.2)

theorem qConjugate_product (q : QuaternionCoords) (hq : qNormSq q = 1) :
    qProduct (qConjugate q) q = (1,(0 : Point)) ∧
      qProduct q (qConjugate q) = (1,(0 : Point)) := by
  dsimp [qNormSq] at hq
  constructor <;> ext <;> simp [qProduct, qConjugate] <;> nlinarith

theorem qConjugate_normSq (q : QuaternionCoords) :
    qNormSq (qConjugate q) = qNormSq q := by simp [qConjugate, qNormSq]

theorem qConjugate_action_left (q : QuaternionCoords) (hq : qNormSq q = 1)
    (p : Point) : qAction (qConjugate q) (qAction q p) = p := by
  rw [← qAction_product, (qConjugate_product q hq).1, qAction_one]

theorem qConjugate_action_right (q : QuaternionCoords) (hq : qNormSq q = 1)
    (p : Point) : qAction q (qAction (qConjugate q) p) = p := by
  rw [← qAction_product, (qConjugate_product q hq).2, qAction_one]

theorem dot_smul_left (a : ℝ) (u p : Point) : dot (a • u) p = a * dot u p := by
  simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem qAction_continuous (q : QuaternionCoords) : Continuous (qAction q) := by
  unfold qAction
  fun_prop

theorem rotated_perpendicular (u : Point) (q : QuaternionCoords)
    (hq : qNormSq q = 1) (s t k : ℝ) (hk : k ≠ 0)
    (hdir : qAction q u = k • (s,t,1)) (p : Point) (hp : dot u p = 0) :
    dot (s,t,1) (qAction q p) = 0 := by
  have h := qAction_dot_of_unit q hq u p
  rw [hdir, dot_smul_left, hp] at h
  exact (mul_eq_zero.mp h).resolve_left hk

theorem unrotated_perpendicular (u : Point) (q : QuaternionCoords)
    (hq : qNormSq q = 1) (s t k : ℝ)
    (hdir : qAction q u = k • (s,t,1)) (p : Point) (hp : dot (s,t,1) p = 0) :
    dot u (qAction (qConjugate q) p) = 0 := by
  have h := qAction_dot_of_unit q hq u (qAction (qConjugate q) p)
  rw [qConjugate_action_right q hq, hdir, dot_smul_left, hp, mul_zero] at h
  exact h.symm

noncomputable def rotatedScreenHomeomorph (u : Point) (q : QuaternionCoords)
    (hq : qNormSq q = 1) (s t k : ℝ) (hk : k ≠ 0)
    (hdir : qAction q u = k • (s,t,1)) : normalPlane u ≃ₜ Plane where
  toFun p := screen s t (qAction q p.val)
  invFun x := ⟨qAction (qConjugate q) (screenLift s t x),
    unrotated_perpendicular u q hq s t k hdir _ (screenLift_perpendicular s t x)⟩
  left_inv p := by
    apply Subtype.ext
    change qAction (qConjugate q) (screenLift s t (screen s t (qAction q p.val))) = p.val
    rw [screenLift_screen s t _ (rotated_perpendicular u q hq s t k hk hdir _ p.property),
      qConjugate_action_left q hq]
  right_inv x := by
    change screen s t (qAction q (qAction (qConjugate q) (screenLift s t x))) = x
    rw [qConjugate_action_right q hq, screen_screenLift]
  continuous_toFun := by
    have h := (qAction_continuous q).comp (continuous_subtype_val (p := fun p => p ∈ normalPlane u))
    change Continuous (fun p : normalPlane u =>
      ((qAction q p.val).1-s*(qAction q p.val).2.2,
        (qAction q p.val).2.1-t*(qAction q p.val).2.2))
    exact (h.fst.sub (continuous_const.mul h.snd.snd)).prodMk
      (h.snd.fst.sub (continuous_const.mul h.snd.snd))
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply (qAction_continuous _).comp
    change Continuous (fun x : Plane => screenLift s t x)
    unfold screenLift
    fun_prop

theorem rotatedScreen_project (u : Point) (hu : u ≠ 0) (q : QuaternionCoords)
    (hq : qNormSq q = 1) (s t k : ℝ) (hk : k ≠ 0)
    (hdir : qAction q u = k • (s,t,1)) (p : Point) :
    rotatedScreenHomeomorph u q hq s t k hk hdir (planeProject u hu p) =
      screen s t (qAction q p) := by
  change screen s t (qActionLinear q (p - (dot u p / dot u u) • u)) = _
  rw [map_sub, map_smul, map_sub, map_smul]
  change screen s t (qAction q p) - (dot u p / dot u u) • screen s t (qAction q u) = _
  rw [hdir, map_smul]
  have hz : screen s t (s,t,1) = 0 := by ext <;> simp [screen]
  rw [hz, smul_zero, smul_zero, sub_zero]

/-- Covariance for an arbitrary outer body, with its transformed image explicit. -/
theorem strict_containment_change_view (u : Point) (hu : u ≠ 0) (q : QuaternionCoords)
    (hq : qNormSq q = 1) (s t k : ℝ) (hk : k ≠ 0)
    (hdir : qAction q u = k • (s,t,1)) (outer : Set Point)
    (hsolid : qAction q '' outer = solid)
    (f : Point → Point) (offset : normalPlane u)
    (hfit : ∀ x ∈ solid, planeProject u hu (f x) + offset ∈
      interior (planeProject u hu '' outer)) :
    ∀ x ∈ solid, screen s t (qAction q (f x)) + screen s t (qAction q offset.val) ∈
      interior (screen s t '' solid) := by
  let e := rotatedScreenHomeomorph u q hq s t k hk hdir
  have hs : e '' (planeProject u hu '' outer) = screen s t '' solid := by
    rw [Set.image_image]
    have he : (fun p => e (planeProject u hu p)) =
        (fun p => screen s t (qAction q p)) := by
      funext p
      exact rotatedScreen_project u hu q hq s t k hk hdir p
    rw [he, ← Set.image_image, hsolid]
  have hi := e.image_interior (planeProject u hu '' outer)
  rw [hs] at hi
  intro x hx
  have hm : e (planeProject u hu (f x) + offset) ∈
      e '' interior (planeProject u hu '' outer) := ⟨_, hfit x hx, rfl⟩
  rw [hi] at hm
  have ha : e (planeProject u hu (f x) + offset) =
      screen s t (qAction q (f x)) + screen s t (qAction q offset.val) := by
    change screen s t (qActionLinear q (orthogonalProject u (f x) + offset.val)) = _
    rw [map_add, map_add]
    exact congrArg (fun z => z + screen s t (qAction q offset.val))
      (rotatedScreen_project u hu q hq s t k hk hdir (f x))
  rwa [ha] at hm

/-- The special case of a symmetry of the fixed hole body. -/
theorem strict_fit_change_view (u : Point) (hu : u ≠ 0) (q : QuaternionCoords)
    (hq : qNormSq q = 1) (s t k : ℝ) (hk : k ≠ 0)
    (hdir : qAction q u = k • (s,t,1)) (hsolid : qAction q '' solid = solid)
    (f : Point → Point) (offset : normalPlane u)
    (hfit : StrictOrthogonalFit u hu f offset) :
    ∀ x ∈ solid, screen s t (qAction q (f x)) + screen s t (qAction q offset.val) ∈
      interior (screen s t '' solid) :=
  strict_containment_change_view u hu q hq s t k hk hdir solid hsolid f offset hfit

end Phinopert
#print axioms Phinopert.qConjugate_product
#print axioms Phinopert.qConjugate_normSq
#print axioms Phinopert.qConjugate_action_left
#print axioms Phinopert.qConjugate_action_right
#print axioms Phinopert.dot_smul_left
#print axioms Phinopert.qAction_continuous
#print axioms Phinopert.rotated_perpendicular
#print axioms Phinopert.unrotated_perpendicular
#print axioms Phinopert.rotatedScreenHomeomorph
#print axioms Phinopert.rotatedScreen_project
#print axioms Phinopert.strict_fit_change_view
#print axioms Phinopert.strict_containment_change_view
