import Geometry
import Symmetry

/-! Actual perpendicular-plane shadows. The interior below is taken in the
two-dimensional subspace, never in ambient three-dimensional space. -/
namespace Phinopert
open Set

def normalPlane (u : Point) : Submodule ℝ Point where
  carrier := {p | dot u p = 0}
  zero_mem' := by simp [dot]
  add_mem' := by
    intro p q hp hq
    change dot u p = 0 at hp
    change dot u q = 0 at hq
    change dot u (p+q) = 0
    simp only [dot, Prod.fst_add, Prod.snd_add] at *
    nlinarith
  smul_mem' := by
    intro a p hp
    change dot u p = 0 at hp
    change dot u (a • p) = 0
    simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at *
    calc
      _ = a * (u.1*p.1+u.2.1*p.2.1+u.2.2*p.2.2) := by ring
      _ = 0 := by rw [hp, mul_zero]

noncomputable def orthogonalProject (u p : Point) : Point :=
  p - (dot u p / dot u u) • u

theorem orthogonalProject_perpendicular (u : Point) (hu : u ≠ 0) (p : Point) :
    dot u (orthogonalProject u p) = 0 := by
  have h := ne_of_gt (dot_self_positive u hu)
  have he : dot u (orthogonalProject u p) =
      dot u p - (dot u p / dot u u) * dot u u := by
    simp only [orthogonalProject, dot, Prod.fst_sub, Prod.snd_sub,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  rw [he, div_mul_cancel₀ _ h, sub_self]

noncomputable def planeProject (u : Point) (hu : u ≠ 0) (p : Point) : normalPlane u :=
  ⟨orthogonalProject u p, orthogonalProject_perpendicular u hu p⟩

theorem orthogonalProject_add (u p v : Point) :
    orthogonalProject u (p+v) = orthogonalProject u p + orthogonalProject u v := by
  have hd : dot u (p+v) = dot u p + dot u v := by
    simp only [dot, Prod.fst_add, Prod.snd_add]
    ring
  unfold orthogonalProject
  rw [hd, add_div, add_smul]
  abel

theorem planeProject_add (u : Point) (hu : u ≠ 0) (p v : Point) :
    planeProject u hu (p+v) = planeProject u hu p + planeProject u hu v :=
  Subtype.ext (orthogonalProject_add u p v)

theorem orthogonalProject_fixed (u p : Point) (hp : dot u p = 0) :
    orthogonalProject u p = p := by
  simp [orthogonalProject, hp]

theorem chart_direction_nonzero (s t : ℝ) : ((s,t,1) : Point) ≠ 0 := by
  intro h
  have := congrArg (fun p : Point => p.2.2) h
  norm_num at this

theorem screen_orthogonalProject (s t : ℝ) (p : Point) :
    screen s t (orthogonalProject (s,t,1) p) = screen s t p := by
  change screen s t (p - (dot (s,t,1) p / dot (s,t,1) (s,t,1)) • (s,t,1)) = _
  rw [map_sub, map_smul]
  have h : screen s t (s,t,1) = 0 := by ext <;> simp [screen]
  rw [h, smul_zero, sub_zero]

noncomputable def screenLift (s t : ℝ) (x : Plane) : Point :=
  let z := -(s*x.1+t*x.2)/(1+s*s+t*t)
  (x.1+s*z, x.2+t*z, z)

theorem chart_denominator_positive (s t : ℝ) : 0 < 1+s*s+t*t := by
  nlinarith [sq_nonneg s, sq_nonneg t]

theorem screenLift_perpendicular (s t : ℝ) (x : Plane) :
    dot (s,t,1) (screenLift s t x) = 0 := by
  have hz := div_mul_cancel₀ (-(s*x.1+t*x.2))
    (ne_of_gt (chart_denominator_positive s t))
  dsimp [dot, screenLift]
  nlinarith

theorem screen_screenLift (s t : ℝ) (x : Plane) :
    screen s t (screenLift s t x) = x := by
  ext <;> dsimp [screen, screenLift] <;> ring

theorem screenLift_screen (s t : ℝ) (p : Point)
    (hp : dot (s,t,1) p = 0) : screenLift s t (screen s t p) = p := by
  have hd := ne_of_gt (chart_denominator_positive s t)
  have hz : -(s*(p.1-s*p.2.2)+t*(p.2.1-t*p.2.2))/(1+s*s+t*t) = p.2.2 := by
    apply (div_eq_iff hd).mpr
    dsimp [dot] at hp
    nlinarith
  change (p.1-s*p.2.2+s*_, p.2.1-t*p.2.2+t*_, _) = p
  dsimp [screen]
  rw [hz]
  ext <;> dsimp <;> ring

/-- A continuous linear-coordinate chart with an explicit continuous inverse. -/
noncomputable def screenHomeomorph (s t : ℝ) : normalPlane (s,t,1) ≃ₜ Plane where
  toFun p := screen s t p.val
  invFun x := ⟨screenLift s t x, screenLift_perpendicular s t x⟩
  left_inv p := Subtype.ext (screenLift_screen s t p.val p.property)
  right_inv := screen_screenLift s t
  continuous_toFun := by
    change Continuous (fun p : normalPlane (s,t,1) =>
      (p.val.1-s*p.val.2.2, p.val.2.1-t*p.val.2.2))
    fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    change Continuous (fun x : Plane => screenLift s t x)
    unfold screenLift
    fun_prop

theorem screenHomeomorph_project (s t : ℝ) (p : Point) :
    screenHomeomorph s t (planeProject (s,t,1) (chart_direction_nonzero s t) p) =
      screen s t p := screen_orthogonalProject s t p

theorem screenHomeomorph_shadow (s t : ℝ) (K : Set Point) :
    screenHomeomorph s t '' (planeProject (s,t,1) (chart_direction_nonzero s t) '' K) =
      screen s t '' K := by
  rw [Set.image_image]
  have he : (fun p => screenHomeomorph s t
      (planeProject (s,t,1) (chart_direction_nonzero s t) p)) = screen s t := by
    funext p
    exact screenHomeomorph_project s t p
  rw [he]

/-- Strict containment of orthogonal shadows, with a translation in the shadow
plane. The plug map is deliberately arbitrary in this coordinate bridge. -/
def StrictOrthogonalFit (u : Point) (hu : u ≠ 0) (f : Point → Point)
    (offset : normalPlane u) : Prop :=
  ∀ x ∈ solid, planeProject u hu (f x) + offset ∈ interior (planeProject u hu '' solid)

theorem strict_orthogonal_iff_screen (s t : ℝ) (f : Point → Point)
    (offset : normalPlane (s,t,1)) :
    StrictOrthogonalFit (s,t,1) (chart_direction_nonzero s t) f offset ↔
      ∀ x ∈ solid, screen s t (f x) + screen s t offset.val ∈
        interior (screen s t '' solid) := by
  have hi := (screenHomeomorph s t).image_interior
    (planeProject (s,t,1) (chart_direction_nonzero s t) '' solid)
  rw [screenHomeomorph_shadow] at hi
  have hm (p : normalPlane (s,t,1)) :
      p ∈ interior (planeProject (s,t,1) (chart_direction_nonzero s t) '' solid) ↔
      screenHomeomorph s t p ∈ interior (screen s t '' solid) := by
    rw [← hi]
    exact ((screenHomeomorph s t).injective.mem_set_image).symm
  have ha (x : Point) : screenHomeomorph s t
      (planeProject (s,t,1) (chart_direction_nonzero s t) (f x) + offset) =
      screen s t (f x) + screen s t offset.val := by
    change screen s t (orthogonalProject (s,t,1) (f x) + offset.val) = _
    rw [map_add, screen_orthogonalProject]
  unfold StrictOrthogonalFit
  simp_rw [hm, ha]

end Phinopert
#print axioms Phinopert.orthogonalProject_perpendicular
#print axioms Phinopert.orthogonalProject_add
#print axioms Phinopert.planeProject_add
#print axioms Phinopert.orthogonalProject_fixed
#print axioms Phinopert.chart_direction_nonzero
#print axioms Phinopert.screen_orthogonalProject
#print axioms Phinopert.chart_denominator_positive
#print axioms Phinopert.screenLift_perpendicular
#print axioms Phinopert.screen_screenLift
#print axioms Phinopert.screenLift_screen
#print axioms Phinopert.screenHomeomorph
#print axioms Phinopert.screenHomeomorph_project
#print axioms Phinopert.screenHomeomorph_shadow
#print axioms Phinopert.strict_orthogonal_iff_screen
