import IcosahedralInvariance
import IcosahedralWalls
import IcosahedralSelection

/-!
Fixed-view shadow identities for the actual quaternion candidates. The view
half-turn negates screen coordinates, while central symmetry removes that
negation at the level of shadow sets. Right icosahedral multiplication uses
the explicitly supplied vertex checks. No physical coverage hypothesis, group
closure table, or unit-norm hypothesis on the input quaternion is needed.
-/
namespace Phinopert

/-- A pure unit quaternion about the screen kernel negates the screen. -/
theorem screen_pure_halfturn (s t : ℝ) (n p : Point)
    (hn : screen s t n = 0) (hu : qNormSq (0,n) = 1) :
    screen s t (qAction (0,n) p) = -screen s t p := by
  have hd : dot n n = 1 := by
    simpa [qNormSq, dot, pow_two] using hu
  rw [pure_quaternion_action, map_sub, map_smul, map_smul, hn, hd,
    smul_zero, one_smul, zero_sub]

#print axioms Phinopert.screen_pure_halfturn

theorem icoViewHalfturn_screen_kernel (s t : ℝ) :
    screen s t (icoViewHalfturn s t).2 = 0 := by
  ext <;> simp [screen, icoViewHalfturn, div_eq_mul_inv]

#print axioms Phinopert.icoViewHalfturn_screen_kernel

/-- The actual normalized half-turn about (s,t,1) flips both screen coordinates. -/
theorem screen_icoViewHalfturn (s t : ℝ) (p : Point) :
    screen s t (qAction (icoViewHalfturn s t) p) = -screen s t p :=
  screen_pure_halfturn s t (icoViewHalfturn s t).2 p
    (icoViewHalfturn_screen_kernel s t) (icoViewHalfturn_unit s t)

#print axioms Phinopert.screen_icoViewHalfturn

/-- Shadow of the solid after the homogeneous quaternion action. -/
noncomputable def quatShadow (s t : ℝ) (q : QuaternionCoords) : Set Plane :=
  ((screen s t).comp (qActionLinear q)) '' solid

theorem mem_quatShadow (s t : ℝ) (q : QuaternionCoords) (y : Plane) :
    y ∈ quatShadow s t q ↔ ∃ x ∈ solid, screen s t (qAction q x) = y :=
  Iff.rfl

#print axioms Phinopert.mem_quatShadow

theorem quatShadow_centrally_symmetric (s t : ℝ) (q : QuaternionCoords)
    {y : Plane} (hy : y ∈ quatShadow s t q) : -y ∈ quatShadow s t q := by
  obtain ⟨x, hx, rfl⟩ := hy
  exact ⟨-x, solid_centrally_symmetric hx,
    ((screen s t).comp (qActionLinear q)).map_neg x⟩

#print axioms Phinopert.quatShadow_centrally_symmetric

/-- Right multiplication by an actual group element leaves the shadow unchanged. -/
theorem quatShadow_right_icoReal_of_checks
    (hchecks : ∀ i : Fin 60, IcoVertexRow i.val)
    (s t : ℝ) (q : QuaternionCoords) {g : QuaternionCoords}
    (hg : g ∈ icoReal (Real.sqrt 5)) :
    quatShadow s t (qProduct q g) = quatShadow s t q := by
  calc
    quatShadow s t (qProduct q g) =
        (fun x => screen s t (qAction q x)) '' (qAction g '' solid) := by
      change (fun x => screen s t (qAction (qProduct q g) x)) '' solid = _
      rw [Set.image_image]
      apply congrArg (fun f : Point → Plane => f '' solid)
      funext x
      exact congrArg (screen s t) (qAction_product q g x)
    _ = quatShadow s t q := by
      rw [icoReal_solid_image_of_checks hchecks hg]
      rfl

#print axioms Phinopert.quatShadow_right_icoReal_of_checks

/-- A left action that negates screen coordinates preserves the shadow set. -/
theorem quatShadow_left_of_screen_neg (s t : ℝ) (q j : QuaternionCoords)
    (hj : ∀ x : Point, screen s t (qAction j x) = -screen s t x) :
    quatShadow s t (qProduct j q) = quatShadow s t q := by
  apply Set.ext
  intro y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := (mem_quatShadow s t (qProduct j q) y).mp hy
    rw [qAction_product, hj]
    exact quatShadow_centrally_symmetric s t q
      ((mem_quatShadow s t q _).mpr ⟨x, hx, rfl⟩)
  · intro hy
    obtain ⟨x, hx, rfl⟩ := (mem_quatShadow s t q y).mp hy
    apply (mem_quatShadow s t (qProduct j q) _).mpr
    refine ⟨-x, solid_centrally_symmetric hx, ?_⟩
    rw [qAction_product, hj, qAction_point_neg, map_neg, neg_neg]

#print axioms Phinopert.quatShadow_left_of_screen_neg

theorem quatShadow_left_icoViewHalfturn (s t : ℝ) (q : QuaternionCoords) :
    quatShadow s t (qProduct (icoViewHalfturn s t) q) = quatShadow s t q :=
  quatShadow_left_of_screen_neg s t q (icoViewHalfturn s t)
    (screen_icoViewHalfturn s t)

#print axioms Phinopert.quatShadow_left_icoViewHalfturn

/-- Every candidate from the actual signed group has the input shadow whenever
the left multiplier flips the screen. This is a shadow equality, not coverage. -/
theorem ico_quaternionCandidates_shadow_of_checks
    (hchecks : ∀ i : Fin 60, IcoVertexRow i.val)
    (s t : ℝ) (p j : QuaternionCoords)
    (hj : ∀ x : Point, screen s t (qAction j x) = -screen s t x)
    {q : QuaternionCoords} (hq : q ∈ quaternionCandidates icoSelectionGroup p j) :
    quatShadow s t q = quatShadow s t p := by
  rcases (mem_quaternionCandidates icoSelectionGroup p j q).mp hq with
    ⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩
  · exact quatShadow_right_icoReal_of_checks hchecks s t p
      ((mem_icoSelectionGroup g).mp hg)
  · rw [quatShadow_right_icoReal_of_checks hchecks s t (qProduct j p)
      ((mem_icoSelectionGroup g).mp hg)]
    exact quatShadow_left_of_screen_neg s t p j hj

#print axioms Phinopert.ico_quaternionCandidates_shadow_of_checks

/-- All actual candidates with the prescribed view half-turn preserve the
original fixed-view shadow, with only the vertex-check table supplied. -/
theorem ico_view_candidates_shadow_of_checks
    (hchecks : ∀ i : Fin 60, IcoVertexRow i.val)
    (s t : ℝ) (p : QuaternionCoords) {q : QuaternionCoords}
    (hq : q ∈ quaternionCandidates icoSelectionGroup p (icoViewHalfturn s t)) :
    quatShadow s t q = quatShadow s t p :=
  ico_quaternionCandidates_shadow_of_checks hchecks s t p (icoViewHalfturn s t)
    (screen_icoViewHalfturn s t) hq

#print axioms Phinopert.ico_view_candidates_shadow_of_checks

end Phinopert
