import IcosahedralReal
import Mathlib.Tactic.FinCases

/-! Three actual icosahedral wall reflections suffice to select the viewing cone.
The orbit-closure hypothesis is discharged by the finite table in the assembler. -/
namespace Phinopert
noncomputable def phi : ℝ := (1+Real.sqrt 5)/2
def wallRaw : List IQ := [((0,0),(4,0),(0,0),(0,0)),
  ((0,0),(0,0),(4,0),(0,0)),((0,0),(-2,0),(-1,-1),(-1,1))]
theorem wall_raw_check : wallRaw.all (fun q => decide (q ∈ icoSignedRaw))=true := by decide
noncomputable def wallNormal : Fin 3 → Point
  | 0 => (1,0,0)
  | 1 => (0,1,0)
  | 2 => (-1/2,-(1+Real.sqrt 5)/4,(-1+Real.sqrt 5)/4)

theorem actual_wall_membership (i : Fin 3) : (0,wallNormal i) ∈ icoReal (Real.sqrt 5) := by
  have hall : ∀ q ∈ wallRaw.map (iqEval (Real.sqrt 5)), q ∈ icoReal (Real.sqrt 5) := by
    intro q hq
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hq
    exact (mem_icoReal_iff _ _).mpr
      ⟨p,of_decide_eq_true ((List.all_eq_true.mp wall_raw_check) p hp),rfl⟩
  fin_cases i <;> apply hall <;> simp [wallRaw,wallNormal,iqEval,ieval] <;> ring <;> simp

theorem actual_wall_orientation (i : Fin 3) : 0 < dot (1,2,9) (wallNormal i) := by
  have hb := (root5_bounds _ sqrt5_spec.1 sqrt5_spec.2).1
  fin_cases i <;> simp [wallNormal,dot] <;> linarith

theorem pure_quaternion_action (n p : Point) :
    qAction (0,n) p = (2*dot n p) • n - (dot n n) • p := by
  ext <;> simp [qAction,dot] <;> ring

theorem unit_pure_mirror (n p : Point) (hn : qNormSq (0,n)=1) :
    mirror n p = -qAction (0,n) p := by
  have hd : dot n n=1 := by simpa [qNormSq,dot,pow_two] using hn
  rw [pure_quaternion_action]
  simp [mirror,hd]

noncomputable def icoViewOrbit (u : Point) : Finset Point := by
  classical
  exact (icoReal (Real.sqrt 5)).image (fun q => qAction q u) ∪
    (icoReal (Real.sqrt 5)).image (fun q => -qAction q u)

theorem mem_icoViewOrbit (u v : Point) : v ∈ icoViewOrbit u ↔
    (∃ q ∈ icoReal (Real.sqrt 5), qAction q u=v) ∨
    (∃ q ∈ icoReal (Real.sqrt 5), -qAction q u=v) := by
  classical
  simp [icoViewOrbit]

theorem icoViewOrbit_nonempty (u : Point) : (icoViewOrbit u).Nonempty := by
  refine ⟨u,(mem_icoViewOrbit u u).mpr (Or.inl ?_)⟩
  exact ⟨(1,0),icoReal_one_mem _,qAction_one u⟩

theorem qAction_neg_point (q : QuaternionCoords) (u : Point) : qAction q (-u)= -qAction q u := by
  ext <;> simp [qAction] <;> ring

theorem icoViewOrbit_wall_closed
    (hc : ∀ p ∈ icoReal (Real.sqrt 5), ∀ q ∈ icoReal (Real.sqrt 5),
      qProduct p q ∈ icoReal (Real.sqrt 5))
    (u : Point) (i : Fin 3) {v : Point} (hv : v ∈ icoViewOrbit u) :
    mirror (wallNormal i) v ∈ icoViewOrbit u := by
  have hi := actual_wall_membership i
  rw [unit_pure_mirror _ _ (icoReal_unit _ sqrt5_spec.1 hi)]
  rcases (mem_icoViewOrbit u v).mp hv with ⟨q,hq,rfl⟩ | ⟨q,hq,rfl⟩
  · apply (mem_icoViewOrbit _ _).mpr
    exact Or.inr ⟨qProduct (0,wallNormal i) q,hc _ hi _ hq,
      congrArg Neg.neg (qAction_product _ _ u)⟩
  · rw [qAction_neg_point,neg_neg]
    apply (mem_icoViewOrbit _ _).mpr
    exact Or.inl ⟨qProduct (0,wallNormal i) q,hc _ hi _ hq,qAction_product _ _ u⟩

theorem three_wall_cone (u : Point) (h : ∀ i : Fin 3, 0 ≤ dot (wallNormal i) u) :
    0 ≤ u.1 ∧ 0 ≤ u.2.1 ∧ phi*u.1+phi^2*u.2.1 ≤ u.2.2 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  simp [wallNormal,dot] at h0 h1
  refine ⟨h0,h1,?_⟩
  have hs := sqrt5_spec.1
  have hlo := (root5_bounds _ hs sqrt5_spec.2).1
  have he : dot (wallNormal 2) u = ((Real.sqrt 5-1)/4)*
      (u.2.2-phi*u.1-phi^2*u.2.1) := by
    dsimp [dot,wallNormal,phi]
    have hs2 : (Real.sqrt 5)^2=5 := by nlinarith
    have hs3 : (Real.sqrt 5)^3=5*Real.sqrt 5 := by rw [pow_succ,hs2]
    ring_nf
    rw [hs2,hs3]
    ring
  rw [he] at h2
  have hp : 0 < (Real.sqrt 5-1)/4 := by linarith
  have := (mul_nonneg_iff_of_pos_left hp).mp h2
  linarith

theorem actual_view_cone_representative
    (hc : ∀ p ∈ icoReal (Real.sqrt 5), ∀ q ∈ icoReal (Real.sqrt 5),
      qProduct p q ∈ icoReal (Real.sqrt 5)) (u : Point) :
    ∃ v ∈ icoViewOrbit u, 0 ≤ v.1 ∧ 0 ≤ v.2.1 ∧ phi*v.1+phi^2*v.2.1 ≤ v.2.2 := by
  obtain ⟨v,hv,hm⟩ := finite_maximiser (icoViewOrbit u) (icoViewOrbit_nonempty u) (dot (1,2,9))
  refine ⟨v,hv,three_wall_cone v ?_⟩
  intro i
  exact maximal_reflection_halfspace _ _ _ (actual_wall_orientation i)
    (hm _ (icoViewOrbit_wall_closed hc u i hv))

theorem icoViewOrbit_nonzero (u : Point) (hu : u ≠ 0) {v : Point}
    (hv : v ∈ icoViewOrbit u) : v ≠ 0 := by
  have hp := dot_self_positive u hu
  have hq : ∀ q ∈ icoReal (Real.sqrt 5), qAction q u ≠ 0 := by
    intro q hq hz
    have he := icoReal_action_dot _ sqrt5_spec.1 hq u u
    rw [hz] at he
    norm_num [dot] at he
    dsimp [dot] at hp
    linarith
  rcases (mem_icoViewOrbit u v).mp hv with ⟨q,hmem,rfl⟩ | ⟨q,hmem,rfl⟩
  · exact hq q hmem
  · exact neg_ne_zero.mpr (hq q hmem)

/-- Every nonzero view, including one initially in the xy-plane, has a
signed icosahedral image with positive height and coordinates in the view box.
No claim about preservation of a physical fit is built into this theorem. -/
theorem actual_view_box_representative
    (hc : ∀ p ∈ icoReal (Real.sqrt 5), ∀ q ∈ icoReal (Real.sqrt 5),
      qProduct p q ∈ icoReal (Real.sqrt 5)) (u : Point) (hu : u ≠ 0) :
    ∃ v ∈ icoViewOrbit u, 0 < v.2.2 ∧
      0 ≤ v.1/v.2.2 ∧ v.1/v.2.2 ≤ 2/3 ∧
      0 ≤ v.2.1/v.2.2 ∧ v.2.1/v.2.2 ≤ 2/5 ∧
      phi*(v.1/v.2.2)+phi^2*(v.2.1/v.2.2) ≤ 1 := by
  obtain ⟨v,hv,hx,hy,hz⟩ := actual_view_cone_representative hc u
  have hφ : 0 < phi := by dsimp [phi]; nlinarith [sqrt5_spec.2]
  have hn := icoViewOrbit_nonzero u hu hv
  have hp := cone_height_positive phi hφ v hn hx hy hz
  obtain ⟨hs,ht,hcone⟩ := normalise_view_cone phi hφ v hn hx hy hz
  have hb := view_cone_box (Real.sqrt 5) _ _ sqrt5_spec.1 sqrt5_spec.2 hs ht hcone
  exact ⟨v,hv,hp,hs,hb.1,ht,hb.2,hcone⟩

end Phinopert
#print axioms Phinopert.wall_raw_check
#print axioms Phinopert.actual_wall_membership
#print axioms Phinopert.actual_wall_orientation
#print axioms Phinopert.pure_quaternion_action
#print axioms Phinopert.unit_pure_mirror
#print axioms Phinopert.mem_icoViewOrbit
#print axioms Phinopert.icoViewOrbit_nonempty
#print axioms Phinopert.qAction_neg_point
#print axioms Phinopert.icoViewOrbit_wall_closed
#print axioms Phinopert.three_wall_cone
#print axioms Phinopert.actual_view_cone_representative
#print axioms Phinopert.icoViewOrbit_nonzero
#print axioms Phinopert.actual_view_box_representative
