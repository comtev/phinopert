
import FoldGeometry

namespace Phinopert

noncomputable def foldLinear (q : QuaternionCoords) (s t x y z : ℝ) : ℝ :=
  -q.1*dot (s,t,1) (x,y,z)-dot q.2 ((s,t,1)+cross3 (s,t,1) (x,y,z))

def Endpoint (lo hi x : ℝ) : Prop := x=lo ∨ x=hi

theorem fold_safe_endpoints (f : ℝ → ℝ) (g : ℝ → Point)
    (hf : ∀ x y t, f ((1-t)*x+t*y) = (1-t)*f x+t*f y)
    (hg : ∀ x y t, g ((1-t)*x+t*y) = (1-t) • g x+t • g y)
    (lo hi x : ℝ) (hx : lo ≤ x ∧ x ≤ hi)
    (hc : ∀ v, Endpoint lo hi v → FoldSafe (f v) (g v)) :
    FoldSafe (f x) (g x) :=
  fold_safe_between f g hf hg lo hi x hx (hc lo (Or.inl rfl)) (hc hi (Or.inr rfl))

theorem fold_safe_axis_s (q : QuaternionCoords) (e s t x y z lo hi : ℝ)
    (hx : lo ≤ s ∧ s ≤ hi)
    (hc : ∀ v, Endpoint lo hi v →
      FoldSafe (e*foldLinear q v t x y z) (v,t,1)) :
    FoldSafe (e*foldLinear q s t x y z) (s,t,1) := by
  apply fold_safe_endpoints (fun v => e*foldLinear q v t x y z)
    (fun v => (v,t,1)) ?_ ?_ lo hi s hx hc
  · intros; dsimp [foldLinear,dot,cross3]; ring
  · intros; ext <;> dsimp <;> ring

theorem fold_safe_axis_t (q : QuaternionCoords) (e s t x y z lo hi : ℝ)
    (hx : lo ≤ t ∧ t ≤ hi)
    (hc : ∀ v, Endpoint lo hi v →
      FoldSafe (e*foldLinear q s v x y z) (s,v,1)) :
    FoldSafe (e*foldLinear q s t x y z) (s,t,1) := by
  apply fold_safe_endpoints (fun v => e*foldLinear q s v x y z)
    (fun v => (s,v,1)) ?_ ?_ lo hi t hx hc
  · intros; dsimp [foldLinear,dot,cross3]; ring
  · intros; ext <;> dsimp <;> ring

theorem fold_safe_axis_x (q : QuaternionCoords) (e s t x y z lo hi : ℝ)
    (hx : lo ≤ x ∧ x ≤ hi)
    (hc : ∀ v, Endpoint lo hi v →
      FoldSafe (e*foldLinear q s t v y z) (s,t,1)) :
    FoldSafe (e*foldLinear q s t x y z) (s,t,1) := by
  apply fold_safe_endpoints (fun v => e*foldLinear q s t v y z)
    (fun v => (s,t,1)) ?_ ?_ lo hi x hx hc
  · intros; dsimp [foldLinear,dot,cross3]; ring
  · intros; ext <;> dsimp <;> ring

theorem fold_safe_axis_y (q : QuaternionCoords) (e s t x y z lo hi : ℝ)
    (hx : lo ≤ y ∧ y ≤ hi)
    (hc : ∀ v, Endpoint lo hi v →
      FoldSafe (e*foldLinear q s t x v z) (s,t,1)) :
    FoldSafe (e*foldLinear q s t x y z) (s,t,1) := by
  apply fold_safe_endpoints (fun v => e*foldLinear q s t x v z)
    (fun v => (s,t,1)) ?_ ?_ lo hi y hx hc
  · intros; dsimp [foldLinear,dot,cross3]; ring
  · intros; ext <;> dsimp <;> ring

theorem fold_safe_axis_z (q : QuaternionCoords) (e s t x y z lo hi : ℝ)
    (hx : lo ≤ z ∧ z ≤ hi)
    (hc : ∀ v, Endpoint lo hi v →
      FoldSafe (e*foldLinear q s t x y v) (s,t,1)) :
    FoldSafe (e*foldLinear q s t x y z) (s,t,1) := by
  apply fold_safe_endpoints (fun v => e*foldLinear q s t x y v)
    (fun v => (s,t,1)) ?_ ?_ lo hi z hx hc
  · intros; dsimp [foldLinear,dot,cross3]; ring
  · intros; ext <;> dsimp <;> ring

/-- Multi-affine interpolation in all five coordinates. A single common sign
is essential; positivity of squared corner values alone is insufficient. -/
theorem fold_safe_box (q : QuaternionCoords) (e : ℝ) (b : RationalBox)
    (hc : ∀ s, Endpoint (b 0).1 (b 0).2 s →
      ∀ t, Endpoint (b 1).1 (b 1).2 t →
      ∀ x, Endpoint (b 2).1 (b 2).2 x →
      ∀ y, Endpoint (b 3).1 (b 3).2 y →
      ∀ z, Endpoint (b 4).1 (b 4).2 z →
      FoldSafe (e*foldLinear q s t x y z) (s,t,1))
    (s t : ℝ) (r : Point) (hb : InClosedBox b s t r) :
    FoldSafe (e*foldLinear q s t r.1 r.2.1 r.2.2) (s,t,1) := by
  apply fold_safe_axis_s q e s t r.1 r.2.1 r.2.2 _ _ (hb 0)
  intro s hs
  apply fold_safe_axis_t q e s t r.1 r.2.1 r.2.2 _ _ (hb 1)
  intro t ht
  apply fold_safe_axis_x q e s t r.1 r.2.1 r.2.2 _ _ (hb 2)
  intro x hx
  apply fold_safe_axis_y q e s t x r.2.1 r.2.2 _ _ (hb 3)
  intro y hy
  apply fold_safe_axis_z q e s t x y r.2.2 _ _ (hb 4)
  intro z hz
  exact hc s hs t ht x hx y hy z hz

theorem fold_domain_nonpositive (s t : ℝ) (r : Point) (hd : InIcoDomain s t r)
    (raw : IQ) (hraw : raw ∈ icoRaw) :
    foldValue s t r (iqEval (Real.sqrt 5) raw) ≤ 0 := by
  apply hd.2.2.2.2.2.2.2
  apply List.mem_append_right
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨raw,hraw,rfl⟩

theorem fold_safe_excludes_domain (raw : IQ) (hraw : raw ∈ icoRaw)
    (e : ℝ) (he : e^2=1) (s t : ℝ) (r : Point)
    (h : FoldSafe (e*foldLinear (iqEval (Real.sqrt 5) raw) s t r.1 r.2.1 r.2.2) (s,t,1)) :
    ¬ InIcoDomain s t r := by
  intro hd
  have hn := fold_domain_nonpositive s t r hd raw hraw
  have hh := h.2
  rw [mul_pow,he,one_mul] at hh
  dsimp [foldValue,foldLinear,dot] at hn hh
  nlinarith

theorem sqrt5_affine_positive (a b : ℚ)
    (h : 0 < (a-b)+(2*b)*(if 0 ≤ 2*b then phiLower else phiUpper)) :
    0 < (a:ℝ)+(b:ℝ)*Real.sqrt 5 := by
  have hp := affine_phi_positive (a-b) (2*b) h
  push_cast at hp
  dsimp [phi] at hp
  nlinarith

theorem fold_safe_exact_corner (a b s t : ℚ)
    (hp : 0 < (a-b)+(2*b)*(if 0 ≤ 2*b then phiLower else phiUpper))
    (hg : 0 < (a*a+5*b*b-1-s*s-t*t-2*a*b)+(4*a*b)*
      (if 0 ≤ 4*a*b then phiLower else phiUpper)) :
    FoldSafe ((a:ℝ)+(b:ℝ)*Real.sqrt 5) ((s:ℝ),(t:ℝ),1) := by
  have hpos := sqrt5_affine_positive a b hp
  have hgap := sqrt5_affine_positive (a*a+5*b*b-1-s*s-t*t) (2*a*b)
    (by simpa only [show 2*(2*a*b)=4*a*b by ring] using hg)
  push_cast at hgap
  have he : ((a:ℝ)+(b:ℝ)*Real.sqrt 5)^2 =
      (a:ℝ)^2+5*(b:ℝ)^2+2*(a:ℝ)*(b:ℝ)*Real.sqrt 5 := by
    calc
      _ = (a:ℝ)^2+(b:ℝ)^2*(Real.sqrt 5*Real.sqrt 5)+
        2*(a:ℝ)*(b:ℝ)*Real.sqrt 5 := by ring
      _ = _ := by rw [sqrt5_spec.1]; ring
  refine ⟨hpos, ?_⟩
  dsimp [dot]
  linarith

end Phinopert
#print axioms Phinopert.fold_safe_endpoints
#print axioms Phinopert.fold_safe_axis_s
#print axioms Phinopert.fold_safe_axis_t
#print axioms Phinopert.fold_safe_axis_x
#print axioms Phinopert.fold_safe_axis_y
#print axioms Phinopert.fold_safe_axis_z
#print axioms Phinopert.fold_safe_box
#print axioms Phinopert.fold_domain_nonpositive
#print axioms Phinopert.fold_safe_excludes_domain
#print axioms Phinopert.sqrt5_affine_positive
#print axioms Phinopert.fold_safe_exact_corner

