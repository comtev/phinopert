import Geometry
import Mathlib.Data.Finset.Max

/-!
Continuous and order-theoretic components of representative selection.
Finite orbit closure, the icosahedral reflection list, quaternion completeness,
and invariance of the containment problem are still separate obligations.
-/
namespace Phinopert

theorem finite_maximiser {α : Type*} (S : Finset α) (hS : S.Nonempty)
    (score : α → ℝ) : ∃ x ∈ S, ∀ y ∈ S, score y ≤ score x :=
  S.exists_max_image score hS

noncomputable def mirror (n u : Point) : Point :=
  u - (2*dot n u / dot n n) • n

theorem dot_self_positive (n : Point) (hn : n ≠ 0) : 0 < dot n n := by
  have h0 := sq_nonneg n.1
  have h1 := sq_nonneg n.2.1
  have h2 := sq_nonneg n.2.2
  by_contra h
  have hle : dot n n ≤ 0 := le_of_not_gt h
  dsimp [dot] at hle
  have e0 : n.1=0 := by nlinarith
  have e1 : n.2.1=0 := by nlinarith
  have e2 : n.2.2=0 := by nlinarith
  apply hn
  ext <;> simp [e0,e1,e2]

theorem mirror_score (h n u : Point) :
    dot h (mirror n u) = dot h u - (2*dot n u / dot n n)*dot h n := by
  simp [mirror, dot]; ring

theorem maximal_reflection_halfspace (h n u : Point)
    (hn : 0 < dot h n) (hmax : dot h (mirror n u) ≤ dot h u) : 0 ≤ dot n u := by
  have hn0 : n ≠ 0 := by
    intro he
    subst n
    simp [dot] at hn
  have hnn := dot_self_positive n hn0
  rw [mirror_score] at hmax
  have hp : 0 ≤ (2*dot n u/dot n n)*dot h n := by linarith
  have hq : 0 ≤ 2*dot n u/dot n n := (mul_nonneg_iff_of_pos_right hn).mp hp
  have hm := mul_nonneg hq (le_of_lt hnn)
  rw [div_mul_cancel₀ _ (ne_of_gt hnn)] at hm
  linarith

/-- The maximiser lies in every oriented reflection halfspace whenever the
finite candidate set is closed under those reflections. Closure is explicit. -/
theorem finite_reflection_representative (S : Finset Point) (hS : S.Nonempty)
    (N : Set Point) (h : Point) (horient : ∀ n ∈ N, 0 < dot h n)
    (hclosed : ∀ n ∈ N, ∀ u ∈ S, mirror n u ∈ S) :
    ∃ u ∈ S, ∀ n ∈ N, 0 ≤ dot n u := by
  obtain ⟨u,hu,hm⟩ := finite_maximiser S hS (dot h)
  exact ⟨u,hu,fun n hn => maximal_reflection_halfspace h n u
    (horient n hn) (hm _ (hclosed n hn u hu))⟩

theorem cone_height_positive (φ : ℝ) (hφ : 0 < φ) (u : Point)
    (hu : u ≠ 0) (hx : 0 ≤ u.1) (hy : 0 ≤ u.2.1)
    (hz : φ*u.1+φ^2*u.2.1 ≤ u.2.2) : 0 < u.2.2 := by
  have hφ2 : 0 < φ^2 := pow_pos hφ _
  have hxφ := mul_nonneg (le_of_lt hφ) hx
  have hyφ := mul_nonneg (le_of_lt hφ2) hy
  by_contra h
  have hle := le_of_not_gt h
  have ez : u.2.2=0 := by linarith
  have ex : u.1=0 := by nlinarith
  have ey : u.2.1=0 := by nlinarith
  apply hu
  ext <;> simp [ex,ey,ez]

theorem normalise_view_cone (φ : ℝ) (hφ : 0 < φ) (u : Point)
    (hu : u ≠ 0) (hx : 0 ≤ u.1) (hy : 0 ≤ u.2.1)
    (hz : φ*u.1+φ^2*u.2.1 ≤ u.2.2) :
    0 ≤ u.1/u.2.2 ∧ 0 ≤ u.2.1/u.2.2 ∧
    φ*(u.1/u.2.2)+φ^2*(u.2.1/u.2.2) ≤ 1 := by
  have hp := cone_height_positive φ hφ u hu hx hy hz
  refine ⟨div_nonneg hx hp.le, div_nonneg hy hp.le, ?_⟩
  rw [← mul_div_assoc, ← mul_div_assoc, ← add_div]
  exact (div_le_one hp).mpr hz

theorem view_cone_box (q s t : ℝ) (hq : q*q=5) (hpos : 0 ≤ q)
    (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hcone : ((1+q)/2)*s+((1+q)/2)^2*t ≤ 1) :
    s ≤ 2/3 ∧ t ≤ 2/5 := by
  have hb := (root5_bounds q hq hpos).1
  have he : ((1+q)/2)^2 = (3+q)/2 := by nlinarith [hq]
  rw [he] at hcone
  have hqs := mul_nonneg (show 0 ≤ q-2 by linarith) hs
  have hqt := mul_nonneg (show 0 ≤ q-2 by linarith) ht
  constructor <;> nlinarith

/-- Signed coordinate competitors and the unit norm prevent the chosen
quaternion scalar from vanishing; this includes original half-turns. -/
theorem quaternion_scalar_lower_bound (a x y z : ℝ)
    (hunit : a*a+x*x+y*y+z*z=1) (ha : 0 ≤ a)
    (hx : -a ≤ x ∧ x ≤ a) (hy : -a ≤ y ∧ y ≤ a)
    (hz : -a ≤ z ∧ z ≤ a) : 1/2 ≤ a := by
  have hxx := mul_nonneg (sub_nonneg.mpr hx.2) (show 0 ≤ a+x by linarith [hx.1])
  have hyy := mul_nonneg (sub_nonneg.mpr hy.2) (show 0 ≤ a+y by linarith [hy.1])
  have hzz := mul_nonneg (sub_nonneg.mpr hz.2) (show 0 ≤ a+z by linarith [hz.1])
  by_contra h
  have hlt := lt_of_not_ge h
  have hp := mul_pos (show 0 < 1/2-a by linarith) (show 0 < 1/2+a by linarith)
  nlinarith

theorem signed_pair_bound (φ x y : ℝ)
    (hpp : x+(φ-1)*y ≤ 2-φ) (hpm : x-(φ-1)*y ≤ 2-φ)
    (hmp : -x+(φ-1)*y ≤ 2-φ) (hmm : -x-(φ-1)*y ≤ 2-φ) :
    -(2-φ) ≤ x ∧ x ≤ 2-φ := by constructor <;> linarith

/-- Abstract finite quaternion selection. The finite group still has to supply
all signed coordinate competitors; no such membership is postulated globally. -/
theorem finite_quaternion_representative (S : Finset (ℝ × Point)) (hS : S.Nonempty)
    (hunit : ∀ p ∈ S, p.1*p.1+p.2.1*p.2.1+p.2.2.1*p.2.2.1+p.2.2.2*p.2.2.2=1)
    (hcomp : ∀ p ∈ S, ∀ c ∈ ([p.1,p.2.1,p.2.2.1,p.2.2.2] : List ℝ),
      (∃ q ∈ S, q.1=c) ∧ (∃ q ∈ S, q.1= -c)) :
    ∃ p ∈ S, 1/2 ≤ p.1 ∧ ∀ q ∈ S, q.1 ≤ p.1 := by
  obtain ⟨p,hp,hm⟩ := finite_maximiser S hS Prod.fst
  have hb : ∀ c ∈ ([p.1,p.2.1,p.2.2.1,p.2.2.2] : List ℝ), -p.1 ≤ c ∧ c ≤ p.1 := by
    intro c hc
    obtain ⟨⟨q,hq,he⟩,⟨q',hq',he'⟩⟩ := hcomp p hp c hc
    have hplus := hm q hq
    have hminus := hm q' hq'
    rw [he] at hplus
    rw [he'] at hminus
    exact ⟨by linarith, hplus⟩
  have ha := (hb p.1 (by simp)).1
  refine ⟨p,hp,?_,hm⟩
  exact quaternion_scalar_lower_bound _ _ _ _ (hunit p hp) (by linarith)
    (hb _ (by simp)) (hb _ (by simp)) (hb _ (by simp))

theorem squared_fold_bound (s t L : ℝ)
    (hp : L ≤ Real.sqrt (1+s^2+t^2))
    (hm : -L ≤ Real.sqrt (1+s^2+t^2)) : L^2 ≤ 1+s^2+t^2 := by
  have hs : 0 ≤ 1+s^2+t^2 := by nlinarith [sq_nonneg s, sq_nonneg t]
  have he := Real.sq_sqrt hs
  have hh := mul_nonneg (sub_nonneg.mpr hp)
    (show 0 ≤ Real.sqrt (1+s^2+t^2)+L by linarith)
  nlinarith

theorem cayley_coordinate_box (q x : ℝ) (hq : q*q=5) (hpos : 0 ≤ q)
    (hx : -(2-(1+q)/2) ≤ x ∧ x ≤ 2-(1+q)/2) : -2/5 ≤ x ∧ x ≤ 2/5 := by
  have hqlo : 11/5 < q := by
    by_contra h
    have hl : q ≤ 11/5 := le_of_not_gt h
    have hm := mul_nonneg (sub_nonneg.mpr hl) (show 0 ≤ 11/5+q by linarith)
    nlinarith
  constructor <;> linarith [hx.1,hx.2]

end Phinopert

#print axioms Phinopert.finite_maximiser
#print axioms Phinopert.dot_self_positive
#print axioms Phinopert.mirror_score
#print axioms Phinopert.maximal_reflection_halfspace
#print axioms Phinopert.finite_reflection_representative
#print axioms Phinopert.cone_height_positive
#print axioms Phinopert.normalise_view_cone
#print axioms Phinopert.view_cone_box
#print axioms Phinopert.quaternion_scalar_lower_bound
#print axioms Phinopert.signed_pair_bound
#print axioms Phinopert.cayley_coordinate_box
#print axioms Phinopert.finite_quaternion_representative
#print axioms Phinopert.squared_fold_bound
