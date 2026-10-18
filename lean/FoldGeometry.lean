import CertificateBoxes

namespace Phinopert

/-- The positive, open Euclidean Lorentz cone. The product norm on `Point`
is deliberately not used: it is not the Euclidean norm. -/
def FoldSafe (a : ℝ) (u : Point) : Prop := 0 < a ∧ dot u u < a^2

theorem dot_self_nonneg_fold (u : Point) : 0 ≤ dot u u := by
  dsimp [dot]
  nlinarith [sq_nonneg u.1, sq_nonneg u.2.1, sq_nonneg u.2.2]

theorem fold_safe_cross_bound (a b : ℝ) (u v : Point)
    (ha : FoldSafe a u) (hb : FoldSafe b v) : dot u v ≤ a*b := by
  have hc := dot_self_nonneg_fold (cross3 u v)
  rw [dot_cross_self] at hc
  have hu := dot_self_nonneg_fold u
  have hv := dot_self_nonneg_fold v
  have hm := mul_nonneg (le_of_lt (sub_pos.mpr ha.2)) hv
  have hn := mul_nonneg (sq_nonneg a) (le_of_lt (sub_pos.mpr hb.2))
  have hab : 0 < a*b := mul_pos ha.1 hb.1
  by_contra h
  have ht : a*b < dot u v := lt_of_not_ge h
  have hp := mul_pos (sub_pos.mpr ht) (show 0 < dot u v+a*b by linarith)
  nlinarith

theorem fold_safe_mix (a b : ℝ) (u v : Point) (t : ℝ)
    (ha : FoldSafe a u) (hb : FoldSafe b v) (ht : 0 ≤ t) (hT : t ≤ 1) :
    FoldSafe ((1-t)*a+t*b) ((1-t) • u+t • v) := by
  have hcross := fold_safe_cross_bound a b u v ha hb
  have hpos : 0 < (1-t)*a+t*b := by
    by_cases he : t = 1
    · subst t; simpa using hb.1
    · have hlt : t < 1 := lt_of_le_of_ne hT he
      have := mul_pos (show 0 < 1-t by linarith) ha.1
      have := mul_nonneg ht (le_of_lt hb.1)
      nlinarith
  refine ⟨hpos, ?_⟩
  have hid : ((1-t)*a+t*b)^2-dot ((1-t) • u+t • v) ((1-t) • u+t • v) =
      (1-t)^2*(a^2-dot u u)+t^2*(b^2-dot v v)+2*t*(1-t)*(a*b-dot u v) := by
    dsimp [dot]; ring
  have h1 := mul_nonneg (sq_nonneg t) (le_of_lt (sub_pos.mpr hb.2))
  have h2 := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) ht)
    (show 0 ≤ 1-t by linarith)) (sub_nonneg.mpr hcross)
  by_cases he : t = 1
  · subst t; simpa using hb.2
  · have hlt : t < 1 := lt_of_le_of_ne hT he
    have h3 := mul_pos (sq_pos_of_pos (show 0 < 1-t by linarith)) (sub_pos.mpr ha.2)
    linarith

/-- Affine interpolation includes both faces and also zero-width intervals. -/
theorem fold_safe_between (f : ℝ → ℝ) (g : ℝ → Point)
    (hf : ∀ x y t, f ((1-t)*x+t*y) = (1-t)*f x+t*f y)
    (hg : ∀ x y t, g ((1-t)*x+t*y) = (1-t) • g x+t • g y)
    (lo hi x : ℝ) (hx : lo ≤ x ∧ x ≤ hi)
    (hl : FoldSafe (f lo) (g lo)) (hh : FoldSafe (f hi) (g hi)) :
    FoldSafe (f x) (g x) := by
  by_cases he : lo = hi
  · have : x = lo := by linarith
    simpa [this] using hl
  have hlt : lo < hi := lt_of_le_of_ne (hx.1.trans hx.2) he
  have hd : 0 < hi-lo := by linarith
  let t := (x-lo)/(hi-lo)
  have ht : 0 ≤ t := div_nonneg (sub_nonneg.mpr hx.1) (le_of_lt hd)
  have hT : t ≤ 1 := (div_le_one hd).mpr (by linarith)
  have hx' : (1-t)*lo+t*hi = x := by
    dsimp [t]
    field_simp
    <;> ring
  have h := fold_safe_mix (f lo) (f hi) (g lo) (g hi) t hl hh ht hT
  rwa [← hf, ← hg, hx'] at h

end Phinopert
#print axioms Phinopert.dot_self_nonneg_fold
#print axioms Phinopert.fold_safe_cross_bound
#print axioms Phinopert.fold_safe_mix
#print axioms Phinopert.fold_safe_between
