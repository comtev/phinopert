import SupportBodyData

namespace Phinopert

noncomputable def supportNormal (a b c : Point) (s t : ℝ) : Point := s • a+t • b+c
noncomputable def supportHeight (n : Point) (p : ZPoint) : ℝ := dot n (bodyEval p)

theorem affine_interval_nonneg (f : ℝ → ℝ)
    (hf : ∀ x y t, f ((1-t)*x+t*y)=(1-t)*f x+t*f y)
    (lo hi x : ℝ) (hx : lo ≤ x ∧ x ≤ hi) (hl : 0 ≤ f lo) (hh : 0 ≤ f hi) :
    0 ≤ f x := by
  by_cases he : lo=hi
  · have : x=lo := by linarith
    simpa [this] using hl
  have hlt : lo < hi := lt_of_le_of_ne (hx.1.trans hx.2) he
  have hd : 0 < hi-lo := by linarith
  let u := (x-lo)/(hi-lo)
  have hu : 0 ≤ u := div_nonneg (sub_nonneg.mpr hx.1) (le_of_lt hd)
  have hU : u ≤ 1 := (div_le_one hd).mpr (by linarith)
  have hm : (1-u)*lo+u*hi=x := by dsimp [u]; field_simp <;> ring
  have h := add_nonneg (mul_nonneg (show 0 ≤ 1-u by linarith) hl) (mul_nonneg hu hh)
  rwa [← hf,hm] at h

theorem affine_interval_positive (f : ℝ → ℝ)
    (hf : ∀ x y t, f ((1-t)*x+t*y)=(1-t)*f x+t*f y)
    (lo hi x : ℝ) (hx : lo ≤ x ∧ x ≤ hi) (hl : 0 < f lo) (hh : 0 < f hi) :
    0 < f x := by
  have h := fold_safe_between f (fun _ => (0,0,0)) hf (by intros; ext <;> simp)
    lo hi x hx (by exact ⟨hl,by simp [dot]; nlinarith [sq_pos_of_pos hl]⟩)
    (by exact ⟨hh,by simp [dot]; nlinarith [sq_pos_of_pos hh]⟩)
  exact h.1

theorem normal_rectangle_support (a b c p q : Point) (sl sh tl th s t : ℝ)
    (hs : sl ≤ s ∧ s ≤ sh) (ht : tl ≤ t ∧ t ≤ th)
    (hc : ∀ x, Endpoint sl sh x → ∀ y, Endpoint tl th y →
      dot (supportNormal a b c x y) q ≤ dot (supportNormal a b c x y) p) :
    dot (supportNormal a b c s t) q ≤ dot (supportNormal a b c s t) p := by
  suffices h : 0 ≤ dot (supportNormal a b c s t) p-dot (supportNormal a b c s t) q by linarith
  apply affine_interval_nonneg (fun x => dot (supportNormal a b c x t) p-dot (supportNormal a b c x t) q)
    (by intros; dsimp [supportNormal,dot]; ring) sl sh s hs
  all_goals
    apply affine_interval_nonneg (fun y => dot (supportNormal a b c _ y) p-dot (supportNormal a b c _ y) q)
      (by intros; dsimp [supportNormal,dot]; ring) tl th t ht
    all_goals linarith [hc sl (Or.inl rfl) tl (Or.inl rfl),hc sl (Or.inl rfl) th (Or.inr rfl),hc sh (Or.inr rfl) tl (Or.inl rfl),hc sh (Or.inr rfl) th (Or.inr rfl)]

def pointCoord (p : Point) (i : Fin 3) : ℝ := ![p.1,p.2.1,p.2.2] i

theorem normal_rectangle_nonzero (a b c : Point) (i : Fin 3) (e : ℝ)
    (sl sh tl th s t : ℝ) (hs : sl ≤ s ∧ s ≤ sh) (ht : tl ≤ t ∧ t ≤ th)
    (hc : ∀ x, Endpoint sl sh x → ∀ y, Endpoint tl th y →
      0 < e*pointCoord (supportNormal a b c x y) i) :
    supportNormal a b c s t ≠ 0 := by
  have hpos : 0 < e*pointCoord (supportNormal a b c s t) i := by
    apply affine_interval_positive (fun x => e*pointCoord (supportNormal a b c x t) i)
      (by intros; fin_cases i <;> dsimp [supportNormal,pointCoord] <;> ring) sl sh s hs
    all_goals
      apply affine_interval_positive (fun y => e*pointCoord (supportNormal a b c _ y) i)
        (by intros; fin_cases i <;> dsimp [supportNormal,pointCoord] <;> ring) tl th t ht
      all_goals first | exact hc sl (Or.inl rfl) tl (Or.inl rfl) | exact hc sl (Or.inl rfl) th (Or.inr rfl) | exact hc sh (Or.inr rfl) tl (Or.inl rfl) | exact hc sh (Or.inr rfl) th (Or.inr rfl)
  intro hn
  rw [hn] at hpos
  have hz : pointCoord (0:Point) i=0 := by fin_cases i <;> rfl
  rw [hz,mul_zero] at hpos
  exact (lt_irrefl 0) hpos

theorem body_support_scaled (n : ZPoint) (p : ZPoint) (scale : ℝ) (a : Point)
    (hc : ∀ q ∈ bodyZPoints, ZNonneg (zdot n (zpsub p q)))
    (hscale : 0 < scale) (he : zpoint n=scale • a) :
    ∀ q ∈ VertexSet (Real.sqrt 5), dot a q ≤ dot a (bodyEval p) := by
  intro q hq
  have h := body_support_at_z5 n p hc q hq
  rw [he] at h
  have hm (v : Point) : dot (scale • a) v=scale*dot a v := by dsimp [dot]; ring
  rw [hm,hm] at h
  exact (mul_le_mul_left hscale).mp h

end Phinopert
#print axioms Phinopert.affine_interval_nonneg
#print axioms Phinopert.affine_interval_positive
#print axioms Phinopert.normal_rectangle_support
#print axioms Phinopert.normal_rectangle_nonzero
#print axioms Phinopert.body_support_scaled
