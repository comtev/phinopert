import FoldBox

namespace Phinopert

abbrev Z5 := ℤ × ℤ
abbrev ZPoint := Z5 × Z5 × Z5
def zadd (a b : Z5) : Z5 := (a.1+b.1,a.2+b.2)
def zneg (a : Z5) : Z5 := (-a.1,-a.2)
def zsub (a b : Z5) : Z5 := zadd a (zneg b)
def zmul (a b : Z5) : Z5 := (a.1*b.1+5*a.2*b.2,a.1*b.2+a.2*b.1)
noncomputable def zeval (a : Z5) : ℝ := a.1+a.2*Real.sqrt 5
noncomputable def zpoint (a : ZPoint) : Point := (zeval a.1,zeval a.2.1,zeval a.2.2)
def zpsub (a b : ZPoint) : ZPoint := (zsub a.1 b.1,zsub a.2.1 b.2.1,zsub a.2.2 b.2.2)
def zdot (a b : ZPoint) : Z5 := zadd (zmul a.1 b.1) (zadd (zmul a.2.1 b.2.1) (zmul a.2.2 b.2.2))

/-- A sufficient, exact ordered-field sign test, including zero. -/
def ZNonneg (q : Z5) : Prop :=
  (0 ≤ q.1 ∧ 0 ≤ q.2) ∨
  (0 ≤ q.1 ∧ q.2 ≤ 0 ∧ 5*q.2*q.2 ≤ q.1*q.1) ∨
  (q.1 ≤ 0 ∧ 0 ≤ q.2 ∧ q.1*q.1 ≤ 5*q.2*q.2)
instance (q : Z5) : Decidable (ZNonneg q) := by unfold ZNonneg; infer_instance

theorem zeval_add (a b : Z5) : zeval (zadd a b)=zeval a+zeval b := by
  dsimp [zeval,zadd]; push_cast; ring
theorem zeval_sub (a b : Z5) : zeval (zsub a b)=zeval a-zeval b := by
  dsimp [zeval,zsub,zadd,zneg]; push_cast; ring
theorem zeval_mul (a b : Z5) : zeval (zmul a b)=zeval a*zeval b := by
  dsimp [zeval,zmul]; push_cast
  have hs : (Real.sqrt 5)^2=5 := by nlinarith [sqrt5_spec.1]
  ring_nf
  rw [hs]
theorem zpoint_sub (a b : ZPoint) : zpoint (zpsub a b)=zpoint a-zpoint b := by
  ext <;> simp [zpoint,zpsub,zeval_sub]
theorem zeval_dot (a b : ZPoint) : zeval (zdot a b)=dot (zpoint a) (zpoint b) := by
  simp only [zdot,zeval_add,zeval_mul,zpoint,dot]
  ring

theorem znonneg_sound (q : Z5) (h : ZNonneg q) : 0 ≤ zeval q := by
  have hs := sqrt5_spec
  have hid : zeval q*((q.1:ℝ)-(q.2:ℝ)*Real.sqrt 5) =
      (q.1:ℝ)^2-5*(q.2:ℝ)^2 := by
    dsimp [zeval]
    calc
      _ = (q.1:ℝ)^2-(q.2:ℝ)^2*(Real.sqrt 5*Real.sqrt 5) := by ring
      _ = _ := by rw [hs.1]; ring
  rcases h with ⟨ha,hb⟩ | ⟨ha,hb,hc⟩ | ⟨ha,hb,hc⟩
  · have ha' : (0:ℝ) ≤ q.1 := by exact_mod_cast ha
    have hb' : (0:ℝ) ≤ q.2 := by exact_mod_cast hb
    exact add_nonneg ha' (mul_nonneg hb' hs.2)
  · have ha' : (0:ℝ) ≤ q.1 := by exact_mod_cast ha
    have hc' : 5*(q.2:ℝ)*(q.2:ℝ) ≤ (q.1:ℝ)*(q.1:ℝ) := by exact_mod_cast hc
    by_contra hn
    have hn' : zeval q < 0 := lt_of_not_ge hn
    have hf : 0 < (q.1:ℝ)-(q.2:ℝ)*Real.sqrt 5 := by dsimp [zeval] at hn'; linarith
    have := mul_neg_of_neg_of_pos hn' hf
    nlinarith
  · have hb' : (0:ℝ) ≤ q.2 := by exact_mod_cast hb
    have hc' : (q.1:ℝ)*(q.1:ℝ) ≤ 5*(q.2:ℝ)*(q.2:ℝ) := by exact_mod_cast hc
    have hm := mul_nonneg hb' hs.2
    by_contra hn
    have hn' : zeval q < 0 := lt_of_not_ge hn
    have hf : (q.1:ℝ)-(q.2:ℝ)*Real.sqrt 5 < 0 := by dsimp [zeval] at hn'; linarith
    have := mul_pos_of_neg_of_neg hn' hf
    nlinarith

/-- A polynomial is represented in a tensor Bernstein basis using unnormalised
nonnegative distances to the closed faces. Its geometric identity is separate. -/
inductive SupportTree where
  | leaf (coefficient : Z5)
  | linear (axis : Fin 5) (left right : SupportTree)
  | quadratic (axis : Fin 5) (left middle right : SupportTree)
  deriving DecidableEq
def SupportTree.Valid : SupportTree → Prop
  | .leaf c => ZNonneg c
  | .linear _ l r => l.Valid ∧ r.Valid
  | .quadratic _ l m r => l.Valid ∧ m.Valid ∧ r.Valid
def supportTreeDecidable : (t : SupportTree) → Decidable t.Valid
  | .leaf c => inferInstanceAs (Decidable (ZNonneg c))
  | .linear _ l r =>
    letI := supportTreeDecidable l
    letI := supportTreeDecidable r
    inferInstanceAs (Decidable (l.Valid ∧ r.Valid))
  | .quadratic _ l m r =>
    letI := supportTreeDecidable l
    letI := supportTreeDecidable m
    letI := supportTreeDecidable r
    inferInstanceAs (Decidable (l.Valid ∧ m.Valid ∧ r.Valid))
instance (t : SupportTree) : Decidable t.Valid := supportTreeDecidable t
noncomputable def SupportTree.value (b : RationalBox) (x : Fin 5 → ℝ) : SupportTree → ℝ
  | .leaf c => zeval c
  | .linear i l r => ((b i).2-x i)*l.value b x+(x i-(b i).1)*r.value b x
  | .quadratic i l m r => ((b i).2-x i)^2*l.value b x+
      2*((b i).2-x i)*(x i-(b i).1)*m.value b x+(x i-(b i).1)^2*r.value b x

theorem support_tree_nonneg (tree : SupportTree) (b : RationalBox) (s t : ℝ) (r : Point)
    (hv : tree.Valid) (hb : InClosedBox b s t r) :
    0 ≤ tree.value b (config s t r) := by
  induction tree with
  | leaf c => exact znonneg_sound c hv
  | linear i l rr hl hr =>
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr (hb i).2) (hl hv.1))
      (mul_nonneg (sub_nonneg.mpr (hb i).1) (hr hv.2))
  | quadratic i l m rr hl hm hr =>
    have hL := sub_nonneg.mpr (hb i).2
    have hR := sub_nonneg.mpr (hb i).1
    exact add_nonneg (add_nonneg (mul_nonneg (sq_nonneg _) (hl hv.1))
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hL) hR) (hm hv.2.1)))
      (mul_nonneg (sq_nonneg _) (hr hv.2.2))

theorem support_tree_gap (tree : SupportTree) (b : RationalBox) (s t : ℝ) (r : Point)
    (scale p : ℝ) (hv : tree.Valid) (hb : InClosedBox b s t r)
    (hscale : 0 < scale) (hid : tree.value b (config s t r)=scale*p) : 0 ≤ p := by
  have h := support_tree_nonneg tree b s t r hv hb
  rw [hid] at h
  by_contra hp
  have := mul_neg_of_pos_of_neg hscale (lt_of_not_ge hp)
  linarith

/-- Small interpolation identities avoid a single enormous tensor expansion. -/
theorem support_linear_step (lo hi x p a b : ℝ) (hx : lo ≤ x ∧ x ≤ hi)
    (hwidth : lo < hi) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hid : (hi-lo)*p=(hi-x)*a+(x-lo)*b) : 0 ≤ p := by
  have h := add_nonneg (mul_nonneg (sub_nonneg.mpr hx.2) ha)
    (mul_nonneg (sub_nonneg.mpr hx.1) hb)
  rw [← hid] at h
  by_contra hp
  have := mul_neg_of_pos_of_neg (sub_pos.mpr hwidth) (lt_of_not_ge hp)
  linarith

theorem support_quadratic_step (lo hi x p a b c : ℝ) (hx : lo ≤ x ∧ x ≤ hi)
    (hwidth : lo < hi) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hid : (hi-lo)^2*p=(hi-x)^2*a+2*(hi-x)*(x-lo)*b+(x-lo)^2*c) : 0 ≤ p := by
  have h : 0 ≤ (hi-x)^2*a+2*(hi-x)*(x-lo)*b+(x-lo)^2*c :=
    add_nonneg (add_nonneg (mul_nonneg (sq_nonneg _) ha)
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (sub_nonneg.mpr hx.2))
        (sub_nonneg.mpr hx.1)) hb)) (mul_nonneg (sq_nonneg _) hc)
  rw [← hid] at h
  by_contra hp
  have := mul_neg_of_pos_of_neg (sq_pos_of_pos (sub_pos.mpr hwidth)) (lt_of_not_ge hp)
  linarith

end Phinopert
#print axioms Phinopert.zeval_add
#print axioms Phinopert.zeval_sub
#print axioms Phinopert.zeval_mul
#print axioms Phinopert.zpoint_sub
#print axioms Phinopert.zeval_dot
#print axioms Phinopert.znonneg_sound
#print axioms Phinopert.support_tree_nonneg
#print axioms Phinopert.support_tree_gap
#print axioms Phinopert.support_linear_step
#print axioms Phinopert.support_quadratic_step
