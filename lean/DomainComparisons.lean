import IcosahedralReal
import CayleyCompatibility

/-!
The twelve actual right-multiplication comparison inequalities. Coordinate
indices are cyclic: (x,y), (y,z), (z,x). Within each block the signs are
(-1,-1), (-1,1), (1,-1), (1,1), exactly as in `icoComparisons`.
Scalar maximality and a positive scalar are explicit hypotheses; no finite
closure, orbit coverage, or unit-quaternion hypothesis is needed here.
-/
namespace Phinopert

/-- The ordered forms `ε*r_i + (φ-1)*δ*r_next + φ-2`. -/
noncomputable def comparisonForms (φ : ℝ) (r : Point) : List ℝ :=
  [-r.1 - (φ-1)*r.2.1 + φ-2,
   -r.1 + (φ-1)*r.2.1 + φ-2,
    r.1 - (φ-1)*r.2.1 + φ-2,
    r.1 + (φ-1)*r.2.1 + φ-2,
   -r.2.1 - (φ-1)*r.2.2 + φ-2,
   -r.2.1 + (φ-1)*r.2.2 + φ-2,
    r.2.1 - (φ-1)*r.2.2 + φ-2,
    r.2.1 + (φ-1)*r.2.2 + φ-2,
   -r.2.2 - (φ-1)*r.1 + φ-2,
   -r.2.2 + (φ-1)*r.1 + φ-2,
    r.2.2 - (φ-1)*r.1 + φ-2,
    r.2.2 + (φ-1)*r.1 + φ-2]

/-- The specified twelve quaternions evaluated at the positive root of five. -/
noncomputable def actualComparisons : List QuaternionCoords :=
  icoComparisons.map (iqEval (Real.sqrt 5))

theorem comparisonForms_length (φ : ℝ) (r : Point) :
    (comparisonForms φ r).length = 12 := rfl

theorem actualComparisons_length : actualComparisons.length = 12 := by
  simp [actualComparisons, icoComparisons]

theorem actualComparisons_mem {g : QuaternionCoords} (hg : g ∈ actualComparisons) :
    g ∈ icoReal (Real.sqrt 5) :=
  icoReal_comparisons (Real.sqrt 5) g hg

/-- This polynomial list identity holds even without imposing `s*s = 5`. -/
theorem comparisonForms_identity_eval (s : ℝ) (r : Point) :
    (icoComparisons.map (iqEval s)).map (fun g => 2*(qProduct (1,r) g).1-2) =
      comparisonForms ((1+s)/2) r := by
  norm_num [icoComparisons, iqEval, ieval, qProduct, comparisonForms]
  repeat' constructor <;> ring_nf

theorem comparisonForms_identity (r : Point) :
    actualComparisons.map (fun g => 2*(qProduct (1,r) g).1-2) =
      comparisonForms ((1+Real.sqrt 5)/2) r :=
  comparisonForms_identity_eval (Real.sqrt 5) r

theorem qProduct_scalar_smul_left (a : ℝ) (q g : QuaternionCoords) :
    (qProduct (a • q) g).1 = a * (qProduct q g).1 := by
  simp [qProduct]
  ring

theorem normalised_scalar_le_one (a : ℝ) (r : Point) (g : QuaternionCoords)
    (ha : 0 < a)
    (hmax : (qProduct (a • (1,r)) g).1 ≤ (a • (1,r) : QuaternionCoords).1) :
    (qProduct (1,r) g).1 ≤ 1 := by
  have hm : a * (qProduct (1,r) g).1 ≤ a * 1 := by
    simpa only [qProduct_scalar_smul_left, Prod.smul_fst, smul_eq_mul] using hmax
  exact (mul_le_mul_left ha).mp hm

/-- Actual group competitors give all twelve forms, in the specified order. -/
theorem comparisonForms_nonpos_of_scalar_max
    (q : QuaternionCoords) (a : ℝ) (r : Point)
    (ha : 0 < a) (hq : q = a • (1,r))
    (hmax : ∀ g ∈ icoReal (Real.sqrt 5), (qProduct q g).1 ≤ q.1) :
    ∀ f ∈ comparisonForms ((1+Real.sqrt 5)/2) r, f ≤ 0 := by
  intro f hf
  rw [← comparisonForms_identity r] at hf
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
  have hm := hmax g (actualComparisons_mem hg)
  rw [hq] at hm
  have hn := normalised_scalar_le_one a r g ha hm
  linarith

/-- Each block of four forms bounds its first coordinate by `2-φ`. -/
theorem comparisonForms_pair_bounds (φ : ℝ) (r : Point)
    (h : ∀ f ∈ comparisonForms φ r, f ≤ 0) :
    (-(2-φ) ≤ r.1 ∧ r.1 ≤ 2-φ) ∧
    (-(2-φ) ≤ r.2.1 ∧ r.2.1 ≤ 2-φ) ∧
    (-(2-φ) ≤ r.2.2 ∧ r.2.2 ≤ 2-φ) := by
  simp only [comparisonForms, List.forall_mem_cons, List.forall_mem_nil, and_true] at h
  obtain ⟨h00, h01, h02, h03, h10, h11, h12, h13, h20, h21, h22, h23⟩ := h
  refine ⟨signed_pair_bound φ r.1 r.2.1 ?_ ?_ ?_ ?_,
    signed_pair_bound φ r.2.1 r.2.2 ?_ ?_ ?_ ?_,
    signed_pair_bound φ r.2.2 r.1 ?_ ?_ ?_ ?_⟩ <;> linarith

theorem comparisonForms_coordinate_bounds (r : Point)
    (h : ∀ f ∈ comparisonForms ((1+Real.sqrt 5)/2) r, f ≤ 0) :
    (-2/5 ≤ r.1 ∧ r.1 ≤ 2/5) ∧
    (-2/5 ≤ r.2.1 ∧ r.2.1 ≤ 2/5) ∧
    (-2/5 ≤ r.2.2 ∧ r.2.2 ≤ 2/5) := by
  obtain ⟨hx, hy, hz⟩ := comparisonForms_pair_bounds _ r h
  have hs : Real.sqrt (5 : ℝ) * Real.sqrt 5 = 5 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
  exact ⟨cayley_coordinate_box _ _ hs (Real.sqrt_nonneg _) hx,
    cayley_coordinate_box _ _ hs (Real.sqrt_nonneg _) hy,
    cayley_coordinate_box _ _ hs (Real.sqrt_nonneg _) hz⟩

theorem comparison_coordinate_bounds_of_scalar_max
    (q : QuaternionCoords) (a : ℝ) (r : Point)
    (ha : 0 < a) (hq : q = a • (1,r))
    (hmax : ∀ g ∈ icoReal (Real.sqrt 5), (qProduct q g).1 ≤ q.1) :
    (-2/5 ≤ r.1 ∧ r.1 ≤ 2/5) ∧
    (-2/5 ≤ r.2.1 ∧ r.2.1 ≤ 2/5) ∧
    (-2/5 ≤ r.2.2 ∧ r.2.2 ≤ 2/5) :=
  comparisonForms_coordinate_bounds r
    (comparisonForms_nonpos_of_scalar_max q a r ha hq hmax)

end Phinopert

#print axioms Phinopert.comparisonForms_length
#print axioms Phinopert.actualComparisons_length
#print axioms Phinopert.actualComparisons_mem
#print axioms Phinopert.comparisonForms_identity_eval
#print axioms Phinopert.comparisonForms_identity
#print axioms Phinopert.qProduct_scalar_smul_left
#print axioms Phinopert.normalised_scalar_le_one
#print axioms Phinopert.comparisonForms_nonpos_of_scalar_max
#print axioms Phinopert.comparisonForms_pair_bounds
#print axioms Phinopert.comparisonForms_coordinate_bounds
#print axioms Phinopert.comparison_coordinate_bounds_of_scalar_max
