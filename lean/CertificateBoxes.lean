import SO3Coverage
import Mathlib.Data.Fin.VecNotation

namespace Phinopert

abbrev RationalBox := Fin 5 → ℚ × ℚ
def config (s t : ℝ) (r : Point) : Fin 5 → ℝ := ![s,t,r.1,r.2.1,r.2.2]
def InClosedBox (b : RationalBox) (s t : ℝ) (r : Point) : Prop :=
  ∀ i, (b i).1 ≤ config s t r i ∧ config s t r i ≤ (b i).2

def cutBox (b : RationalBox) (i : Fin 5) (m : ℚ) (right : Bool) : RationalBox :=
  Function.update b i (if right then (m,(b i).2) else ((b i).1,m))

theorem closed_box_split (b : RationalBox) (i : Fin 5) (m : ℚ)
    (s t : ℝ) (r : Point) (h : InClosedBox b s t r) :
    InClosedBox (cutBox b i m false) s t r ∨ InClosedBox (cutBox b i m true) s t r := by
  rcases le_total (config s t r i) (m : ℝ) with hl | hr
  · left
    intro j
    by_cases hj : j = i
    · subst j
      exact ⟨by simpa [cutBox] using (h i).1, by simpa [cutBox] using hl⟩
    · simpa [cutBox,hj] using h j
  · right
    intro j
    by_cases hj : j = i
    · subst j
      exact ⟨by simpa [cutBox] using hr, by simpa [cutBox] using (h i).2⟩
    · simpa [cutBox,hj] using h j

inductive BoxPartition where
  | leaf
  | split (axis : Fin 5) (cut : ℚ) (left right : BoxPartition)
  deriving DecidableEq

def partitionLeaves (b : RationalBox) : BoxPartition → List RationalBox
  | .leaf => [b]
  | .split i m l r => partitionLeaves (cutBox b i m false) l ++
      partitionLeaves (cutBox b i m true) r

/-- A total closed cover, including each splitting face. No exclusion is
inferred merely from being a leaf. -/
theorem partition_covers (tree : BoxPartition) (b : RationalBox)
    (s t : ℝ) (r : Point) (h : InClosedBox b s t r) :
    ∃ c ∈ partitionLeaves b tree, InClosedBox c s t r := by
  induction tree generalizing b with
  | leaf => exact ⟨b,by simp [partitionLeaves],h⟩
  | split i m l right ihl ihr =>
    rcases closed_box_split b i m s t r h with hl | hr
    · obtain ⟨c,hc,hfit⟩ := ihl _ hl
      exact ⟨c,List.mem_append_left _ hc,hfit⟩
    · obtain ⟨c,hc,hfit⟩ := ihr _ hr
      exact ⟨c,List.mem_append_right _ hc,hfit⟩

theorem partition_exclusion (tree : BoxPartition) (b : RationalBox)
    (hleaves : ∀ c ∈ partitionLeaves b tree, ∀ s t r,
      InClosedBox c s t r → InIcoDomain s t r → ¬ StrictShadowFit s t r 0) :
    ∀ s t r, InClosedBox b s t r → InIcoDomain s t r → ¬ StrictShadowFit s t r 0 := by
  intro s t r hb hd
  obtain ⟨c,hc,hb⟩ := partition_covers tree b s t r hb
  exact hleaves c hc s t r hb hd

noncomputable def affineDomainValues (s t : ℝ) (r : Point) : List ℝ :=
  [phi*s+phi^2*t-1] ++ comparisonForms phi r

theorem affine_domain_nonpositive (s t : ℝ) (r : Point) (hd : InIcoDomain s t r)
    (f : ℝ) (hf : f ∈ affineDomainValues s t r) : f ≤ 0 := by
  have h := hd.2.2.2.2.2.2.2
  apply h f
  change f ∈ [_] ++ (comparisonForms phi r ++ _)
  rcases List.mem_append.mp hf with h1 | h2
  · exact List.mem_append_left _ h1
  · exact List.mem_append_right _ (List.mem_append_left _ h2)

/-- Exact rational brackets, proved once, are used only to certify strict
affine margins. A margin too small for these brackets must be left pending. -/
def phiLower : ℚ := 16180339887498948482045868343656381177203091798057 / 10000000000000000000000000000000000000000000000000
def phiUpper : ℚ := 16180339887498948482045868343656381177203091798058 / 10000000000000000000000000000000000000000000000000

theorem phi_rational_bounds : (phiLower : ℝ) ≤ phi ∧ phi ≤ (phiUpper : ℝ) := by
  have h := sqrt5_spec
  have hb := root5_bounds _ h.1 h.2
  have hpoly : phi^2-phi-1 = 0 := by dsimp [phi]; nlinarith [h.1]
  have hp : 1 < phi := by dsimp [phi]; linarith [hb.1]
  have hl : 1 < (phiLower : ℝ) := by norm_num [phiLower]
  have hu : 1 < (phiUpper : ℝ) := by norm_num [phiUpper]
  have hll : (phiLower : ℝ)^2-phiLower-1 < 0 := by norm_num [phiLower]
  have huu : 0 < (phiUpper : ℝ)^2-phiUpper-1 := by norm_num [phiUpper]
  constructor
  · by_contra hn
    have hlt : phi < (phiLower : ℝ) := lt_of_not_ge hn
    nlinarith [mul_pos (sub_pos.mpr hlt) (show 0 < (phiLower : ℝ)+phi-1 by linarith)]
  · by_contra hn
    have hlt : (phiUpper : ℝ) < phi := lt_of_not_ge hn
    nlinarith [mul_pos (sub_pos.mpr hlt) (show 0 < (phiUpper : ℝ)+phi-1 by linarith)]

theorem affine_phi_positive (a b : ℚ)
    (h : 0 < a+b*(if 0 ≤ b then phiLower else phiUpper)) :
    0 < (a : ℝ)+(b : ℝ)*phi := by
  have bounds := phi_rational_bounds
  by_cases hb : 0 ≤ b
  · simp only [if_pos hb] at h
    have hr : 0 < (a : ℝ)+(b : ℝ)*(phiLower : ℝ) := by exact_mod_cast h
    have hbr : (0 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    nlinarith [mul_nonneg hbr (sub_nonneg.mpr bounds.1)]
  · simp only [if_neg hb] at h
    have hr : 0 < (a : ℝ)+(b : ℝ)*(phiUpper : ℝ) := by exact_mod_cast h
    have hbr : (b : ℝ) ≤ 0 := by exact_mod_cast (le_of_not_ge hb)
    nlinarith [mul_nonneg (neg_nonneg.mpr hbr) (sub_nonneg.mpr bounds.2)]

theorem phi_square : phi^2 = phi+1 := by
  dsimp [phi]
  nlinarith [sqrt5_spec.1]

theorem phi_gt_one : 1 < phi := by
  have := root5_bounds _ sqrt5_spec.1 sqrt5_spec.2
  dsimp [phi]
  linarith

/-- Reusable tensor/Bernstein sign rule for forthcoming geometric leaves.
The polynomial identity remains an explicit obligation, never a Python flag. -/
theorem certified_nonnegative_sum {ι : Type*} (indices : Finset ι)
    (coeff basis : ι → ℝ) (p : ℝ)
    (hc : ∀ i ∈ indices, 0 ≤ coeff i) (hb : ∀ i ∈ indices, 0 ≤ basis i)
    (hid : p = ∑ i ∈ indices, coeff i * basis i) : 0 ≤ p := by
  rw [hid]
  exact Finset.sum_nonneg (fun i hi => mul_nonneg (hc i hi) (hb i hi))

end Phinopert
#print axioms Phinopert.closed_box_split
#print axioms Phinopert.partition_covers
#print axioms Phinopert.partition_exclusion
#print axioms Phinopert.affine_domain_nonpositive
#print axioms Phinopert.phi_rational_bounds
#print axioms Phinopert.affine_phi_positive
#print axioms Phinopert.phi_square
#print axioms Phinopert.phi_gt_one
#print axioms Phinopert.certified_nonnegative_sum
