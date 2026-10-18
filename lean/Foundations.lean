import PhinopertData
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
First Phinopert formalisation milestone.
This file proves arithmetic and finite-rotation facts, NOT non-Rupertness.
The real parameter s is explicitly required to be the positive root of five.
No coverage result or Python success flag is assumed.
-/
namespace Phinopert
open scoped BigOperators

abbrev Point := ℝ × ℝ × ℝ
def eval (s : ℝ) (q : Q5) : ℝ := q.1 + q.2 * s
def evalPoint (s : ℝ) (p : RawPoint) : Point :=
  (eval s p.1, eval s p.2.1, eval s p.2.2)
def pointNeg (p : Point) : Point := (-p.1, -p.2.1, -p.2.2)
def VertexSet (s : ℝ) : Set Point := {p | ∃ q ∈ vertices, evalPoint s q = p}

def qadd (p q : Q5) : Q5 := (p.1+q.1, p.2+q.2)
def qmul (p q : Q5) : Q5 := (p.1*q.1+5*p.2*q.2, p.1*q.2+p.2*q.1)

theorem eval_neg (s : ℝ) (p : Q5) : eval s (qneg p) = -eval s p := by
  simp only [eval, qneg, Rat.cast_neg]
  ring

theorem eval_add (s : ℝ) (p q : Q5) :
    eval s (qadd p q) = eval s p + eval s q := by
  simp only [eval, qadd, Rat.cast_add]
  ring

theorem eval_mul (s : ℝ) (hs : s*s=5) (p q : Q5) :
    eval s (qmul p q) = eval s p * eval s q := by
  simp only [eval, qmul, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat]
  have hs2 : s^2=5 := by nlinarith [hs]
  ring_nf
  rw [hs2]

theorem eval_rawNeg (s : ℝ) (p : RawPoint) :
    evalPoint s (rawNeg p) = pointNeg (evalPoint s p) := by
  simp only [evalPoint, rawNeg, pointNeg, eval_neg]

theorem vertex_set_centrally_symmetric (s : ℝ) {p : Point}
    (hp : p ∈ VertexSet s) : pointNeg p ∈ VertexSet s := by
  obtain ⟨q, hq, rfl⟩ := hp
  exact ⟨rawNeg q, raw_neg_closed hq, eval_rawNeg s q⟩

def rawSeed0 : RawPoint := ((9/4,1/2),(0,0),(3/2,1/2))
def rawSeed1 : RawPoint := ((3/2,1/2),(9/4,1/2),(0,0))
def rawSeed2 : RawPoint := ((0,0),(3/2,1/2),(9/4,1/2))

theorem rawSeed0_mem : rawSeed0 ∈ vertices := by
  have hm : representatives[16]'(by decide) ∈ representatives := List.getElem_mem _
  have hv : representatives[16]'(by decide) ∈ vertices := List.mem_append_left _ hm
  have hn := raw_neg_closed hv
  norm_num [representatives, rawNeg, qneg, rawSeed0] at hn ⊢
  exact hn

theorem rawSeed1_mem : rawSeed1 ∈ vertices := by
  have hm : representatives[30]'(by decide) ∈ representatives := List.getElem_mem _
  have hv : representatives[30]'(by decide) ∈ vertices := List.mem_append_left _ hm
  have hn := raw_neg_closed hv
  norm_num [representatives, rawNeg, qneg, rawSeed1] at hn ⊢
  exact hn

theorem rawSeed2_mem : rawSeed2 ∈ vertices := by
  have hm : representatives[88]'(by decide) ∈ representatives := List.getElem_mem _
  have hv : representatives[88]'(by decide) ∈ vertices := List.mem_append_left _ hm
  have hn := raw_neg_closed hv
  norm_num [representatives, rawNeg, qneg, rawSeed2] at hn ⊢
  exact hn

theorem root5_bounds (s : ℝ) (hs : s*s=5) (hpos : 0 ≤ s) : 2 < s ∧ s < 3 := by
  constructor
  · by_contra h
    have hle : s ≤ 2 := le_of_not_gt h
    nlinarith [mul_nonneg (sub_nonneg.mpr hle) (show 0 ≤ 2+s by linarith)]
  · by_contra h
    have hle : 3 ≤ s := le_of_not_gt h
    nlinarith [mul_nonneg (sub_nonneg.mpr hle) (show 0 ≤ s+3 by linarith)]

-- An exact sign rule for opposite-sign coefficients, the difficult Q(sqrt5) case.
theorem opposite_sign_positive (a b s : ℝ) (ha : 0 < a) (hb : b < 0)
    (hs : s*s=5) (hpos : 0 ≤ s) :
    0 < a+b*s ↔ 5*b*b < a*a := by
  have hspos : 0 < s := (root5_bounds s hs hpos).1.trans' (by norm_num)
  have hbs : b*s < 0 := mul_neg_of_neg_of_pos hb hspos
  have hid : (a+b*s)*(a-b*s) = a*a-5*b*b := by
    calc
      _ = a*a-b*b*(s*s) := by ring
      _ = _ := by rw [hs]; ring
  have hfactor : 0 < a-b*s := by linarith
  constructor
  · intro h
    have := mul_pos h hfactor
    linarith
  · intro h
    have : 0 < (a+b*s)*(a-b*s) := by linarith
    exact (mul_pos_iff_of_pos_right hfactor).mp this

def dot (p q : Point) : ℝ := p.1*q.1 + p.2.1*q.2.1 + p.2.2*q.2.2
def denom (r : Point) : ℝ := 1 + dot r r
def numerator (r p : Point) : Point :=
  ((1+r.1^2-r.2.1^2-r.2.2^2)*p.1 + 2*(r.1*r.2.1-r.2.2)*p.2.1
      + 2*(r.1*r.2.2+r.2.1)*p.2.2,
   2*(r.1*r.2.1+r.2.2)*p.1 + (1-r.1^2+r.2.1^2-r.2.2^2)*p.2.1
      + 2*(r.2.1*r.2.2-r.1)*p.2.2,
   2*(r.1*r.2.2-r.2.1)*p.1 + 2*(r.2.1*r.2.2+r.1)*p.2.1
      + (1-r.1^2-r.2.1^2+r.2.2^2)*p.2.2)
noncomputable def cayley (r p : Point) : Point :=
  ((numerator r p).1 / denom r,
   (numerator r p).2.1 / denom r,
   (numerator r p).2.2 / denom r)

theorem denom_positive (r : Point) : 0 < denom r := by
  dsimp [denom, dot]
  nlinarith [sq_nonneg r.1, sq_nonneg r.2.1, sq_nonneg r.2.2]

set_option maxHeartbeats 1000000 in
theorem numerator_dot (r p q : Point) :
    dot (numerator r p) (numerator r q) = denom r ^ 2 * dot p q := by
  dsimp [dot, numerator, denom]
  ring

theorem cayley_dot (r p q : Point) : dot (cayley r p) (cayley r q) = dot p q := by
  have hd : denom r ≠ 0 := ne_of_gt (denom_positive r)
  calc
    _ = dot (numerator r p) (numerator r q) / (denom r * denom r) := by
      dsimp [dot,cayley]; ring
    _ = dot p q := by
      rw [numerator_dot,pow_two]
      exact mul_div_cancel_left₀ _ (mul_ne_zero hd hd)

def det (p q r : Point) : ℝ :=
  p.1*(q.2.1*r.2.2-q.2.2*r.2.1) -
  p.2.1*(q.1*r.2.2-q.2.2*r.1) +
  p.2.2*(q.1*r.2.1-q.2.1*r.1)

set_option maxHeartbeats 1000000 in
theorem numerator_orientation (r : Point) :
    det (numerator r (1,0,0)) (numerator r (0,1,0)) (numerator r (0,0,1))
      = denom r ^ 3 := by
  dsimp [det, numerator, denom, dot]
  ring

theorem cayley_orientation (r : Point) :
    det (cayley r (1,0,0)) (cayley r (0,1,0)) (cayley r (0,0,1)) = 1 := by
  have hd : denom r ≠ 0 := ne_of_gt (denom_positive r)
  calc
    _ = det (numerator r (1,0,0)) (numerator r (0,1,0))
          (numerator r (0,0,1)) / denom r ^ 3 := by
      dsimp [det,cayley]; ring
    _ = 1 := by rw [numerator_orientation]; exact div_self (pow_ne_zero 3 hd)

theorem seed_determinant_positive (s : ℝ) (hs : s*s=5) (hpos : 0 ≤ s) :
    0 < det (evalPoint s rawSeed0) (evalPoint s rawSeed1) (evalPoint s rawSeed2) := by
  have hb := (root5_bounds s hs hpos).1
  have hx : 0 < (9/4 : ℝ)+s/2 := by linarith
  have hz : 0 < (3/2 : ℝ)+s/2 := by linarith
  have he : det (evalPoint s rawSeed0) (evalPoint s rawSeed1) (evalPoint s rawSeed2) =
      ((9/4 : ℝ)+s/2)^3 + ((3/2 : ℝ)+s/2)^3 := by
    norm_num [det,evalPoint,eval,rawSeed0,rawSeed1,rawSeed2]
    ring
  rw [he]
  exact add_pos (pow_pos hx 3) (pow_pos hz 3)

-- Scalar support-gap obstruction. The projection/interior bridge is a later obligation.
theorem cleared_support_gap (r p n : Point) (h : ℝ) :
    denom r * (dot n (cayley r p) - h) = dot n (numerator r p) - denom r*h := by
  have hd : denom r ≠ 0 := ne_of_gt (denom_positive r)
  have he : dot n (cayley r p) = dot n (numerator r p) / denom r := by
    dsimp [dot,cayley]; ring
  rw [he, mul_sub, mul_div_cancel₀ _ hd]

theorem nonnegative_gap_excludes_strict_support (r p n : Point) (h : ℝ)
    (hgap : 0 ≤ dot n (numerator r p) - denom r*h) :
    ¬ dot n (cayley r p) < h := by
  intro hfit
  have hneg := mul_neg_of_pos_of_neg (denom_positive r) (sub_neg.mpr hfit)
  rw [cleared_support_gap] at hneg
  exact (not_lt_of_ge hgap) hneg

end Phinopert

#print axioms Phinopert.vertex_list_length
#print axioms Phinopert.raw_neg_involution
#print axioms Phinopert.raw_neg_closed
#print axioms Phinopert.eval_neg
#print axioms Phinopert.eval_add
#print axioms Phinopert.eval_mul
#print axioms Phinopert.vertex_set_centrally_symmetric
#print axioms Phinopert.rawSeed0_mem
#print axioms Phinopert.rawSeed1_mem
#print axioms Phinopert.rawSeed2_mem
#print axioms Phinopert.seed_determinant_positive
#print axioms Phinopert.root5_bounds
#print axioms Phinopert.opposite_sign_positive
#print axioms Phinopert.denom_positive
#print axioms Phinopert.numerator_dot
#print axioms Phinopert.cayley_dot
#print axioms Phinopert.numerator_orientation
#print axioms Phinopert.cayley_orientation
#print axioms Phinopert.cleared_support_gap
#print axioms Phinopert.nonnegative_gap_excludes_strict_support
