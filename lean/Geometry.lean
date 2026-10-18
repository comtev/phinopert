import Foundations
import Mathlib.Analysis.Convex.Topology
import Mathlib.Data.Real.Sqrt

/-! Geometric bridge for Phinopert. No global covering theorem is assumed here. -/
namespace Phinopert
open Set
open scoped Pointwise
open scoped BigOperators

abbrev Plane := ℝ × ℝ
noncomputable def solid : Set Point := convexHull ℝ (VertexSet (Real.sqrt 5))

theorem sqrt5_spec : Real.sqrt 5 * Real.sqrt 5 = 5 ∧ 0 ≤ Real.sqrt 5 :=
  ⟨Real.mul_self_sqrt (by norm_num), Real.sqrt_nonneg _⟩

theorem solid_centrally_symmetric {p : Point} (hp : p ∈ solid) : -p ∈ solid := by
  have hv : -(VertexSet (Real.sqrt 5)) = VertexSet (Real.sqrt 5) := by
    ext x
    constructor
    · intro hx
      have hn : -x ∈ VertexSet (Real.sqrt 5) := by simpa using hx
      have := vertex_set_centrally_symmetric (Real.sqrt 5) hn
      simpa [pointNeg] using this
    · intro hx
      have := vertex_set_centrally_symmetric (Real.sqrt 5) hx
      simpa [pointNeg] using this
  have hh : -solid = solid := by
    unfold solid
    rw [← convexHull_neg, hv]
  have : p ∈ -solid := by rw [hh]; exact hp
  simpa using this

def screen (s t : ℝ) : Point →ₗ[ℝ] Plane where
  toFun p := (p.1-s*p.2.2, p.2.1-t*p.2.2)
  map_add' p q := by ext <;> simp <;> ring
  map_smul' a p := by ext <;> simp <;> ring

def screenNormal (n : Point) : Plane →ₗ[ℝ] ℝ where
  toFun x := n.1*x.1+n.2.1*x.2
  map_add' p q := by simp; ring
  map_smul' a p := by simp; ring

theorem screen_kernel (s t : ℝ) (p : Point) :
    screen s t p = 0 ↔ ∃ a : ℝ, p = a • (s,t,1) := by
  constructor
  · intro hp
    have hx := congrArg Prod.fst hp
    have hy := congrArg Prod.snd hp
    change p.1-s*p.2.2=0 at hx
    change p.2.1-t*p.2.2=0 at hy
    refine ⟨p.2.2, ?_⟩
    ext <;> simp <;> nlinarith
  · rintro ⟨a,rfl⟩
    ext <;> simp [screen] <;> ring

noncomputable def rotationMap (r : Point) : Point →ₗ[ℝ] Point where
  toFun p := cayley r p
  map_add' p q := by ext <;> simp [cayley,numerator] <;> ring
  map_smul' a p := by ext <;> simp [cayley,numerator] <;> ring

theorem screen_dot (s t : ℝ) (p n : Point)
    (hn : n.1*s+n.2.1*t+n.2.2=0) :
    screenNormal n (screen s t p) = dot n p := by
  change n.1*(p.1-s*p.2.2)+n.2.1*(p.2.1-t*p.2.2) = dot n p
  dsimp [dot]
  nlinarith [congrArg (fun a : ℝ => a*p.2.2) hn]

theorem shadow_convex (s t : ℝ) : Convex ℝ (screen s t '' solid) :=
  (convex_convexHull ℝ _).linear_image _

theorem shadow_centrally_symmetric (s t : ℝ) {x : Plane}
    (hx : x ∈ screen s t '' solid) : -x ∈ screen s t '' solid := by
  obtain ⟨p, hp, rfl⟩ := hx
  exact ⟨-p, solid_centrally_symmetric hp, (screen s t).map_neg p⟩

/-- Convexity of the outer shadow and symmetry of both shadows remove translation. -/
theorem centre_strict_containment (A B : Set Plane) (t : Plane)
    (hA : ∀ x ∈ A, -x ∈ A) (hB : ∀ x ∈ B, -x ∈ B)
    (hconv : Convex ℝ B) (hfit : ∀ x ∈ A, x+t ∈ interior B) :
    A ⊆ interior B := by
  have hopen : IsOpenMap (fun x : Plane => -x) :=
    IsOpenMap.of_inverse continuous_neg neg_neg neg_neg
  have hneg : ∀ x ∈ interior B, -x ∈ interior B :=
    hopen.mapsTo_interior hB
  intro x hx
  have hplus := hfit x hx
  have hminus := hneg (-x+t) (hfit (-x) (hA x hx))
  have hm := hconv.interior hplus hminus
    (show (0:ℝ) ≤ 1/2 by norm_num) (show (0:ℝ) ≤ 1/2 by norm_num)
    (show (1/2:ℝ)+1/2=1 by norm_num)
  have he : (1/2:ℝ) • (x+t) + (1/2:ℝ) • -(-x+t) = x := by
    ext <;> simp <;> ring
  rwa [he] at hm

def StrictShadowFit (s t : ℝ) (r : Point) (offset : Plane) : Prop :=
  ∀ p ∈ solid, screen s t (cayley r p)+offset ∈ interior (screen s t '' solid)

theorem strict_fit_centred (s t : ℝ) (r : Point) (offset : Plane)
    (hfit : StrictShadowFit s t r offset) : StrictShadowFit s t r 0 := by
  let f : Point →ₗ[ℝ] Plane := (screen s t).comp (rotationMap r)
  have hA : ∀ x ∈ f '' solid, -x ∈ f '' solid := by
    rintro x ⟨p,hp,rfl⟩
    exact ⟨-p,solid_centrally_symmetric hp,f.map_neg p⟩
  have ht : ∀ x ∈ f '' solid, x+offset ∈ interior (screen s t '' solid) := by
    rintro x ⟨p,hp,rfl⟩
    exact hfit p hp
  have hc := centre_strict_containment _ _ offset hA
    (fun x hx => shadow_centrally_symmetric s t hx)
    (shadow_convex s t) ht
  intro p hp
  simpa only [add_zero] using hc (Set.mem_image_of_mem f hp)

/-- A linear functional with a right inverse is open: an explicit local section proof. -/
theorem planar_functional_open (f : Plane →ₗ[ℝ] ℝ) (v : Plane) (hv : f v=1) :
    IsOpenMap f := by
  apply IsOpenMap.of_sections
  intro x
  refine ⟨fun y => x+(y-f x) • v, ?_, ?_, ?_⟩
  · exact (continuous_const.add ((continuous_id.sub continuous_const).smul
      continuous_const)).continuousAt
  · simp
  · intro y
    simp [map_add, map_smul, hv]

theorem interior_support_strict (B : Set Plane) (f : Plane →ₗ[ℝ] ℝ)
    (v : Plane) (hv : f v=1) (h : ℝ) (hsupport : ∀ y ∈ B, f y ≤ h)
    {x : Plane} (hx : x ∈ interior B) : f x < h := by
  have hb : B ⊆ f ⁻¹' Iic h := hsupport
  have hi := (planar_functional_open f v hv).interior_preimage_subset_preimage_interior
    (interior_mono hb hx)
  simpa only [interior_Iic, mem_preimage, mem_Iio] using hi

theorem screen_normal_section (s t : ℝ) (n : Point) (hne : n ≠ 0)
    (hn : n.1*s+n.2.1*t+n.2.2=0) : ∃ v : Plane, screenNormal n v=1 := by
  by_cases h0 : n.1=0
  · have h1 : n.2.1 ≠ 0 := by
      intro h1
      have h2 : n.2.2=0 := by simpa [h0,h1] using hn
      apply hne
      ext <;> simp [h0,h1,h2]
    refine ⟨(0,1/n.2.1), ?_⟩
    change n.1*0+n.2.1*(1/n.2.1)=1
    simp [h1]
  · refine ⟨(1/n.1,0), ?_⟩
    change n.1*(1/n.1)+n.2.1*0=1
    simp [h0]

theorem hull_support (V : Set Point) (n : Point) (h : ℝ)
    (hv : ∀ p ∈ V, dot n p ≤ h) : ∀ p ∈ convexHull ℝ V, dot n p ≤ h := by
  apply convexHull_min hv
  intro p hp q hq a b ha hb hab
  change dot n (a • p+b • q) ≤ h
  have he : dot n (a • p+b • q) = a*dot n p+b*dot n q := by
    simp [dot]; ring
  rw [he]
  have hpa := mul_le_mul_of_nonneg_left hp ha
  have hqb := mul_le_mul_of_nonneg_left hq hb
  calc
    a*dot n p+b*dot n q ≤ a*h+b*h := add_le_add hpa hqb
    _ = h := by rw [← add_mul, hab, one_mul]

/-- A nonnegative cleared gap at one vertex rules out strict containment in the
outer shadow. The bound need only be verified on the exact outer vertex set. -/
theorem gap_excludes_shadow_interior (s t : ℝ) (r p n : Point) (h : ℝ)
    (hne : n ≠ 0) (hn : n.1*s+n.2.1*t+n.2.2=0)
    (hsupport : ∀ q ∈ VertexSet (Real.sqrt 5), dot n q ≤ h)
    (hgap : 0 ≤ dot n (numerator r p)-denom r*h) :
    screen s t (cayley r p) ∉ interior (screen s t '' solid) := by
  intro hfit
  obtain ⟨v,hv⟩ := screen_normal_section s t n hne hn
  have hs : ∀ y ∈ screen s t '' solid, screenNormal n y ≤ h := by
    rintro y ⟨q,hq,rfl⟩
    rw [screen_dot s t q n hn]
    exact hull_support _ n h hsupport q hq
  have hlt := interior_support_strict _ _ v hv h hs hfit
  rw [screen_dot s t (cayley r p) n hn] at hlt
  exact nonnegative_gap_excludes_strict_support r p n h hgap hlt

theorem strict_fit_gap_negative (s t : ℝ) (r p n : Point) (h : ℝ) (offset : Plane)
    (hp : p ∈ VertexSet (Real.sqrt 5)) (hne : n ≠ 0)
    (hn : n.1*s+n.2.1*t+n.2.2=0)
    (hsupport : ∀ q ∈ VertexSet (Real.sqrt 5), dot n q ≤ h)
    (hfit : StrictShadowFit s t r offset) :
    dot n (numerator r p)-denom r*h < 0 := by
  have hc := strict_fit_centred s t r offset hfit p (subset_convexHull ℝ _ hp)
  simp only [add_zero] at hc
  by_contra hnonneg
  exact gap_excludes_shadow_interior s t r p n h hne hn hsupport
    (le_of_not_gt hnonneg) hc

theorem gap_excludes_translated_fit (s t : ℝ) (r p n : Point) (h : ℝ)
    (hp : p ∈ VertexSet (Real.sqrt 5)) (hne : n ≠ 0)
    (hn : n.1*s+n.2.1*t+n.2.2=0)
    (hsupport : ∀ q ∈ VertexSet (Real.sqrt 5), dot n q ≤ h)
    (hgap : 0 ≤ dot n (numerator r p)-denom r*h) :
    ¬ ∃ offset, StrictShadowFit s t r offset := by
  rintro ⟨offset,hfit⟩
  exact (not_lt_of_ge hgap) (strict_fit_gap_negative s t r p n h offset hp hne hn hsupport hfit)

/-- A weighted certificate need not exhibit any individually nonnegative gap.
Weights may vanish, but at least one must be strictly positive. -/
theorem weighted_gaps_exclude_translated_fit {ι : Type*} (S : Finset ι)
    (s t : ℝ) (r : Point) (p n : ι → Point) (h w : ι → ℝ)
    (hp : ∀ i ∈ S, p i ∈ VertexSet (Real.sqrt 5))
    (hne : ∀ i ∈ S, n i ≠ 0)
    (hn : ∀ i ∈ S, (n i).1*s+(n i).2.1*t+(n i).2.2=0)
    (hsupport : ∀ i ∈ S, ∀ q ∈ VertexSet (Real.sqrt 5), dot (n i) q ≤ h i)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hwpos : ∃ i ∈ S, 0 < w i)
    (hgap : 0 ≤ ∑ i ∈ S, w i*(dot (n i) (numerator r (p i))-denom r*h i)) :
    ¬ ∃ offset, StrictShadowFit s t r offset := by
  rintro ⟨offset,hfit⟩
  have hg : ∀ i ∈ S, dot (n i) (numerator r (p i))-denom r*h i < 0 := by
    intro i hi
    exact strict_fit_gap_negative s t r (p i) (n i) (h i) offset
      (hp i hi) (hne i hi) (hn i hi) (hsupport i hi) hfit
  have hsum : (∑ i ∈ S, w i*(dot (n i) (numerator r (p i))-denom r*h i)) < 0 := by
    apply Finset.sum_neg'
    · intro i hi
      exact mul_nonpos_of_nonneg_of_nonpos (hw i hi) (hg i hi).le
    · obtain ⟨i,hi,hwi⟩ := hwpos
      exact ⟨i,hi,mul_neg_of_pos_of_neg hwi (hg i hi)⟩
  exact (not_lt_of_ge hgap) hsum

end Phinopert

#print axioms Phinopert.sqrt5_spec
#print axioms Phinopert.solid_centrally_symmetric
#print axioms Phinopert.screen_dot
#print axioms Phinopert.screen_kernel
#print axioms Phinopert.shadow_convex
#print axioms Phinopert.shadow_centrally_symmetric
#print axioms Phinopert.centre_strict_containment
#print axioms Phinopert.strict_fit_centred
#print axioms Phinopert.planar_functional_open
#print axioms Phinopert.interior_support_strict
#print axioms Phinopert.screen_normal_section
#print axioms Phinopert.hull_support
#print axioms Phinopert.gap_excludes_shadow_interior
#print axioms Phinopert.strict_fit_gap_negative
#print axioms Phinopert.gap_excludes_translated_fit
#print axioms Phinopert.weighted_gaps_exclude_translated_fit
