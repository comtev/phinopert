import ActualIcosahedral
import ViewCovariance

/-! Unconditional viewing-direction coverage for the unit-quaternion model.
Every nonzero normal is allowed, including directions outside the original
screen chart. Arbitrary SO(3) representation and exclusion of the reduced
domain are separate obligations; neither is assumed to have been proved. -/
namespace Phinopert

theorem positive_height_normalisation (v : Point) (hv : 0 < v.2.2) :
    v = v.2.2 • (v.1/v.2.2, v.2.1/v.2.2, (1 : ℝ)) := by
  ext <;> simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  · exact (mul_div_cancel₀ v.1 (ne_of_gt hv)).symm
  · exact (mul_div_cancel₀ v.2.1 (ne_of_gt hv)).symm
  · ring

theorem quaternion_fit_to_domain_of_view
    (u : Point) (hu : u ≠ 0) (q : QuaternionCoords)
    (hq : q ∈ icoReal (Real.sqrt 5)) (s t k : ℝ) (hk : k ≠ 0)
    (hdir : qAction q u = k • (s,t,1))
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hcone : phi*s+phi^2*t ≤ 1)
    (p : QuaternionCoords) (hp : qNormSq p = 1) (offset : normalPlane u)
    (hfit : StrictOrthogonalFit u hu (qAction p) offset) :
    ∃ r : Point, InIcoDomain s t r ∧ StrictShadowFit s t r 0 := by
  have hqu := icoReal_unit _ sqrt5_spec.1 hq
  have hc := strict_fit_change_view u hu q hqu s t k hk hdir
    (actual_ico_solid_invariant hq) (qAction p) offset hfit
  apply actual_fixed_view_domain_reduction s t hs ht hcone (qProduct q p)
    (qProduct_unit q p hqu hp) (screen s t (qAction q offset.val))
  intro x hx
  rw [qAction_product]
  exact hc x hx

/-- Full coverage of nonzero viewing normals, with a genuine relative-interior
containment hypothesis and an arbitrary in-plane translation. The plug's
rotation is represented by an arbitrary unit quaternion. -/
theorem actual_all_view_domain_reduction
    (u : Point) (hu : u ≠ 0) (p : QuaternionCoords) (hp : qNormSq p = 1)
    (offset : normalPlane u) (hfit : StrictOrthogonalFit u hu (qAction p) offset) :
    ∃ s t : ℝ, ∃ r : Point, InIcoDomain s t r ∧ StrictShadowFit s t r 0 := by
  obtain ⟨v, hv, hz, hs, _hsmax, ht, _htmax, hcone⟩ := actual_ico_view_representative u hu
  have hn := positive_height_normalisation v hz
  rcases (mem_icoViewOrbit u v).mp hv with ⟨q,hq,hqv⟩ | ⟨q,hq,hqv⟩
  · refine ⟨v.1/v.2.2, v.2.1/v.2.2, ?_⟩
    exact quaternion_fit_to_domain_of_view u hu q hq _ _ v.2.2 (ne_of_gt hz)
      (hqv.trans hn) hs ht hcone p hp offset hfit
  · have he : qAction q u = -v := by rw [← hqv, neg_neg]
    have hdir : qAction q u = (-v.2.2) • (v.1/v.2.2, v.2.1/v.2.2, (1 : ℝ)) := by
      rw [he, neg_smul, ← hn]
    refine ⟨v.1/v.2.2, v.2.1/v.2.2, ?_⟩
    exact quaternion_fit_to_domain_of_view u hu q hq _ _ (-v.2.2)
      (neg_ne_zero.mpr (ne_of_gt hz)) hdir hs ht hcone p hp offset hfit

/-- The remaining domain-exclusion obligation is explicit, not an axiom or
an imported numerical assertion. This is NOT a non-Rupertness theorem. -/
theorem all_view_exclusion_of_domain_exclusion
    (hexclude : ∀ s t r, InIcoDomain s t r → ¬ StrictShadowFit s t r 0)
    (u : Point) (hu : u ≠ 0) (p : QuaternionCoords) (hp : qNormSq p = 1)
    (offset : normalPlane u) : ¬ StrictOrthogonalFit u hu (qAction p) offset := by
  intro hfit
  obtain ⟨s,t,r,hd,hf⟩ := actual_all_view_domain_reduction u hu p hp offset hfit
  exact hexclude s t r hd hf

end Phinopert
#print axioms Phinopert.positive_height_normalisation
#print axioms Phinopert.quaternion_fit_to_domain_of_view
#print axioms Phinopert.actual_all_view_domain_reduction
#print axioms Phinopert.all_view_exclusion_of_domain_exclusion
