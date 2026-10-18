import GlobalViewCoverage

/-! Independently oriented hole and plug, both represented by unit quaternions.
Translations are relative translations in the physical shadow plane. -/
namespace Phinopert
open Set

def StrictTwoBodyFit (u : Point) (hu : u ≠ 0)
    (hole plug : QuaternionCoords) (offset : normalPlane u) : Prop :=
  ∀ x ∈ solid, planeProject u hu (qAction plug x) + offset ∈
    interior (planeProject u hu '' (qAction hole '' solid))

/-- A signed scalar on the normal, but always a proper body symmetry. -/
theorem actual_view_chart (u : Point) (hu : u ≠ 0) :
    ∃ q ∈ icoReal (Real.sqrt 5), ∃ s t k : ℝ,
      k ≠ 0 ∧ qAction q u = k • (s,t,1) ∧
      0 ≤ s ∧ 0 ≤ t ∧ phi*s+phi^2*t ≤ 1 := by
  obtain ⟨v,hv,hz,hs,_hsmax,ht,_htmax,hcone⟩ := actual_ico_view_representative u hu
  have hn := positive_height_normalisation v hz
  rcases (mem_icoViewOrbit u v).mp hv with ⟨q,hq,hqv⟩ | ⟨q,hq,hqv⟩
  · exact ⟨q,hq,_,_,v.2.2,ne_of_gt hz,hqv.trans hn,hs,ht,hcone⟩
  · have he : qAction q u = -v := by rw [← hqv, neg_neg]
    refine ⟨q,hq,_,_,-v.2.2,neg_ne_zero.mpr (ne_of_gt hz),?_,hs,ht,hcone⟩
    rw [he,neg_smul,← hn]

theorem unit_action_nonzero (q : QuaternionCoords) (hq : qNormSq q = 1)
    (u : Point) (hu : u ≠ 0) : qAction q u ≠ 0 := by
  intro hz
  have hzero : qAction q (0 : Point) = 0 := (qActionLinear q).map_zero
  exact hu (qAction_injective_of_unit q hq (hz.trans hzero.symm))

theorem normalised_hole_image (q hole : QuaternionCoords)
    (hh : qNormSq hole = 1) (hq : qAction q '' solid = solid) :
    qAction (qProduct q (qConjugate hole)) '' (qAction hole '' solid) = solid := by
  rw [Set.image_image]
  have hf : (fun x => qAction (qProduct q (qConjugate hole)) (qAction hole x)) =
      qAction q := by
    funext x
    rw [qAction_product, qConjugate_action_left hole hh]
  rw [hf,hq]

/-- The complete all-view, two-body reduction for unit-quaternion orientations.
No finite-certificate exclusion is used in this theorem. -/
theorem actual_two_body_domain_reduction
    (u : Point) (hu : u ≠ 0) (hole plug : QuaternionCoords)
    (hh : qNormSq hole = 1) (hp : qNormSq plug = 1) (offset : normalPlane u)
    (hfit : StrictTwoBodyFit u hu hole plug offset) :
    ∃ s t : ℝ, ∃ r : Point, InIcoDomain s t r ∧ StrictShadowFit s t r 0 := by
  have hch : qNormSq (qConjugate hole) = 1 := (qConjugate_normSq hole).trans hh
  obtain ⟨q,hq,s,t,k,hk,hdir,hs,ht,hcone⟩ := actual_view_chart
    (qAction (qConjugate hole) u) (unit_action_nonzero _ hch u hu)
  let c := qProduct q (qConjugate hole)
  have hc : qNormSq c = 1 := qProduct_unit q _ (icoReal_unit _ sqrt5_spec.1 hq) hch
  have hcu : qAction c u = k • (s,t,1) := by
    change qAction (qProduct q (qConjugate hole)) u = _
    rw [qAction_product]
    exact hdir
  have hout : qAction c '' (qAction hole '' solid) = solid :=
    normalised_hole_image q hole hh (actual_ico_solid_invariant hq)
  have hf := strict_containment_change_view u hu c hc s t k hk hcu
    (qAction hole '' solid) hout (qAction plug) offset hfit
  refine ⟨s,t,?_⟩
  apply actual_fixed_view_domain_reduction s t hs ht hcone (qProduct c plug)
    (qProduct_unit c plug hc hp) (screen s t (qAction c offset.val))
  intro x hx
  rw [qAction_product]
  exact hf x hx

theorem two_body_exclusion_of_domain_exclusion
    (hexclude : ∀ s t r, InIcoDomain s t r → ¬ StrictShadowFit s t r 0)
    (u : Point) (hu : u ≠ 0) (hole plug : QuaternionCoords)
    (hh : qNormSq hole = 1) (hp : qNormSq plug = 1) (offset : normalPlane u) :
    ¬ StrictTwoBodyFit u hu hole plug offset := by
  intro hfit
  obtain ⟨s,t,r,hd,hf⟩ := actual_two_body_domain_reduction u hu hole plug hh hp offset hfit
  exact hexclude s t r hd hf

/-- A relative translation may be specified in ambient 3-space: its component
along the viewing direction vanishes on projection. -/
theorem actual_ambient_translation_domain_reduction
    (u : Point) (hu : u ≠ 0) (hole plug : QuaternionCoords)
    (hh : qNormSq hole = 1) (hp : qNormSq plug = 1) (translation : Point)
    (hfit : ∀ x ∈ solid, planeProject u hu (qAction plug x + translation) ∈
      interior (planeProject u hu '' (qAction hole '' solid))) :
    ∃ s t : ℝ, ∃ r : Point, InIcoDomain s t r ∧ StrictShadowFit s t r 0 := by
  apply actual_two_body_domain_reduction u hu hole plug hh hp (planeProject u hu translation)
  intro x hx
  simpa only [planeProject_add] using hfit x hx

end Phinopert
#print axioms Phinopert.actual_view_chart
#print axioms Phinopert.unit_action_nonzero
#print axioms Phinopert.normalised_hole_image
#print axioms Phinopert.actual_two_body_domain_reduction
#print axioms Phinopert.two_body_exclusion_of_domain_exclusion
#print axioms Phinopert.actual_ambient_translation_domain_reduction
