import IcosahedralClosure
import IcosahedralVertexChecks
import IcosahedralInvariance
import IcosahedralWalls
import IcosahedralSelection
import CayleyCompatibility
import DomainCoverage
import ContainmentSymmetries
import FixedViewCoverage

/-! Final assembly of this milestone. All finite-table hypotheses are discharged
by imported kernel proofs. These are actual group/invariance/selection results,
not the still-missing theorem that physical fits have representatives in D. -/
namespace Phinopert

theorem actual_ico_product_closed {p q : QuaternionCoords}
    (hp : p ∈ icoReal (Real.sqrt 5)) (hq : q ∈ icoReal (Real.sqrt 5)) :
    qProduct p q ∈ icoReal (Real.sqrt 5) :=
  icoReal_product_closed_of_table _ sqrt5_spec.1 ico_closure_all hp hq

theorem actual_ico_solid_invariant {q : QuaternionCoords}
    (hq : q ∈ icoReal (Real.sqrt 5)) : qAction q '' solid = solid :=
  icoReal_solid_image_of_checks ico_vertex_checks hq

theorem actual_ico_view_representative (u : Point) (hu : u ≠ 0) :
    ∃ v ∈ icoViewOrbit u, 0 < v.2.2 ∧
      0 ≤ v.1/v.2.2 ∧ v.1/v.2.2 ≤ 2/3 ∧
      0 ≤ v.2.1/v.2.2 ∧ v.2.1/v.2.2 ≤ 2/5 ∧
      phi*(v.1/v.2.2)+phi^2*(v.2.1/v.2.2) ≤ 1 :=
  actual_view_box_representative (fun _ hp _ hq => actual_ico_product_closed hp hq) u hu

theorem actual_ico_quaternion_representative (p j : QuaternionCoords)
    (hp : qNormSq p = 1) (hj : qNormSq j = 1)
    (hjj : qProduct j j = (-1, (0 : Point))) :
    ∃ q ∈ quaternionCandidates icoSelectionGroup p j,
      qNormSq q = 1 ∧ 1/2 ≤ q.1 ∧
      (∀ v ∈ quaternionCandidates icoSelectionGroup p j, v.1 ≤ q.1) ∧
      (∀ g ∈ icoSelectionGroup,
        (-q.1 ≤ (qProduct q g).1 ∧ (qProduct q g).1 ≤ q.1) ∧
        (-q.1 ≤ (qProduct (qProduct j q) g).1 ∧
          (qProduct (qProduct j q) g).1 ≤ q.1)) :=
  ico_quaternion_selection_of_table ico_closure_all p j hp hj hjj

theorem actual_ico_domain_rotation (p : QuaternionCoords) (hp : qNormSq p=1)
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (hcone : phi*s+phi^2*t ≤ 1) :
    ∃ q ∈ quaternionCandidates icoSelectionGroup p (icoViewHalfturn s t),
      qNormSq q=1 ∧ 1/2 ≤ q.1 ∧ InIcoDomain s t (icoSelectedVector q) ∧
      (∀ x : Point, qAction q x = cayley (icoSelectedVector q) x) :=
  selected_rotation_in_domain_of_table ico_closure_all p hp s t hs ht hcone

theorem actual_fixed_view_domain_reduction
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (hcone : phi*s+phi^2*t ≤ 1)
    (p : QuaternionCoords) (hp : qNormSq p=1) (offset : Plane)
    (hfit : StrictQuaternionFit s t p offset) :
    ∃ r : Point, InIcoDomain s t r ∧ StrictShadowFit s t r 0 :=
  fixed_view_domain_reduction_of_checks ico_closure_all ico_vertex_checks s t hs ht hcone p hp offset hfit

end Phinopert
#print axioms Phinopert.actual_ico_product_closed
#print axioms Phinopert.actual_ico_solid_invariant
#print axioms Phinopert.actual_ico_view_representative
#print axioms Phinopert.actual_ico_quaternion_representative
#print axioms Phinopert.actual_ico_domain_rotation
#print axioms Phinopert.actual_fixed_view_domain_reduction
