import DomainCoverage
import ContainmentSymmetries

namespace Phinopert
def StrictQuaternionFit (s t : ℝ) (p : QuaternionCoords) (offset : Plane) : Prop :=
  ∀ x ∈ solid, screen s t (qAction p x)+offset ∈ interior (screen s t '' solid)

/-- For a viewing direction already in the cone, every translated strict fit
by a unit quaternion has a centred Cayley representative satisfying ALL 73
domain inequalities. Finite-table obligations remain explicit until assembly. -/
theorem fixed_view_domain_reduction_of_checks
    (htable : ∀ i : Fin 60, IcoClosureRow i.val)
    (hvertices : ∀ i : Fin 60, IcoVertexRow i.val)
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (hcone : phi*s+phi^2*t ≤ 1)
    (p : QuaternionCoords) (hp : qNormSq p=1) (offset : Plane)
    (hfit : StrictQuaternionFit s t p offset) :
    ∃ r : Point, InIcoDomain s t r ∧ StrictShadowFit s t r 0 := by
  obtain ⟨q,hq,_,_,hd,haction⟩ := selected_rotation_in_domain_of_table htable p hp s t hs ht hcone
  have he := ico_view_candidates_shadow_of_checks hvertices s t p hq
  have hf : StrictShadowFit s t (icoSelectedVector q) offset := by
    intro x hx
    have hmem : screen s t (cayley (icoSelectedVector q) x) ∈ quatShadow s t q := by
      rw [← haction x]
      exact ⟨x,hx,rfl⟩
    rw [he] at hmem
    obtain ⟨y,hy,heq⟩ := (mem_quatShadow s t p _).mp hmem
    have hh := hfit y hy
    rwa [heq] at hh
  exact ⟨icoSelectedVector q,hd,strict_fit_centred s t _ offset hf⟩

end Phinopert
#print axioms Phinopert.fixed_view_domain_reduction_of_checks
