import SO3Frames

namespace Phinopert
open Set

/-- Physical orthogonal-shadow containment for arbitrary proper orthogonal
linear orientations, with an ambient relative translation. -/
def ProperShadowFit (u : Point) (hu : u ≠ 0)
    (hole plug : Point →ₗ[ℝ] Point) (translation : Point) : Prop :=
  ∀ x ∈ solid, planeProject u hu (plug x + translation) ∈
    interior (planeProject u hu '' (hole '' solid))

theorem actual_SO3_domain_reduction (u : Point) (hu : u ≠ 0)
    (hole plug : Point →ₗ[ℝ] Point) (hh : IsProperRotation hole)
    (hp : IsProperRotation plug) (translation : Point)
    (hfit : ProperShadowFit u hu hole plug translation) :
    ∃ s t : ℝ, ∃ r : Point, InIcoDomain s t r ∧ StrictShadowFit s t r 0 := by
  obtain ⟨a,ha,hea⟩ := proper_rotation_has_quaternion hole hh
  obtain ⟨b,hb,heb⟩ := proper_rotation_has_quaternion plug hp
  apply actual_ambient_translation_domain_reduction u hu a b ha hb translation
  have he : qAction a = hole := funext hea
  intro x hx
  rw [heb,he]
  exact hfit x hx

def NoProperShadowFit : Prop :=
  ∀ (u : Point) (hu : u ≠ 0) (hole plug : Point →ₗ[ℝ] Point),
    IsProperRotation hole → IsProperRotation plug →
    ∀ translation, ¬ ProperShadowFit u hu hole plug translation

/-- Final geometric assembly, still conditional on actual domain exclusion. -/
theorem no_proper_shadow_fit_of_domain_exclusion
    (hexclude : ∀ s t r, InIcoDomain s t r → ¬ StrictShadowFit s t r 0) :
    NoProperShadowFit := by
  intro u hu hole plug hh hp translation hfit
  obtain ⟨s,t,r,hd,hf⟩ := actual_SO3_domain_reduction u hu hole plug hh hp translation hfit
  exact hexclude s t r hd hf

end Phinopert
#print axioms Phinopert.actual_SO3_domain_reduction
#print axioms Phinopert.no_proper_shadow_fit_of_domain_exclusion
