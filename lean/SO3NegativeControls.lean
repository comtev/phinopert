import CertificateBoxes

namespace Phinopert

def reflectionX : Point →ₗ[ℝ] Point where
  toFun p := (-p.1,p.2.1,p.2.2)
  map_add' p q := by ext <;> simp <;> ring
  map_smul' a p := by ext <;> simp

/-- Orthogonality alone is insufficient: the improper reflection is rejected. -/
theorem reflection_not_proper : ¬ IsProperRotation reflectionX := by
  intro h
  have hd := h.2
  norm_num [reflectionX,axisX,axisY,axisZ,det] at hd

theorem antipodal_first_axis_covered : ∃ q : QuaternionCoords,
    qNormSq q = 1 ∧ qAction q axisX = (-1,0,0) :=
  quaternion_maps_first_axis _ (by norm_num [dot])

theorem antipodal_second_axis_covered : ∃ q : QuaternionCoords,
    qNormSq q = 1 ∧ qAction q axisX = axisX ∧ qAction q axisY = (0,-1,0) :=
  quaternion_fixes_first_maps_second _ rfl (by norm_num [dot])

theorem false_affine_margin_rejected : ¬ (0 < (-2 : ℚ)+phiLower) := by
  norm_num [phiLower]

theorem zero_margin_is_not_strict : ¬ (0 < (0 : ℚ)+0*phiLower) := by norm_num

theorem missing_partition_child_rejected :
    (partitionLeaves (fun _ => (0,1)) (.split 0 (1/2) .leaf .leaf)).length ≠ 1 := by
  norm_num [partitionLeaves]

end Phinopert
#print axioms Phinopert.reflection_not_proper
#print axioms Phinopert.antipodal_first_axis_covered
#print axioms Phinopert.antipodal_second_axis_covered
#print axioms Phinopert.false_affine_margin_rejected
#print axioms Phinopert.zero_margin_is_not_strict
#print axioms Phinopert.missing_partition_child_rejected
