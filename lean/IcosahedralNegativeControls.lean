import IcosahedralVertexData
namespace Phinopert
-- Deliberately false zero-scaled witnesses must be rejected by the same
-- integer arithmetic used in the exhaustive multiplication/action tables.
theorem ico_bad_product_rejected :
    iqMul (icoAt 0) (icoAt 0) ≠ iqScale 0 (icoAt 0) := by decide
theorem ico_bad_vertex_action_rejected :
    iqAction (icoAt 0) (icoVertexAt 0) ≠ ipScale 0 (icoVertexAt 0) := by decide
end Phinopert
#print axioms Phinopert.ico_bad_product_rejected
#print axioms Phinopert.ico_bad_vertex_action_rejected
