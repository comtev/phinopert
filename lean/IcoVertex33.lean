import IcosahedralVertexData
namespace Phinopert
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem ico_vertex_row_33 : IcoVertexRow 33 := by unfold IcoVertexRow; decide
end Phinopert
#print axioms Phinopert.ico_vertex_row_33
