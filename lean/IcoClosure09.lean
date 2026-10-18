import IcosahedralData
namespace Phinopert
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem ico_closure_row_09 : IcoClosureRow 9 := by unfold IcoClosureRow; decide
end Phinopert
#print axioms Phinopert.ico_closure_row_09
