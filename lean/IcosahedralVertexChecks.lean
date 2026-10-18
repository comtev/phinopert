import IcoVertex00
import IcoVertex01
import IcoVertex02
import IcoVertex03
import IcoVertex04
import IcoVertex05
import IcoVertex06
import IcoVertex07
import IcoVertex08
import IcoVertex09
import IcoVertex10
import IcoVertex11
import IcoVertex12
import IcoVertex13
import IcoVertex14
import IcoVertex15
import IcoVertex16
import IcoVertex17
import IcoVertex18
import IcoVertex19
import IcoVertex20
import IcoVertex21
import IcoVertex22
import IcoVertex23
import IcoVertex24
import IcoVertex25
import IcoVertex26
import IcoVertex27
import IcoVertex28
import IcoVertex29
import IcoVertex30
import IcoVertex31
import IcoVertex32
import IcoVertex33
import IcoVertex34
import IcoVertex35
import IcoVertex36
import IcoVertex37
import IcoVertex38
import IcoVertex39
import IcoVertex40
import IcoVertex41
import IcoVertex42
import IcoVertex43
import IcoVertex44
import IcoVertex45
import IcoVertex46
import IcoVertex47
import IcoVertex48
import IcoVertex49
import IcoVertex50
import IcoVertex51
import IcoVertex52
import IcoVertex53
import IcoVertex54
import IcoVertex55
import IcoVertex56
import IcoVertex57
import IcoVertex58
import IcoVertex59
import Mathlib.Tactic.FinCases
namespace Phinopert
theorem ico_vertex_checks : ∀ i : Fin 60, IcoVertexRow i.val := by
  intro i
  fin_cases i
  · exact ico_vertex_row_00
  · exact ico_vertex_row_01
  · exact ico_vertex_row_02
  · exact ico_vertex_row_03
  · exact ico_vertex_row_04
  · exact ico_vertex_row_05
  · exact ico_vertex_row_06
  · exact ico_vertex_row_07
  · exact ico_vertex_row_08
  · exact ico_vertex_row_09
  · exact ico_vertex_row_10
  · exact ico_vertex_row_11
  · exact ico_vertex_row_12
  · exact ico_vertex_row_13
  · exact ico_vertex_row_14
  · exact ico_vertex_row_15
  · exact ico_vertex_row_16
  · exact ico_vertex_row_17
  · exact ico_vertex_row_18
  · exact ico_vertex_row_19
  · exact ico_vertex_row_20
  · exact ico_vertex_row_21
  · exact ico_vertex_row_22
  · exact ico_vertex_row_23
  · exact ico_vertex_row_24
  · exact ico_vertex_row_25
  · exact ico_vertex_row_26
  · exact ico_vertex_row_27
  · exact ico_vertex_row_28
  · exact ico_vertex_row_29
  · exact ico_vertex_row_30
  · exact ico_vertex_row_31
  · exact ico_vertex_row_32
  · exact ico_vertex_row_33
  · exact ico_vertex_row_34
  · exact ico_vertex_row_35
  · exact ico_vertex_row_36
  · exact ico_vertex_row_37
  · exact ico_vertex_row_38
  · exact ico_vertex_row_39
  · exact ico_vertex_row_40
  · exact ico_vertex_row_41
  · exact ico_vertex_row_42
  · exact ico_vertex_row_43
  · exact ico_vertex_row_44
  · exact ico_vertex_row_45
  · exact ico_vertex_row_46
  · exact ico_vertex_row_47
  · exact ico_vertex_row_48
  · exact ico_vertex_row_49
  · exact ico_vertex_row_50
  · exact ico_vertex_row_51
  · exact ico_vertex_row_52
  · exact ico_vertex_row_53
  · exact ico_vertex_row_54
  · exact ico_vertex_row_55
  · exact ico_vertex_row_56
  · exact ico_vertex_row_57
  · exact ico_vertex_row_58
  · exact ico_vertex_row_59

end Phinopert
#print axioms Phinopert.ico_vertex_checks
