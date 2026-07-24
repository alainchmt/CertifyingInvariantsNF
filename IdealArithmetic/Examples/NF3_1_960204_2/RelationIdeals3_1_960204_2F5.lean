import IdealArithmetic.Examples.NF3_1_960204_2.PrimesBelow3_1_960204_2F5
import IdealArithmetic.Examples.NF3_1_960204_2.ClassGroupData3_1_960204_2

set_option linter.all false

noncomputable section


noncomputable def E269RS0 : RelationCertificate Table 3 ![![269, 0, 0], ![103, 1, 0]]
  ![16398, 27, 389] ![![3, 0, 0], ![29, 0, 1]] where
    su := ![![807, 0, 0], ![309, 3, 0]]
    hsu := by decide
    w := ![![49194, 81, 1167], ![495591, 816, 11757]]
    hw := by decide
    g := ![![![385, -9327, -548], ![3747, -2152, 0]], ![![141, -3534, -208], ![1421, -816, 0]]]
    h := ![![![594688, -60735311, -1786331], ![2134, 160174476, 0]], ![![5991659, -611860658, -17995885], ![19818, 1613632328, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R269N0 : Ideal.span {3} * I269N0 =  Ideal.span {B.equivFun.symm ![16398, 27, 389]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E269RS0 


noncomputable def E269RS1 : RelationCertificate Table 1089 ![![269, 0, 0], ![-88, 1, 0]]
  ![-82761, -141, -1964] ![![1089, 0, 0], ![62, 0, 1]] where
    su := ![![292941, 0, 0], ![-95832, 1089, 0]]
    hsu := by decide
    w := ![![-90126729, -153549, -2138796], ![-5232645, -8712, -124146]]
    hw := by decide
    g := ![![![-4777710122879, -1879686789922, -93734481570], ![-272095281612, 102348945711271, 0]], ![![1580729371139, 621903807690, 31012523635], ![90024090238, -33862662328726, 0]]]
    h := ![![![14612922802, 1299122823248, -43790663113], ![49017326, 3926562791811, 0]], ![![848408277, 75425461987, -2542431660], ![2846127, 227971372142, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R269N1 : Ideal.span {1089} * I269N1 =  Ideal.span {B.equivFun.symm ![-82761, -141, -1964]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E269RS1 


noncomputable def E269RS2 : RelationCertificate Table 11 ![![269, 0, 0], ![-15, 1, 0]]
  ![6, -7, -1] ![![11, 0, 0], ![0, 1, 0]] where
    su := ![![2959, 0, 0], ![-165, 11, 0]]
    hsu := by decide
    w := ![![66, -77, -11], ![-44, 55, -22]]
    hw := by decide
    g := ![![![-472, -398, 1201], ![-31, -4410, 0]], ![![23, 19, -58], ![4, 213, 0]]]
    h := ![![![-480, -7830, 1468], ![167, -131631, 0]], ![![331, 5221, -979], ![84, 87783, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R269N2 : Ideal.span {11} * I269N2 =  Ideal.span {B.equivFun.symm ![6, -7, -1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E269RS2 
