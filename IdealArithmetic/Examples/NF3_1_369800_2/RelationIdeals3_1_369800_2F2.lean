import IdealArithmetic.Examples.NF3_1_369800_2.PrimesBelow3_1_369800_2F2
import IdealArithmetic.Examples.NF3_1_369800_2.ClassGroupData3_1_369800_2

set_option linter.all false

noncomputable section


noncomputable def E101RS1 : RelationCertificate Table 14 ![![101, 0, 0], ![-45, 1, 0]]
  ![200, 58, 9] ![![14, 0, 0], ![-44, -3, 1]] where
    su := ![![1414, 0, 0], ![-630, 14, 0]]
    hsu := by decide
    w := ![![2800, 812, 126], ![2954, 840, 126]]
    hw := by decide
    g := ![![![81449, 19155, 4697], ![-259721, -38784, 0]], ![![-36463, -8580, -2105], ![116372, 17376, 0]]]
    h := ![![![1738, -114392, 5085], ![-1810, -256788, 0]], ![![1834, -120691, 5365], ![-1909, -270928, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {14} * I101N1 =  Ideal.span {B.equivFun.symm ![200, 58, 9]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E101RS1 


noncomputable def E103RS1 : RelationCertificate Table 14 ![![103, 0, 0], ![33, 1, 0]]
  ![-141, -11, 3] ![![14, 0, 0], ![-44, -3, 1]] where
    su := ![![1442, 0, 0], ![462, 14, 0]]
    hsu := by decide
    w := ![![-1974, -154, 42], ![294, 84, -14]]
    hw := by decide
    g := ![![![-10234890, -2407220, -590427], ![32640572, 4874919, 0]], ![![-3326839, -782469, -191920], ![10609885, 1584601, 0]]]
    h := ![![![-376, -14634, -887], ![-215, 45682, 0]], ![![42, 2161, 131], ![74, -6747, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {14} * I103N1 =  Ideal.span {B.equivFun.symm ![-141, -11, 3]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E103RS1 


noncomputable def E107RS0 : RelationCertificate Table 2 ![![107, 0, 0], ![17, 1, 0]]
  ![97, 27, 4] ![![2, 0, 0], ![-45, -4, 1]] where
    su := ![![214, 0, 0], ![34, 2, 0]]
    hsu := by decide
    w := ![![194, 54, 8], ![-80, -26, -4]]
    hw := by decide
    g := ![![![19000, -73680, 14257], ![-272737, 0, 11102]], ![![4390, -17003, 3290], ![-62942, 0, 2562]]]
    h := ![![![-379, -6765, -796], ![-114, 42588, 0]], ![![146, 2787, 328], ![111, -17549, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N0 : Ideal.span {2} * I107N0 =  Ideal.span {B.equivFun.symm ![97, 27, 4]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E107RS0 


noncomputable def E107RS2 : RelationCertificate Table 2 ![![107, 0, 0], ![-4, 1, 0]]
  ![-633, -179, -27] ![![2, 0, 0], ![-46, -3, 1]] where
    su := ![![214, 0, 0], ![-8, 2, 0]]
    hsu := by decide
    w := ![![-1266, -358, -54], ![-7764, -2198, -332]]
    hw := by decide
    g := ![![![-1, 53, -4], ![-57, 0, 0]], ![![14, -4, 0], ![7, 0, 0]]]
    h := ![![![94053, -377215, 188639], ![-6974, -10092200, 0]], ![![576782, -2313334, 1156862], ![-43161, -61892200, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N2 : Ideal.span {2} * I107N2 =  Ideal.span {B.equivFun.symm ![-633, -179, -27]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E107RS2 


noncomputable def E109RS1 : RelationCertificate Table 49 ![![109, 0, 0], ![-29, 1, 0]]
  ![-547, -32, 10] ![![49, 0, 0], ![-24, 1, 0]] where
    su := ![![5341, 0, 0], ![-1421, 49, 0]]
    hsu := by decide
    w := ![![-26803, -1568, 490], ![16366, 931, -294]]
    hw := by decide
    g := ![![![-1387, 54660, -4558], ![1816, 111672, 0]], ![![381, -14391, 1200], ![-446, -29400, 0]]]
    h := ![![![344171, -11498954, 793156], ![-196959, -43226997, 0]], ![![-210148, 7022057, -484356], ![120377, 26397399, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {49} * I109N1 =  Ideal.span {B.equivFun.symm ![-547, -32, 10]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E109RS1 
