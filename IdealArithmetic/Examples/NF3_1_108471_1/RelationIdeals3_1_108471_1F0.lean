import IdealArithmetic.Examples.NF3_1_108471_1.PrimesBelow3_1_108471_1F0
import IdealArithmetic.Examples.NF3_1_108471_1.ClassGroupData3_1_108471_1

set_option linter.all false

noncomputable section


noncomputable def E3RS1 : RelationCertificate Table 5 ![![3, 0, 0], ![1, 1, 0]]
  ![-8, 5, 4] ![![5, 0, 0], ![-10, -2, 1]] where
    su := ![![15, 0, 0], ![5, 5, 0]]
    hsu := by decide
    w := ![![-40, 25, 20], ![5, -80, -55]]
    hw := by decide
    g := ![![![-40, 71, -31], ![58, 0, 0]], ![![131, -193, 84], ![-151, 0, 0]]]
    h := ![![![-6, -1, -2], ![10, 2, 0]], ![![0, -6, -2], ![1, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {5} * I3N1 =  Ideal.span {B.equivFun.symm ![-8, 5, 4]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E3RS1 


noncomputable def E5RS1 : RelationCertificate Table 5 ![![5, 0, 0], ![-7, 0, 1]]
  ![-16, 5, -2] ![![5, 0, 0], ![-10, -2, 1]] where
    su := ![![25, 0, 0], ![-35, 0, 5]]
    hsu := by decide
    w := ![![-80, 25, -10], ![-365, 110, -45]]
    hw := by decide
    g := ![![![4, -1, 0], ![-3, 0, 0]], ![![6, 4, 0], ![7, 0, 0]]]
    h := ![![![53, -5, 7], ![-67, 10, 0]], ![![224, -22, 32], ![-301, 44, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {5} * I5N1 =  Ideal.span {B.equivFun.symm ![-16, 5, -2]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E5RS1 


noncomputable def E5RS2 : RelationCertificate Table 5 ![![5, 0, 0], ![-6, 0, 1]]
  ![121, -37, 15] ![![5, 0, 0], ![-10, -2, 1]] where
    su := ![![25, 0, 0], ![-30, 0, 5]]
    hsu := by decide
    w := ![![605, -185, 75], ![2690, -825, 335]]
    hw := by decide
    g := ![![![5, 2, 1], ![0, 0, 0]], ![![-15, 7, 0], ![18, 0, 0]]]
    h := ![![![-5521, 703, -760], ![6479, -888, 0]], ![![-24628, 3135, -3388], ![28887, -3960, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N2 : Ideal.span {5} * I5N2 =  Ideal.span {B.equivFun.symm ![121, -37, 15]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E5RS2 


noncomputable def E11RS1 : RelationCertificate Table 5 ![![11, 0, 0], ![-1, 1, 0]]
  ![-425209, 130251, -52852] ![![5, 0, 0], ![-10, -2, 1]] where
    su := ![![55, 0, 0], ![-5, 5, 0]]
    hsu := by decide
    w := ![![-2126045, 651255, -264260], ![-9480635, 2904130, -1178410]]
    hw := by decide
    g := ![![![42, -188, -121], ![-32, 0, 0]], ![![201, -190, -37], ![-329, 0, 0]]]
    h := ![![![-154224, 128503, -6627], ![-1271255, 4009, 0]], ![![-687732, 573029, -29542], ![-5668925, 17856, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {5} * I11N1 =  Ideal.span {B.equivFun.symm ![-425209, 130251, -52852]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E11RS1 


noncomputable def E13RS0 : RelationCertificate Table 5 ![![13, 0, 0], ![1, 1, 0]]
  ![41, 0, -3] ![![5, 0, 0], ![-10, -2, 1]] where
    su := ![![65, 0, 0], ![5, 5, 0]]
    hsu := by decide
    w := ![![205, 0, -15], ![-635, 5, 50]]
    hw := by decide
    g := ![![![19, -23, 10], ![-17, 0, 0]], ![![-6, 16, -7], ![14, 0, 0]]]
    h := ![![![6, 3, -1], ![-37, 2, 0]], ![![-20, -10, 0], ![133, 2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {5} * I13N0 =  Ideal.span {B.equivFun.symm ![41, 0, -3]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E13RS0 


noncomputable def E13RS2 : RelationCertificate Table 5 ![![13, 0, 0], ![-5, 1, 0]]
  ![-8985392, 2752426, -1116853] ![![5, 0, 0], ![-10, -2, 1]] where
    su := ![![65, 0, 0], ![-25, 5, 0]]
    hsu := by decide
    w := ![![-44926960, 13762130, -5584265], ![-200342005, 61369225, -24901815]]
    hw := by decide
    g := ![![![2573, -1445, 296], ![-4504, 0, 0]], ![![-233, 380, 157], ![366, 0, 0]]]
    h := ![![![-1913729, -50890797, 36590539], ![-3178617, -95358772, 0]], ![![-8533872, -226936436, 163167549], ![-14174387, -425231700, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N2 : Ideal.span {5} * I13N2 =  Ideal.span {B.equivFun.symm ![-8985392, 2752426, -1116853]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E13RS2 


noncomputable def E19RS1 : RelationCertificate Table 5 ![![19, 0, 0], ![8, 1, 0]]
  ![-2959, -458, -96] ![![5, 0, 0], ![-10, -2, 1]] where
    su := ![![95, 0, 0], ![40, 5, 0]]
    hsu := by decide
    w := ![![-14795, -2290, -480], ![56740, 6870, 535]]
    hw := by decide
    g := ![![![412791, -644510, 280806], ![-511594, 0, 0]], ![![-28724, 44853, -19542], ![35604, 0, 0]]]
    h := ![![![-71509, -10112, -979], ![169464, 3701, 0]], ![![273788, 38694, 3733], ![-648828, -14164, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {5} * I19N1 =  Ideal.span {B.equivFun.symm ![-2959, -458, -96]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E19RS1 


noncomputable def E29RS1 : RelationCertificate Table 5 ![![29, 0, 0], ![-1, 1, 0]]
  ![-626, 9, 52] ![![5, 0, 0], ![-10, -2, 1]] where
    su := ![![145, 0, 0], ![-5, 5, 0]]
    hsu := by decide
    w := ![![-3130, 45, 260], ![9485, -220, -845]]
    hw := by decide
    g := ![![![3820, -5963, 2598], ![-4733, 0, 0]], ![![-1357, 2123, -925], ![1686, 0, 0]]]
    h := ![![![-86, 67, -2], ![-1868, 22, 0]], ![![262, -198, -6], ![5701, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {5} * I29N1 =  Ideal.span {B.equivFun.symm ![-626, 9, 52]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E29RS1 


noncomputable def E31RS1 : RelationCertificate Table 5 ![![31, 0, 0], ![-14, 1, 0]]
  ![317, -7, -28] ![![5, 0, 0], ![-10, -2, 1]] where
    su := ![![155, 0, 0], ![-70, 5, 0]]
    hsu := by decide
    w := ![![1585, -35, -140], ![-4745, 150, 450]]
    hw := by decide
    g := ![![![1050, -1632, 711], ![-1294, 0, 0]], ![![-779, 1230, -536], ![979, 0, 0]]]
    h := ![![![59, 3603, -1128], ![108, 6988, 0]], ![![-153, -10797, 3380], ![-271, -20938, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {5} * I31N1 =  Ideal.span {B.equivFun.symm ![317, -7, -28]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E31RS1 
