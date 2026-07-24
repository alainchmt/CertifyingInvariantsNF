import IdealArithmetic.Examples.NF3_1_136971_1.PrimesBelow3_1_136971_1F2
import IdealArithmetic.Examples.NF3_1_136971_1.ClassGroupData3_1_136971_1

set_option linter.all false

noncomputable section


noncomputable def E83RS1 : RelationCertificate Table 2 ![![83, 0, 0], ![-38, 1, 0]]
  ![-19, -3, -1] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![166, 0, 0], ![-76, 2, 0]]
    hsu := by decide
    w := ![![-38, -6, -2], ![-90, -16, -4]]
    hw := by decide
    g := ![![![2425, -12140, -14563], ![-4855, 29128, 0]], ![![-1075, 5379, 6454], ![2154, -12909, 0]]]
    h := ![![![-1501, 77, -1], ![-3278, 82, 0]], ![![-3535, 130, -1], ![-7720, 81, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {2} * I83N1 =  Ideal.span {B.equivFun.symm ![-19, -3, -1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E83RS1 


noncomputable def E97RS1 : RelationCertificate Table 7 ![![97, 0, 0], ![40, 1, 0]]
  ![92, 18, 5] ![![7, 0, 0], ![2, 1, 0]] where
    su := ![![679, 0, 0], ![280, 7, 0]]
    hsu := by decide
    w := ![![644, 126, 35], ![539, 98, 28]]
    hw := by decide
    g := ![![![-202, 5007, 2550], ![664, -17848, 0]], ![![-82, 2052, 1045], ![270, -7314, 0]]]
    h := ![![![556, 12, 0], ![-1346, 5, 0]], ![![421, 9, 0], ![-1019, 4, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {7} * I97N1 =  Ideal.span {B.equivFun.symm ![92, 18, 5]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E97RS1 


noncomputable def E101RS1 : RelationCertificate Table 196 ![![101, 0, 0], ![24, 1, 0]]
  ![-115, -33, -1] ![![196, 0, 0], ![-33, 1, 0]] where
    su := ![![19796, 0, 0], ![4704, 196, 0]]
    hsu := by decide
    w := ![![-22540, -6468, -196], ![3724, 980, 0]]
    hw := by decide
    g := ![![![24931508, 29846006191, -904447324], ![148078050, 177271675499, 0]], ![![5842051, 6993616456, -211933136], ![34698243, 41538894655, 0]]]
    h := ![![![-348575, -15748, -51], ![1466915, 5150, 0]], ![![57551, 2590, 8], ![-242193, -808, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {196} * I101N1 =  Ideal.span {B.equivFun.symm ![-115, -33, -1]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E101RS1 


noncomputable def E103RS0 : RelationCertificate Table 4 ![![103, 0, 0], ![-46, 1, 0]]
  ![23, 5, 1] ![![4, 0, 0], ![-1, 1, 0]] where
    su := ![![412, 0, 0], ![-184, 4, 0]]
    hsu := by decide
    w := ![![92, 20, 4], ![48, 12, 4]]
    hw := by decide
    g := ![![![0, -89, 92], ![-21, -366, 0]], ![![1, 39, -41], ![12, 163, 0]]]
    h := ![![![5083, -110, 0], ![11381, 1, 0]], ![![2644, -57, 0], ![5920, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N0 : Ideal.span {4} * I103N0 =  Ideal.span {B.equivFun.symm ![23, 5, 1]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E103RS0 


noncomputable def E103RS1 : RelationCertificate Table 49 ![![103, 0, 0], ![-40, 1, 0]]
  ![34, 17, 2] ![![49, 0, 0], ![16, 1, 0]] where
    su := ![![5047, 0, 0], ![-1960, 49, 0]]
    hsu := by decide
    w := ![![1666, 833, 98], ![686, 294, 49]]
    hw := by decide
    g := ![![![-52, 7995, 500], ![159, -24495, 0]], ![![5, -3007, -188], ![-15, 9210, 0]]]
    h := ![![![74078, -2051, 5], ![190750, -513, 0]], ![![30498, -842, 2], ![78532, -205, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {49} * I103N1 =  Ideal.span {B.equivFun.symm ![34, 17, 2]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E103RS1 


noncomputable def E103RS2 : RelationCertificate Table 14 ![![103, 0, 0], ![-17, 1, 0]]
  ![-55, -3, 5] ![![14, 0, 0], ![-5, 1, 0]] where
    su := ![![1442, 0, 0], ![-238, 14, 0]]
    hsu := by decide
    w := ![![-770, -42, 70], ![630, -70, -28]]
    hw := by decide
    g := ![![![72051844, 3184689764, -639820021], ![201745044, 8957480325, 0]], ![![-12590813, -556513936, 111806419], ![-35254261, -1565289870, 0]]]
    h := ![![![-13247, 814, -2], ![-80258, 211, 0]], ![![10891, -641, 0], ![65984, -2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N2 : Ideal.span {14} * I103N2 =  Ideal.span {B.equivFun.symm ![-55, -3, 5]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E103RS2 
