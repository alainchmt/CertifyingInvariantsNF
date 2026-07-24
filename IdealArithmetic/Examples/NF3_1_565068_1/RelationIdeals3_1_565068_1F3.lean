import IdealArithmetic.Examples.NF3_1_565068_1.PrimesBelow3_1_565068_1F3
import IdealArithmetic.Examples.NF3_1_565068_1.ClassGroupData3_1_565068_1

set_option linter.all false

noncomputable section


noncomputable def E149RS1 : RelationCertificate Table 121 ![![149, 0, 0], ![-23, 1, 0]]
  ![197, -8, 9] ![![121, 0, 0], ![-9, 1, 0]] where
    su := ![![18029, 0, 0], ![-2783, 121, 0]]
    hsu := by decide
    w := ![![23837, -968, 1089], ![-2178, 0, -121]]
    hw := by decide
    g := ![![![-1147991, -1877871690, 1173749528], ![-15434111, -28404738576, 0]], ![![168845, 276178809, -172623481], ![2270029, 4177488240, 0]]]
    h := ![![![894, -21, -4], ![5783, 121, 0]], ![![-56, 20, -4], ![-362, 119, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R149N1 : Ideal.span {121} * I149N1 =  Ideal.span {B.equivFun.symm ![197, -8, 9]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E149RS1 


noncomputable def E167RS1 : RelationCertificate Table 33 ![![167, 0, 0], ![-49, 1, 0]]
  ![-21, -14, 2] ![![33, 0, 0], ![23, 0, 1]] where
    su := ![![5511, 0, 0], ![-1617, 33, 0]]
    hsu := by decide
    w := ![![-693, -462, 66], ![165, 66, -33]]
    hw := by decide
    g := ![![![-3927, -788, 85], ![-2699, -4329, 0]], ![![1126, 231, -26], ![826, 1269, 0]]]
    h := ![![![-10122, 245, -4], ![-34497, 134, 0]], ![![2438, -21, -3], ![8309, 100, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R167N1 : Ideal.span {33} * I167N1 =  Ideal.span {B.equivFun.symm ![-21, -14, 2]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E167RS1 


noncomputable def E173RS1 : RelationCertificate Table 3 ![![173, 0, 0], ![-2, 1, 0]]
  ![-33063, 336, -1111] ![![3, 0, 0], ![20, 0, 1]] where
    su := ![![519, 0, 0], ![-6, 3, 0]]
    hsu := by decide
    w := ![![-99189, 1008, -3333], ![-686379, 6975, -23064]]
    hw := by decide
    g := ![![![-4, -93, -25], ![-17, 0, 0]], ![![-4, 5, -3], ![2, 0, 0]]]
    h := ![![![-191, -16436, 82183], ![10, -2843754, 0]], ![![-1329, -113732, 568699], ![-562, -19678523, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R173N1 : Ideal.span {3} * I173N1 =  Ideal.span {B.equivFun.symm ![-33063, 336, -1111]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E173RS1 


noncomputable def E179RS1 : RelationCertificate Table 3 ![![179, 0, 0], ![82, 1, 0]]
  ![-336642, 3421, -11312] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![537, 0, 0], ![246, 3, 0]]
    hsu := by decide
    w := ![![-1009926, 10263, -33936], ![172398, -1752, 5793]]
    hw := by decide
    g := ![![![-78, -91, -136], ![-55, 133, 0]], ![![-54, -53, -63], ![-35, 61, 0]]]
    h := ![![![-31207830, -551186, -10343], ![68120304, 368017, 0]], ![![5327118, 94061, 1764], ![-11628008, -62765, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R179N1 : Ideal.span {3} * I179N1 =  Ideal.span {B.equivFun.symm ![-336642, 3421, -11312]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E179RS1 


noncomputable def E191RS1 : RelationCertificate Table 3 ![![191, 0, 0], ![93, 1, 0]]
  ![3, 0, -4] ![![3, 0, 0], ![20, 0, 1]] where
    su := ![![573, 0, 0], ![279, 3, 0]]
    hsu := by decide
    w := ![![9, 0, -12], ![24, 36, 39]]
    hw := by decide
    g := ![![![-127, 48, 71], ![-689, 0, 0]], ![![-61, 23, 34], ![-330, 0, 0]]]
    h := ![![![75, -74, -4], ![-154, 152, 0]], ![![76, -38, -2], ![-156, 79, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R191N1 : Ideal.span {3} * I191N1 =  Ideal.span {B.equivFun.symm ![3, 0, -4]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E191RS1 
