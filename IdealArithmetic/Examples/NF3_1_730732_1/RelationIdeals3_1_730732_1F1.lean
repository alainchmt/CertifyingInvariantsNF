import IdealArithmetic.Examples.NF3_1_730732_1.PrimesBelow3_1_730732_1F1
import IdealArithmetic.Examples.NF3_1_730732_1.ClassGroupData3_1_730732_1

set_option linter.all false

noncomputable section


noncomputable def E37RS1 : RelationCertificate Table 3 ![![37, 0, 0], ![-3, 1, 0]]
  ![1342, 25329, 21932] ![![3, 0, 0], ![24, -2, 1]] where
    su := ![![111, 0, 0], ![-9, 3, 0]]
    hsu := by decide
    w := ![![4026, 75987, 65796], ![389088, -284700, -381693]]
    hw := by decide
    g := ![![![-4969929478, -9658254535, 4258483668], ![-31901104834, 0, 0]], ![![757841879, 1472743213, -649356765], ![4864454073, 0, 0]]]
    h := ![![![1270, -3051, 3086], ![-159, -46125, 0]], ![![-216752, 665900, -449723], ![35580, 8256260, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {3} * I37N1 =  Ideal.span {B.equivFun.symm ![1342, 25329, 21932]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E37RS1 


noncomputable def E41RS1 : RelationCertificate Table 3 ![![41, 0, 0], ![-15, 1, 0]]
  ![-41, 2, -1] ![![3, 0, 0], ![24, -2, 1]] where
    su := ![![123, 0, 0], ![-45, 3, 0]]
    hsu := by decide
    w := ![![-123, 6, -3], ![-1341, 57, -33]]
    hw := by decide
    g := ![![![-22, -1, -1], ![2, 0, 0]], ![![-21, 3, -1], ![3, 0, 0]]]
    h := ![![![-221, 4502, -601], ![220, 12320, 0]], ![![-2507, 49079, -6551], ![2130, 134290, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {3} * I41N1 =  Ideal.span {B.equivFun.symm ![-41, 2, -1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E41RS1 


noncomputable def E61RS1 : RelationCertificate Table 3 ![![61, 0, 0], ![21, 1, 0]]
  ![-78855591, 3518528, -1932216] ![![3, 0, 0], ![24, -2, 1]] where
    su := ![![183, 0, 0], ![63, 3, 0]]
    hsu := by decide
    w := ![![-236566773, 10555584, -5796648], ![-2544977664, 113556630, -62360151]]
    hw := by decide
    g := ![![![613, 5320, -268], ![1324, 0, 0]], ![![197, 1895, 65], ![429, 0, 0]]]
    h := ![![![5614313093, 149553648792, 14250012904], ![4384495496, -434626359680, 0]], ![![60398598061, 1608893298579, 153301176207], ![47168260003, -4675696267672, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {3} * I61N1 =  Ideal.span {B.equivFun.symm ![-78855591, 3518528, -1932216]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E61RS1 


noncomputable def E61RS2 : RelationCertificate Table 3 ![![61, 0, 0], ![25, 1, 0]]
  ![31, 14, 2] ![![3, 0, 0], ![24, -2, 1]] where
    su := ![![183, 0, 0], ![75, 3, 0]]
    hsu := by decide
    w := ![![93, 42, 6], ![-486, -228, -39]]
    hw := by decide
    g := ![![![-149, -252, 111], ![-835, 0, 0]], ![![-71, -91, 40], ![-304, 0, 0]]]
    h := ![![![1265, 44604, 3570], ![1270, -108884, 0]], ![![-6646, -232904, -18641], ![-6532, 568544, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N2 : Ideal.span {3} * I61N2 =  Ideal.span {B.equivFun.symm ![31, 14, 2]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E61RS2 


noncomputable def E71RS0 : RelationCertificate Table 3 ![![71, 0, 0], ![0, 1, 0]]
  ![0, 1, 0] ![![3, 0, 0], ![24, -2, 1]] where
    su := ![![213, 0, 0], ![0, 3, 0]]
    hsu := by decide
    w := ![![0, 3, 0], ![-108, -12, -3]]
    hw := by decide
    g := ![![![1276, -23, -79], ![-45, 0, -20]], ![![1276, -17, -86], ![-36, 0, -21]]]
    h := ![![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 1], ![-4, -36, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N0 : Ideal.span {3} * I71N0 =  Ideal.span {B.equivFun.symm ![0, 1, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E71RS0 


noncomputable def E73RS1 : RelationCertificate Table 3 ![![73, 0, 0], ![25, 1, 0]]
  ![10587442044386, -472410526767, 259426435813] ![![3, 0, 0], ![24, -2, 1]] where
    su := ![![219, 0, 0], ![75, 3, 0]]
    hsu := by decide
    w := ![![31762326133158, -1417231580301, 778279307439], ![341698073405733, -15246531331755, 8372703523305]]
    hw := by decide
    g := ![![![-255887, -2146674, 183857], ![-554498, 0, 0]], ![![-91387, -800551, 15065], ![-192293, 0, 0]]]
    h := ![![![-832539675329113, -26338379117651658, -2107774111110909], ![-645916041107858, 76933884768766085, 0]], ![![-8956434799553519, -283347427496379967, -22675365460378207], ![-6948743801167319, 827652234754391773, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {3} * I73N1 =  Ideal.span {B.equivFun.symm ![10587442044386, -472410526767, 259426435813]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E73RS1 


noncomputable def E73RS2 : RelationCertificate Table 3 ![![73, 0, 0], ![-31, 1, 0]]
  ![-4064029, -1604192, -58256] ![![3, 0, 0], ![24, -2, 1]] where
    su := ![![219, 0, 0], ![-93, 3, 0]]
    hsu := by decide
    w := ![![-12192087, -4812576, -174768], ![67501944, 27320106, 1564131]]
    hw := by decide
    g := ![![![1331957694683, 2588444469430, -1141287844379], ![8549602629889, 0, 0]], ![![-613831086197, -1192881490525, 525961117188], ![-3940073989996, 0, 0]]]
    h := ![![![55078130, -2459897177, 158751280], ![-57086559, -5794450848, 0]], ![![-304865007, 13615876327, -878707703], ![315982119, 32073091848, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N2 : Ideal.span {3} * I73N2 =  Ideal.span {B.equivFun.symm ![-4064029, -1604192, -58256]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E73RS2 
