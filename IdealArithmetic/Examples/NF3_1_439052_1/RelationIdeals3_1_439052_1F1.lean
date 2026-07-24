import IdealArithmetic.Examples.NF3_1_439052_1.PrimesBelow3_1_439052_1F1
import IdealArithmetic.Examples.NF3_1_439052_1.ClassGroupData3_1_439052_1

set_option linter.all false

noncomputable section


noncomputable def E41RS1 : RelationCertificate Table 190 ![![41, 0, 0], ![18, 1, 0]]
  ![28, -2, 1] ![![190, 0, 0], ![-133, 9, 2]] where
    su := ![![7790, 0, 0], ![3420, 190, 0]]
    hsu := by decide
    w := ![![5320, -380, 190], ![-5320, 570, 0]]
    hw := by decide
    g := ![![![-8453, -871, 409], ![5943, -4480, 0]], ![![-3673, -385, 179], ![2664, -1967, 0]]]
    h := ![![![57728, 1533518, 170561], ![62760, -3496500, 0]], ![![-57878, -1536927, -170940], ![-62850, 3504270, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {190} * I41N1 =  Ideal.span {B.equivFun.symm ![28, -2, 1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E41RS1 


noncomputable def E47RS1 : RelationCertificate Table 5 ![![47, 0, 0], ![5, 1, 0]]
  ![222, -17, -6] ![![5, 0, 0], ![-39, 2, 1]] where
    su := ![![235, 0, 0], ![25, 5, 0]]
    hsu := by decide
    w := ![![1110, -85, -30], ![-150, 195, 35]]
    hw := by decide
    g := ![![![27, -73, 21], ![-37, 0, 0]], ![![31, 9, -4], ![10, 0, 0]]]
    h := ![![![-19819, -101280, -40548], ![-4232, 952875, 0]], ![![2845, 14564, 5831], ![656, -137025, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {5} * I47N1 =  Ideal.span {B.equivFun.symm ![222, -17, -6]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E47RS1 


noncomputable def E53RS0 : RelationCertificate Table 190 ![![53, 0, 0], ![4, 1, 0]]
  ![-1354, 284, 67] ![![190, 0, 0], ![-133, 9, 2]] where
    su := ![![10070, 0, 0], ![760, 190, 0]]
    hsu := by decide
    w := ![![-257260, 53960, 12730], ![-150480, -1330, 1900]]
    hw := by decide
    g := ![![![350711874, 35925632, -16926967], ![-243974569, 185203568, 0]], ![![30071504, 3080382, -1451382], ![-20919177, 15880058, 0]]]
    h := ![![![10201810, 41245510, 20637359], ![1548174, -546889980, 0]], ![![5934941, 23994726, 12005860], ![900655, -318155285, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N0 : Ideal.span {190} * I53N0 =  Ideal.span {B.equivFun.symm ![-1354, 284, 67]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E53RS0 


noncomputable def E59RS0 : RelationCertificate Table 190 ![![59, 0, 0], ![25, 1, 0]]
  ![1958, -186, -59] ![![190, 0, 0], ![-133, 9, 2]] where
    su := ![![11210, 0, 0], ![4750, 190, 0]]
    hsu := by decide
    w := ![![372020, -35340, -11210], ![-3610, 6460, 1140]]
    hw := by decide
    g := ![![![1705, 157, -78], ![-1167, 878, 0]], ![![726, 70, -34], ![-495, 377, 0]]]
    h := ![![![-579, -21643, -1733], ![-599, 51094, 0]], ![![1, 224, 18], ![18, -528, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N0 : Ideal.span {190} * I59N0 =  Ideal.span {B.equivFun.symm ![1958, -186, -59]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E59RS0 


noncomputable def E59RS1 : RelationCertificate Table 190 ![![59, 0, 0], ![-23, 1, 0]]
  ![-20303, 5637, -871] ![![190, 0, 0], ![-133, 9, 2]] where
    su := ![![11210, 0, 0], ![-4370, 190, 0]]
    hsu := by decide
    w := ![![-3857570, 1071030, -165490], ![2006590, -557080, 86070]]
    hw := by decide
    g := ![![![-1302, -137, 64], ![1082, -693, 0]], ![![373, 27, -16], ![-159, 161, 0]]]
    h := ![![![-117104984, 3656577692, -318121909], ![107627049, 9384595880, 0]], ![![60914432, -1902039095, 165477219], ![-55984209, -4881577734, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {190} * I59N1 =  Ideal.span {B.equivFun.symm ![-20303, 5637, -871]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E59RS1 


noncomputable def E61RS1 : RelationCertificate Table 38 ![![61, 0, 0], ![-21, 1, 0]]
  ![-400, 110, -17] ![![38, 0, 0], ![3, 1, 0]] where
    su := ![![2318, 0, 0], ![-798, 38, 0]]
    hsu := by decide
    w := ![![-15200, 4180, -646], ![3534, -988, 152]]
    hw := by decide
    g := ![![![-11, 11, 8], ![11, -150, 0]], ![![3, -3, -2], ![5, 37, 0]]]
    h := ![![![1672, -44322, 4223], ![-1258, -128810, 0]], ![![-379, 10306, -982], ![321, 29953, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {38} * I61N1 =  Ideal.span {B.equivFun.symm ![-400, 110, -17]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E61RS1 


noncomputable def E67RS1 : RelationCertificate Table 5 ![![67, 0, 0], ![-31, 1, 0]]
  ![46, -13, 2] ![![5, 0, 0], ![-39, 2, 1]] where
    su := ![![335, 0, 0], ![-155, 5, 0]]
    hsu := by decide
    w := ![![230, -65, 10], ![410, -105, 15]]
    hw := by decide
    g := ![![![36, -7, -2], ![14, 0, 0]], ![![15, 1, 0], ![-2, 0, 0]]]
    h := ![![![637, -30028, 1938], ![-719, -64922, 0]], ![![1135, -53502, 3453], ![-1281, -115674, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {5} * I67N1 =  Ideal.span {B.equivFun.symm ![46, -13, 2]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E67RS1 


noncomputable def E71RS0 : RelationCertificate Table 5 ![![71, 0, 0], ![15, 1, 0]]
  ![-397, 32, 11] ![![5, 0, 0], ![-39, 2, 1]] where
    su := ![![355, 0, 0], ![75, 5, 0]]
    hsu := by decide
    w := ![![-1985, 160, 55], ![-340, -325, -50]]
    hw := by decide
    g := ![![![19, -247, 74], ![-137, 0, 0]], ![![8, -11, 3], ![-5, 0, 0]]]
    h := ![![![1738, 28795, 3841], ![837, -136350, 0]], ![![278, 4663, 622], ![152, -22086, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N0 : Ideal.span {5} * I71N0 =  Ideal.span {B.equivFun.symm ![-397, 32, 11]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E71RS0 


noncomputable def E71RS1 : RelationCertificate Table 5 ![![71, 0, 0], ![-10, 1, 0]]
  ![-10, 1, 0] ![![5, 0, 0], ![-39, 2, 1]] where
    su := ![![355, 0, 0], ![-50, 5, 0]]
    hsu := by decide
    w := ![![-50, 5, 0], ![120, -5, -5]]
    hw := by decide
    g := ![![![27, -3, -1], ![3, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    h := ![![![320, -3299, 660], ![-70, -23430, 0]], ![![-746, 7851, -1571], ![278, 55770, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {5} * I71N1 =  Ideal.span {B.equivFun.symm ![-10, 1, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E71RS1 


noncomputable def E79RS1 : RelationCertificate Table 38 ![![79, 0, 0], ![14, 1, 0]]
  ![-86, -2, 1] ![![38, 0, 0], ![3, 1, 0]] where
    su := ![![3002, 0, 0], ![532, 38, 0]]
    hsu := by decide
    w := ![![-3268, -76, 38], ![-532, -38, 0]]
    hw := by decide
    g := ![![![-1265964, -3840206, -2563663], ![-200981, 48709598, 0]], ![![-225325, -683503, -456296], ![-35759, 8669624, 0]]]
    h := ![![![51640, 769753, 109999], ![18951, -4344960, 0]], ![![8382, 124953, 17856], ![3080, -705312, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {38} * I79N1 =  Ideal.span {B.equivFun.symm ![-86, -2, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E79RS1 
