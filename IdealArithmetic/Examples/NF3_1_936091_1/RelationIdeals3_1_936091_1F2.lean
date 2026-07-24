import IdealArithmetic.Examples.NF3_1_936091_1.PrimesBelow3_1_936091_1F2
import IdealArithmetic.Examples.NF3_1_936091_1.ClassGroupData3_1_936091_1

set_option linter.all false

noncomputable section


noncomputable def E97RS0 : RelationCertificate Table 4 ![![97, 0, 0], ![0, 1, 0]]
  ![14647, -3573, 483] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![388, 0, 0], ![0, 4, 0]]
    hsu := by decide
    w := ![![58588, -14292, 1932], ![-64408, 15712, -2124]]
    hw := by decide
    g := ![![![-72013, 720149, 378057], ![144034, -1512189, 0]], ![![71992, -720094, -378050], ![-144023, 1512203, 0]]]
    h := ![![![151, -37, 0], ![16, 483, 0]], ![![-166, 40, 0], ![48, -531, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N0 : Ideal.span {4} * I97N0 =  Ideal.span {B.equivFun.symm ![14647, -3573, 483]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E97RS0 


noncomputable def E101RS0 : RelationCertificate Table 36 ![![101, 0, 0], ![18, 1, 0]]
  ![-169, -33, -1] ![![36, 0, 0], ![2, 1, 0]] where
    su := ![![3636, 0, 0], ![648, 36, 0]]
    hsu := by decide
    w := ![![-6084, -1188, -36], ![-144, -252, -36]]
    hw := by decide
    g := ![![![19, 1024, 516], ![45, -18550, 0]], ![![2, 187, 94], ![8, -3381, 0]]]
    h := ![![![-81629, -4733, -11], ![458020, 1110, 0]], ![![-1964, -127, -1], ![11020, 100, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N0 : Ideal.span {36} * I101N0 =  Ideal.span {B.equivFun.symm ![-169, -33, -1]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E101RS0 


noncomputable def E101RS1 : RelationCertificate Table 3 ![![101, 0, 0], ![29, 1, 0]]
  ![-1900415, 463590, -62669] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![303, 0, 0], ![87, 3, 0]]
    hsu := by decide
    w := ![![-5701245, 1390770, -188007], ![14058201, -3429378, 463590]]
    hw := by decide
    g := ![![![-2879, 395, 198], ![1094, 0, 0]], ![![-1172, 77, 69], ![419, -8, 0]]]
    h := ![![![-3690334, -132411, -979], ![12787011, 36210, 0]], ![![9099532, 326437, 2412], ![-31529885, -89082, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {3} * I101N1 =  Ideal.span {B.equivFun.symm ![-1900415, 463590, -62669]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E101RS1 


noncomputable def E101RS2 : RelationCertificate Table 2 ![![101, 0, 0], ![-48, 1, 0]]
  ![421, 85, 3] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![202, 0, 0], ![-96, 2, 0]]
    hsu := by decide
    w := ![![842, 170, 6], ![-582, 472, 88]]
    hw := by decide
    g := ![![![-45972, 8971, -4740], ![4487, 6448, 0]], ![![24760, -4832, 2227], ![-2416, -2821, 0]]]
    h := ![![![11777, -243, 0], ![24772, 3, 0]], ![![-8103, 192, 0], ![-17044, 44, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N2 : Ideal.span {2} * I101N2 =  Ideal.span {B.equivFun.symm ![421, 85, 3]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E101RS2 


noncomputable def E137RS0 : RelationCertificate Table 9 ![![137, 0, 0], ![15, 1, 0]]
  ![125, -6, -4] ![![9, 0, 0], ![2, 1, 0]] where
    su := ![![1233, 0, 0], ![135, 9, 0]]
    hsu := by decide
    w := ![![1125, -54, -36], ![1026, 45, -18]]
    hw := by decide
    g := ![![![-55885, 2370691, 1199273], ![250997, -10793489, 0]], ![![-6429, 272883, 138046], ![28900, -1242416, 0]]]
    h := ![![![775, 52, 0], ![-7070, -4, 0]], ![![702, 47, 0], ![-6404, -2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N0 : Ideal.span {9} * I137N0 =  Ideal.span {B.equivFun.symm ![125, -6, -4]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E137RS0 


noncomputable def E137RS1 : RelationCertificate Table 9 ![![137, 0, 0], ![57, 1, 0]]
  ![-9028859, 2202513, -297740] ![![9, 0, 0], ![2, 1, 0]] where
    su := ![![1233, 0, 0], ![513, 9, 0]]
    hsu := by decide
    w := ![![-81259731, 19822617, -2679660], ![39703842, -9685413, 1309293]]
    hw := by decide
    g := ![![![18031, -984080, -497833], ![-105334, 4481976, 0]], ![![-118108588429, 5019614908191, 2539334600622], ![531488636817, -22854011404958, 0]]]
    h := ![![![-1612595902, -40149857, -210523], ![3875729995, 28543911, 0]], ![![787920976, 19617362, 102862], ![-1893697582, -13946617, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {9} * I137N1 =  Ideal.span {B.equivFun.symm ![-9028859, 2202513, -297740]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E137RS1 


noncomputable def E137RS2 : RelationCertificate Table 9 ![![137, 0, 0], ![64, 1, 0]]
  ![-245, 60, -8] ![![9, 0, 0], ![2, 1, 0]] where
    su := ![![1233, 0, 0], ![576, 9, 0]]
    hsu := by decide
    w := ![![-2205, 540, -72], ![1062, -261, 36]]
    hw := by decide
    g := ![![![15, 18, 10], ![6, -98, 0]], ![![8, 11, 6], ![4, -58, 0]]]
    h := ![![![-1613, -85, -1], ![3449, 129, 0]], ![![710, 9, 0], ![-1518, 4, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N2 : Ideal.span {9} * I137N2 =  Ideal.span {B.equivFun.symm ![-245, 60, -8]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E137RS2 
