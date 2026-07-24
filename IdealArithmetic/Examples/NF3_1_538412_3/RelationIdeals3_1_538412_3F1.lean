import IdealArithmetic.Examples.NF3_1_538412_3.PrimesBelow3_1_538412_3F1
import IdealArithmetic.Examples.NF3_1_538412_3.ClassGroupData3_1_538412_3

set_option linter.all false

noncomputable section


noncomputable def E47RS1 : RelationCertificate Table 5 ![![47, 0, 0], ![3, 1, 0]]
  ![3, 1, 0] ![![5, 0, 0], ![-1, 1, 0]] where
    su := ![![235, 0, 0], ![15, 5, 0]]
    hsu := by decide
    w := ![![15, 5, 0], ![-5, 0, 10]]
    hw := by decide
    g := ![![![6657, 748, 47], ![-1178, 0, -233]], ![![430, 48, 3], ![-75, 0, -15]]]
    h := ![![![-20, 10, 100], ![1, -470, 0]], ![![5, -4, -34], ![28, 160, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {5} * I47N1 =  Ideal.span {B.equivFun.symm ![3, 1, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E47RS1 


noncomputable def E53RS0 : RelationCertificate Table 25 ![![53, 0, 0], ![0, 1, 0]]
  ![-162, -14, 15] ![![25, 0, 0], ![4, 1, 0]] where
    su := ![![1325, 0, 0], ![0, 25, 0]]
    hsu := by decide
    w := ![![-4050, -350, 375], ![1600, -25, -50]]
    hw := by decide
    g := ![![![4320, -6348, -31057], ![443, 77462, 308]], ![![32, -41, -202], ![8, 505, 2]]]
    h := ![![![7938, 7937, -39705], ![201, 210438, 0]], ![![-3136, -3137, 15686], ![-12, -83136, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N0 : Ideal.span {25} * I53N0 =  Ideal.span {B.equivFun.symm ![-162, -14, 15]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E53RS0 


noncomputable def E53RS1 : RelationCertificate Table 25 ![![53, 0, 0], ![18, 1, 0]]
  ![864, 33, -55] ![![25, 0, 0], ![4, 1, 0]] where
    su := ![![1325, 0, 0], ![450, 25, 0]]
    hsu := by decide
    w := ![![21600, 825, -1375], ![-4750, 325, 0]]
    hw := by decide
    g := ![![![435856770, -442264774, -2202147621], ![52046499, 5505746492, -629185]], ![![160578740, -162939662, -811317550], ![19175022, 2028432914, -231805]]]
    h := ![![![-119508, 1014734, 633955], ![-21397, -3359967, 0]], ![![27222, -231180, -144430], ![4889, 765479, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {25} * I53N1 =  Ideal.span {B.equivFun.symm ![864, 33, -55]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E53RS1 


noncomputable def E53RS2 : RelationCertificate Table 25 ![![53, 0, 0], ![-18, 1, 0]]
  ![-74, -3, 5] ![![25, 0, 0], ![4, 1, 0]] where
    su := ![![1325, 0, 0], ![-450, 25, 0]]
    hsu := by decide
    w := ![![-1850, -75, 125], ![450, -25, 0]]
    hw := by decide
    g := ![![![-103407752, 105869085, 526883565], ![-12310469, -1317208984, 120]], ![![34470984, -35291470, -175636688], ![4103701, 439091744, -40]]]
    h := ![![![-176074, -1846182, 922855], ![25023, -4891131, 0]], ![![42930, 449934, -224910], ![-6043, 1192023, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N2 : Ideal.span {25} * I53N2 =  Ideal.span {B.equivFun.symm ![-74, -3, 5]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E53RS2 


noncomputable def E61RS1 : RelationCertificate Table 5 ![![61, 0, 0], ![-17, 1, 0]]
  ![-17, 1, 0] ![![5, 0, 0], ![-1, 1, 0]] where
    su := ![![305, 0, 0], ![-85, 5, 0]]
    hsu := by decide
    w := ![![-85, 5, 0], ![15, -20, 10]]
    hw := by decide
    g := ![![![-83704, -9414, -586], ![14859, 0, 2928]], ![![24013, 2700, 168], ![-4260, 0, -840]]]
    h := ![![![-223, -2281, 1200], ![62, -7320, 0]], ![![47, 414, -218], ![12, 1330, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {5} * I61N1 =  Ideal.span {B.equivFun.symm ![-17, 1, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E61RS1 


noncomputable def E67RS0 : RelationCertificate Table 25 ![![67, 0, 0], ![-23, 1, 0]]
  ![352, 44, 35] ![![25, 0, 0], ![4, 1, 0]] where
    su := ![![1675, 0, 0], ![-575, 25, 0]]
    hsu := by decide
    w := ![![8800, 1100, 875], ![6500, 825, 650]]
    hw := by decide
    g := ![![![-1944055564, 1990342742, 9905426637], ![-231435160, -24763566581, -21]], ![![277892214, -284508722, -1415927121], ![33082419, 3539817801, 3]]]
    h := ![![![-530170, -6963426, 2784905], ![78086, -18658860, 0]], ![![-391564, -5143130, 2056908], ![57718, -13781281, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N0 : Ideal.span {25} * I67N0 =  Ideal.span {B.equivFun.symm ![352, 44, 35]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E67RS0 


noncomputable def E67RS1 : RelationCertificate Table 25 ![![67, 0, 0], ![-22, 1, 0]]
  ![1876, -53, -45] ![![25, 0, 0], ![4, 1, 0]] where
    su := ![![1675, 0, 0], ![-550, 25, 0]]
    hsu := by decide
    w := ![![46900, -1325, -1125], ![950, 1275, -800]]
    hw := by decide
    g := ![![![197596671046, -202301250630, -1006801601399], ![23523417356, 2517004013068, -16616]], ![![-66357090020, 67936985722, 338105008460], ![-7899654967, -845262524454, 5580]]]
    h := ![![![267318, 3356251, -1398205], ![-37614, 9367969, 0]], ![![2970, 37220, -15506], ![-401, 103887, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {25} * I67N1 =  Ideal.span {B.equivFun.symm ![1876, -53, -45]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E67RS1 
