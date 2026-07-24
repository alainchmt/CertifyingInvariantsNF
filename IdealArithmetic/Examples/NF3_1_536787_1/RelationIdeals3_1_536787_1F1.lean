import IdealArithmetic.Examples.NF3_1_536787_1.PrimesBelow3_1_536787_1F1
import IdealArithmetic.Examples.NF3_1_536787_1.ClassGroupData3_1_536787_1

set_option linter.all false

noncomputable section


noncomputable def E41RS1 : RelationCertificate Table 5 ![![41, 0, 0], ![4, 1, 0]]
  ![4, 1, 0] ![![5, 0, 0], ![1, 1, 1]] where
    su := ![![205, 0, 0], ![20, 5, 0]]
    hsu := by decide
    w := ![![20, 5, 0], ![145, 5, 5]]
    hw := by decide
    g := ![![![3, -1, 0], ![1, 0, 0]], ![![0, -1, -1], ![5, 0, 0]]]
    h := ![![![60, 15, 0], ![-614, 0, 0]], ![![465, 116, 0], ![-4759, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {5} * I41N1 =  Ideal.span {B.equivFun.symm ![4, 1, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E41RS1 


noncomputable def E53RS1 : RelationCertificate Table 20 ![![53, 0, 0], ![-8, 1, 0]]
  ![3169, 609, 117] ![![20, 0, 0], ![6, 1, 1]] where
    su := ![![1060, 0, 0], ![-160, 20, 0]]
    hsu := by decide
    w := ![![63380, 12180, 2340], ![121380, 23320, 4480]]
    hw := by decide
    g := ![![![3563033, 111664, -26105], ![1073197, -551070, 0]], ![![-465935, -14604, 3413], ![-140326, 72063, 0]]]
    h := ![![![11373, -1425, 5], ![74950, -148, 0]], ![![21793, -2734, 10], ![143620, -306, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {20} * I53N1 =  Ideal.span {B.equivFun.symm ![3169, 609, 117]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E53RS1 


noncomputable def E59RS1 : RelationCertificate Table 20 ![![59, 0, 0], ![27, 1, 0]]
  ![-91, -71, 17] ![![20, 0, 0], ![6, 1, 1]] where
    su := ![![1180, 0, 0], ![540, 20, 0]]
    hsu := by decide
    w := ![![-1820, -1420, 340], ![-8160, 1880, -60]]
    hw := by decide
    g := ![![![-24674177129, -773246527, 180787072], ![-7431876098, 3816133011, 0]], ![![-10873391745, -340753543, 79669059], ![-3275071731, 1681689652, 0]]]
    h := ![![![-27029, -1334, -12], ![59060, 725, 0]], ![![-118374, -5785, -52], ![258654, 3065, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {20} * I59N1 =  Ideal.span {B.equivFun.symm ![-91, -71, 17]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E59RS1 


noncomputable def E71RS1 : RelationCertificate Table 8 ![![71, 0, 0], ![1, 1, 0]]
  ![83, 15, 3] ![![8, 0, 0], ![3, 1, 0]] where
    su := ![![568, 0, 0], ![8, 8, 0]]
    hsu := by decide
    w := ![![664, 120, 24], ![672, 128, 24]]
    hw := by decide
    g := ![![![-441104, 10733667, 3626901], ![1176300, -29015211, 0]], ![![-1, 0, 0], ![1, 0, 0]]]
    h := ![![![2, 1, 0], ![-59, 3, 0]], ![![2, 1, 0], ![-58, 3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {8} * I71N1 =  Ideal.span {B.equivFun.symm ![83, 15, 3]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E71RS1 


noncomputable def E79RS0 : RelationCertificate Table 10 ![![79, 0, 0], ![-32, 1, 0]]
  ![785, 151, 29] ![![10, 0, 0], ![-4, 1, 1]] where
    su := ![![790, 0, 0], ![-320, 10, 0]]
    hsu := by decide
    w := ![![7850, 1510, 290], ![22240, 4270, 820]]
    hw := by decide
    g := ![![![1019088, 6737, 48580], ![-402095, -83687, 0]], ![![-384553, -2544, -18333], ![151743, 31580, 0]]]
    h := ![![![317119, -10952, 33], ![782863, -2578, 0]], ![![898320, -31041, 94], ![2217658, -7344, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N0 : Ideal.span {10} * I79N0 =  Ideal.span {B.equivFun.symm ![785, 151, 29]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E79RS0 


noncomputable def E79RS2 : RelationCertificate Table 40 ![![79, 0, 0], ![-22, 1, 0]]
  ![-23, -3, 1] ![![40, 0, 0], ![-14, 1, 1]] where
    su := ![![3160, 0, 0], ![-880, 40, 0]]
    hsu := by decide
    w := ![![-920, -120, 40], ![40, 160, -40]]
    hw := by decide
    g := ![![![-5632039, 578550, -94450], ![1983329, 1794667, 0]], ![![1269199, -130378, 21284], ![-446927, -404432, 0]]]
    h := ![![![-149, 29, -1], ![-534, 80, 0]], ![![39, 20, -1], ![140, 78, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N2 : Ideal.span {40} * I79N2 =  Ideal.span {B.equivFun.symm ![-23, -3, 1]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E79RS2 
