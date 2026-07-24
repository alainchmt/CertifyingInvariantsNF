import IdealArithmetic.Examples.NF3_1_45227_1.PrimesBelow3_1_45227_1F0
import IdealArithmetic.Examples.NF3_1_45227_1.ClassGroupData3_1_45227_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 1 ![![2, 0, 0], ![0, 1, 0]]
  ![1, 0, 0] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![2, 0, 0], ![0, 1, 0]]
    hsu := by decide
    w := ![![2, 0, 0], ![0, 1, 0]]
    hw := by decide
    g := ![![![0, 0, -3], ![0, 2, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![0, 0, -3], ![0, 2, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {1} * I2N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 4 ![![2, 0, 0], ![12, 1, 1]]
  ![748, -9, 47] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![8, 0, 0], ![48, 4, 4]]
    hsu := by decide
    w := ![![2992, -36, 188], ![320, -4, 20]]
    hw := by decide
    g := ![![![851, 0, 2554], ![3, -3405, 0]], ![![5117, -4, 15346], ![0, -20460, 0]]]
    h := ![![![8, -35, -7], ![61, 0, 0]], ![![-2, -4, -1], ![7, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {4} * I2N1 =  Ideal.span {B.equivFun.symm ![748, -9, 47]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E2RS1 


noncomputable def E3RS0 : RelationCertificate Table 4 ![![3, 0, 0], ![1, 1, 0]]
  ![0, 7, 11] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![12, 0, 0], ![4, 4, 0]]
    hsu := by decide
    w := ![![0, 28, 44], ![84, -176, 32]]
    hw := by decide
    g := ![![![0, -4904, -233], ![-1225, 567, -1309]], ![![0, -2538, -381], ![-631, 648, -677]]]
    h := ![![![-19, 37, -1], ![8, 0, 7]], ![![177, -343, 46], ![-55, 0, -65]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {4} * I3N0 =  Ideal.span {B.equivFun.symm ![0, 7, 11]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 4 ![![3, 0, 0], ![12, 0, 1]]
  ![28, -61, 7] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![12, 0, 0], ![48, 0, 4]]
    hsu := by decide
    w := ![![112, -244, 28], ![-12, -84, -176]]
    hw := by decide
    g := ![![![11267, -128, 710], ![-28, -3, 0]], ![![44045, -497, 2775], ![-123, -11, 0]]]
    h := ![![![32, -431, 47], ![174, -308, 0]], ![![-10, 37, -20], ![-17, 33, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {4} * I3N1 =  Ideal.span {B.equivFun.symm ![28, -61, 7]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E3RS1 


noncomputable def E3RS2 : RelationCertificate Table 4 ![![3, 0, 0], ![-11, 1, -1]]
  ![0, 1, 1] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![12, 0, 0], ![-44, 4, -4]]
    hsu := by decide
    w := ![![0, 4, 4], ![8, -16, 4]]
    hw := by decide
    g := ![![![0, 33, -13], ![11, 16, 9]], ![![0, -116, 44], ![-29, -54, -31]]]
    h := ![![![9, 1, 2], ![3, -1, 0]], ![![9, -11, -4], ![-1, 6, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N2 : Ideal.span {4} * I3N2 =  Ideal.span {B.equivFun.symm ![0, 1, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E3RS2 


noncomputable def E5RS0 : RelationCertificate Table 4 ![![5, 0, 0], ![11, -2, 1]]
  ![-48, 1, -3] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![20, 0, 0], ![44, -8, 4]]
    hsu := by decide
    w := ![![-192, 4, -12], ![-20, 0, 0]]
    hw := by decide
    g := ![![![2, -1, 6], ![3, -8, 0]], ![![4, 0, 13], ![1, -17, 0]]]
    h := ![![![-3, -1, 0], ![-3, 0, 0]], ![![-1, 0, 0], ![0, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {4} * I5N0 =  Ideal.span {B.equivFun.symm ![-48, 1, -3]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 2 ![![5, 0, 0], ![0, 1, 0]]
  ![80, -1, 5] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![10, 0, 0], ![0, 2, 0]]
    hsu := by decide
    w := ![![160, -2, 10], ![34, 0, 2]]
    hw := by decide
    g := ![![![28, 0, 85], ![2, -57, 0]], ![![9, 1, 29], ![1, -19, 0]]]
    h := ![![![15, -2, -2], ![9, 5, 0]], ![![3, 0, -1], ![0, 2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {2} * I5N1 =  Ideal.span {B.equivFun.symm ![80, -1, 5]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E5RS1 


noncomputable def E7RS0 : RelationCertificate Table 2 ![![7, 0, 0], ![2, 1, 0]]
  ![14, -27, 9] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![14, 0, 0], ![4, 2, 0]]
    hsu := by decide
    w := ![![28, -54, 18], ![36, -130, -72]]
    hw := by decide
    g := ![![![-12403, 118, -810], ![61, 21, 0]], ![![-4301, 41, -279], ![21, 6, 0]]]
    h := ![![![-111, -256, -390], ![-61, 913, 0]], ![![-181, -424, -651], ![-111, 1507, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {2} * I7N0 =  Ideal.span {B.equivFun.symm ![14, -27, 9]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E7RS0 


noncomputable def E17RS1 : RelationCertificate Table 4 ![![17, 0, 0], ![-6, 1, 0]]
  ![366776, -4395, 23041] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![68, 0, 0], ![-24, 4, 0]]
    hsu := by decide
    w := ![![1467104, -17580, 92164], ![156892, -1880, 9856]]
    hw := by decide
    g := ![![![909, 85, 2843], ![23, -3794, 0]], ![![-185, -31, -593], ![-4, 813, 0]]]
    h := ![![![14622770, -111769007, 56230895], ![-11735624, -318634058, 0]], ![![1563759, -11952570, 6013328], ![-1255004, -34074704, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {4} * I17N1 =  Ideal.span {B.equivFun.symm ![366776, -4395, 23041]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E17RS1 


noncomputable def E19RS1 : RelationCertificate Table 2 ![![19, 0, 0], ![7, 1, 0]]
  ![64, -191, -65] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![38, 0, 0], ![14, 2, 0]]
    hsu := by decide
    w := ![![128, -382, -130], ![-646, 1104, -638]]
    hw := by decide
    g := ![![![771010, -7387, 49867], ![-3692, -975, 0]], ![![301449, -2888, 19598], ![-1443, -450, 0]]]
    h := ![![![-178, -1651, -710], ![-147, 4475, 0]], ![![805, 7554, 3224], ![701, -20525, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {2} * I19N1 =  Ideal.span {B.equivFun.symm ![64, -191, -65]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E19RS1 


noncomputable def E23RS1 : RelationCertificate Table 2 ![![23, 0, 0], ![1, 1, 0]]
  ![-747990, 8963, -46989] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![46, 0, 0], ![2, 2, 0]]
    hsu := by decide
    w := ![![-1495980, 17926, -93978], ![-319960, 3834, -20100]]
    hw := by decide
    g := ![![![66, -128, 15], ![-63, 69, 0]], ![![32, -68, -15], ![-34, 3, 0]]]
    h := ![![![-16179, 16732, 46989], ![39, -375912, 0]], ![![-3461, 3578, 10050], ![23, -80400, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {2} * I23N1 =  Ideal.span {B.equivFun.symm ![-747990, 8963, -46989]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E23RS1 
