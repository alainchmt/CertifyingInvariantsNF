import IdealArithmetic.Examples.NF3_1_797796_1.PrimesBelow3_1_797796_1F0
import IdealArithmetic.Examples.NF3_1_797796_1.ClassGroupData3_1_797796_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 16 ![![2, 0, 0], ![-78, -4, 1]]
  ![8594, 419, -102] ![![16, 0, 0], ![-383, -13, 5]] where
    su := ![![32, 0, 0], ![-1248, -64, 16]]
    hsu := by decide
    w := ![![137504, 6704, -1632], ![-862592, -52992, 11472]]
    hw := by decide
    g := ![![![387, 1362, 334], ![-1277, 0, 31]], ![![-2439, 48382, 7588], ![23816, 0, -1085]]]
    h := ![![![2316, 16927, 7135], ![-118284, -12989, 0]], ![![-17809, -134134, -56360], ![934813, 102672, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {16} * I2N0 =  Ideal.span {B.equivFun.symm ![8594, 419, -102]} * (J0 ^ 7) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 1 ![![2, 0, 0], ![-77, -4, 1]]
  ![1, 0, 0] ![![2, 0, 0], ![-77, -4, 1]] where
    su := ![![2, 0, 0], ![-77, -4, 1]]
    hsu := by decide
    w := ![![2, 0, 0], ![-77, -4, 1]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![18, 70, 6], ![149, 0, -4]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![18, 70, 6], ![149, 0, -4]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {1} * I2N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS1 


noncomputable def E3RS0 : RelationCertificate Table 4 ![![3, 0, 0], ![-1, 1, 0]]
  ![-1442, -319, -36] ![![4, 0, 0], ![-79, -3, 1]] where
    su := ![![12, 0, 0], ![-4, 4, 0]]
    hsu := by decide
    w := ![![-5768, -1276, -144], ![-35892, -7940, -896]]
    hw := by decide
    g := ![![![214, -1945, -257], ![-2457, 0, 92]], ![![43, 1, 1], ![-35, 0, 0]]]
    h := ![![![-1048, 502, -94], ![-1702, 123, 0]], ![![-6524, 3122, -576], ![-10599, 752, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {4} * I3N0 =  Ideal.span {B.equivFun.symm ![-1442, -319, -36]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E3RS0 


noncomputable def E5RS0 : RelationCertificate Table 8 ![![5, 0, 0], ![0, 1, 0]]
  ![10, 1, 0] ![![8, 0, 0], ![-75, -5, 1]] where
    su := ![![40, 0, 0], ![0, 8, 0]]
    hsu := by decide
    w := ![![80, 8, 0], ![-40, -8, 0]]
    hw := by decide
    g := ![![![1, 0, 0], ![1, 0, 0]], ![![-1, 0, 0], ![-2, 0, 0]]]
    h := ![![![2, 0, 0], ![1, 0, 0]], ![![-1, 0, 0], ![-1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {8} * I5N0 =  Ideal.span {B.equivFun.symm ![10, 1, 0]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 8 ![![5, 0, 0], ![2, 1, 0]]
  ![484, 17, -5] ![![8, 0, 0], ![-75, -1, 1]] where
    su := ![![40, 0, 0], ![16, 8, 0]]
    hsu := by decide
    w := ![![3872, 136, -40], ![-20680, -960, 240]]
    hw := by decide
    g := ![![![0, -76, -14], ![39, 0, 0]], ![![58, -299, -56], ![160, 0, 0]]]
    h := ![![![4516, 2657, 443], ![-11048, -1110, 0]], ![![-24197, -14244, -2374], ![59200, 5950, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {8} * I5N1 =  Ideal.span {B.equivFun.symm ![484, 17, -5]} * (J0 ^ 6) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6 E5RS1 


noncomputable def E5RS2 : RelationCertificate Table 16 ![![5, 0, 0], ![-2, 1, 0]]
  ![-78827922, -17437621, -1967748] ![![16, 0, 0], ![-383, -13, 5]] where
    su := ![![80, 0, 0], ![-32, 16, 0]]
    hsu := by decide
    w := ![![-1261246752, -279001936, -31483968], ![-13550146384, -2997444448, -338246560]]
    hw := by decide
    g := ![![![757, -10039, -1685], ![-8821, 0, 318]], ![![107, -2718, 100], ![3012, 0, 0]]]
    h := ![![![-3054765402, 1665443847, -149825012], ![-7597499544, 373578656, 0]], ![![-32818731425, 17892619266, -1609638106], ![-81623386488, 4013525060, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N2 : Ideal.span {16} * I5N2 =  Ideal.span {B.equivFun.symm ![-78827922, -17437621, -1967748]} * (J0 ^ 7) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7 E5RS2 


noncomputable def E17RS1 : RelationCertificate Table 4 ![![17, 0, 0], ![-5, 1, 0]]
  ![-86, -4, 1] ![![4, 0, 0], ![-79, -5, 1]] where
    su := ![![68, 0, 0], ![-20, 4, 0]]
    hsu := by decide
    w := ![![-344, -16, 4], ![404, 48, -8]]
    hw := by decide
    g := ![![![34, 4, 0], ![1, 0, 0]], ![![26, 3, 0], ![1, 0, 0]]]
    h := ![![![-228, 52, -3], ![-758, 26, 0]], ![![288, -56, 0], ![959, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {4} * I17N1 =  Ideal.span {B.equivFun.symm ![-86, -4, 1]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E17RS1 


noncomputable def E23RS1 : RelationCertificate Table 4 ![![23, 0, 0], ![-10, 1, 0]]
  ![853718, 188852, 21311] ![![4, 0, 0], ![-79, -5, 1]] where
    su := ![![92, 0, 0], ![-40, 4, 0]]
    hsu := by decide
    w := ![![3414872, 755408, 85244], ![-9012852, -1993744, -224984]]
    hw := by decide
    g := ![![![33, -199, 39], ![997, 0, 0]], ![![65, 140, -31], ![-880, 0, 0]]]
    h := ![![![3925386, -422928, 9389], ![8943016, -97318, 0]], ![![-10360221, 1116237, -24782], ![-23603187, 256870, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {4} * I23N1 =  Ideal.span {B.equivFun.symm ![853718, 188852, 21311]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E23RS1 


noncomputable def E29RS0 : RelationCertificate Table 4 ![![29, 0, 0], ![6, 1, 0]]
  ![6, 1, 0] ![![4, 0, 0], ![-79, -3, 1]] where
    su := ![![116, 0, 0], ![24, 4, 0]]
    hsu := by decide
    w := ![![24, 4, 0], ![236, 20, 0]]
    hw := by decide
    g := ![![![-3912, 39069, 5149], ![49629, 0, -1848]], ![![-956, 9768, 1287], ![12408, 0, -462]]]
    h := ![![![-6, -1, 0], ![30, 0, 0]], ![![49, 8, 0], ![-227, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N0 : Ideal.span {4} * I29N0 =  Ideal.span {B.equivFun.symm ![6, 1, 0]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E29RS0 


noncomputable def E29RS2 : RelationCertificate Table 8 ![![29, 0, 0], ![-1, 1, 0]]
  ![-68, -5, 1] ![![8, 0, 0], ![-75, -1, 1]] where
    su := ![![232, 0, 0], ![-8, 8, 0]]
    hsu := by decide
    w := ![![-544, -40, 8], ![840, 96, -16]]
    hw := by decide
    g := ![![![22, 2, 0], ![1, 0, 0]], ![![12, 1, 0], ![1, 0, 0]]]
    h := ![![![-4, 2, -1], ![-48, 15, 0]], ![![8, -3, -2], ![127, 28, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N2 : Ideal.span {8} * I29N2 =  Ideal.span {B.equivFun.symm ![-68, -5, 1]} * (J0 ^ 6) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6 E29RS2 
