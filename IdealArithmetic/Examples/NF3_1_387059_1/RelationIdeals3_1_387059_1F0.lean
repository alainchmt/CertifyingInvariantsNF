import IdealArithmetic.Examples.NF3_1_387059_1.PrimesBelow3_1_387059_1F0
import IdealArithmetic.Examples.NF3_1_387059_1.ClassGroupData3_1_387059_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 1024 ![![2, 0, 0], ![0, 1, 0]]
  ![8622, -129, 292] ![![1024, 0, 0], ![119, 1, 0]] where
    su := ![![2048, 0, 0], ![0, 1024, 0]]
    hsu := by decide
    w := ![![8828928, -132096, 299008], ![1028096, -15360, 34816]]
    hw := by decide
    g := ![![![230357193, 13867453619, 470081580], ![40313390, -120341627814, 24573]], ![![230357233, 13867451112, 470081495], ![40312680, -120341606052, 24573]]]
    h := ![![![3635, -104, -1206], ![755, 676, 0]], ![![423, -12, -141], ![88, 79, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {1024} * I2N0 =  Ideal.span {B.equivFun.symm ![8622, -129, 292]} * (J0 ^ 10) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_10 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 1 ![![2, 0, 0], ![1, 1, 0]]
  ![1, 0, 0] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![2, 0, 0], ![1, 1, 0]]
    hsu := by decide
    w := ![![2, 0, 0], ![1, 1, 0]]
    hw := by decide
    g := ![![![0, -1, 0], ![2, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![0, -1, 0], ![2, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {1} * I2N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS1 


noncomputable def E7RS0 : RelationCertificate Table 2 ![![7, 0, 0], ![0, 1, 0]]
  ![0, 1, 0] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![14, 0, 0], ![0, 2, 0]]
    hsu := by decide
    w := ![![0, 2, 0], ![2, 0, 4]]
    hw := by decide
    g := ![![![0, 8, -2], ![43, 0, 2]], ![![0, -1, 0], ![2, 0, 0]]]
    h := ![![![0, 0, 0], ![1, 0, 0]], ![![-1, 2, -2], ![-10, 4, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {2} * I7N0 =  Ideal.span {B.equivFun.symm ![0, 1, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 1024 ![![7, 0, 0], ![19, 3, 1]]
  ![-62, 121, -4] ![![1024, 0, 0], ![119, 1, 0]] where
    su := ![![7168, 0, 0], ![19456, 3072, 1024]]
    hsu := by decide
    w := ![![-63488, 123904, -4096], ![-7168, 14336, 0]]
    hw := by decide
    g := ![![![13453154, 809541936, 27524170], ![2354787, -7025372376, -688104]], ![![36435854, 2192509439, 74544628], ![6375585, -19027050420, -1863615]]]
    h := ![![![-17, 16, -1], ![3, 0, 0]], ![![-1, 2, 0], ![0, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {1024} * I7N1 =  Ideal.span {B.equivFun.symm ![-62, 121, -4]} * (J0 ^ 10) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_10 E7RS1 


noncomputable def E11RS0 : RelationCertificate Table 256 ![![11, 0, 0], ![4, 1, 0]]
  ![62, 7, 4] ![![256, 0, 0], ![119, 1, 0]] where
    su := ![![2816, 0, 0], ![1024, 256, 0]]
    hsu := by decide
    w := ![![15872, 1792, 1024], ![7424, 768, 512]]
    hw := by decide
    g := ![![![-10752, -863657, -29290], ![-8363, 1873774, 26]], ![![-5059, -398716, -13522], ![-3656, 865045, 12]]]
    h := ![![![-106, -190, -260], ![-51, 716, 0]], ![![-53, -90, -122], ![-15, 336, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {256} * I11N0 =  Ideal.span {B.equivFun.symm ![62, 7, 4]} * (J0 ^ 8) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 64 ![![11, 0, 0], ![-4, 1, 0]]
  ![2, -7, -4] ![![64, 0, 0], ![-9, 1, 0]] where
    su := ![![704, 0, 0], ![-256, 64, 0]]
    hsu := by decide
    w := ![![128, -448, -256], ![-64, 192, 0]]
    hw := by decide
    g := ![![![6, 9, 0], ![19, 24, 12]], ![![7, -4, 0], ![58, -8, -4]]]
    h := ![![![4, -11, 8], ![-1, -23, 0]], ![![-1, 5, -4], ![3, 11, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {64} * I11N1 =  Ideal.span {B.equivFun.symm ![2, -7, -4]} * (J0 ^ 6) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6 E11RS1 


noncomputable def E11RS2 : RelationCertificate Table 256 ![![11, 0, 0], ![-1, 1, 0]]
  ![-818, 15, -28] ![![256, 0, 0], ![119, 1, 0]] where
    su := ![![2816, 0, 0], ![-256, 256, 0]]
    hsu := by decide
    w := ![![-209408, 3840, -7168], ![-97536, 1792, -3328]]
    hw := by decide
    g := ![![![-38, -183, 0], ![76, 393, -13]], ![![-50, 14, 0], ![108, -31, 1]]]
    h := ![![![-58, -15, 28], ![12, -84, 0]], ![![-27, -7, 13], ![6, -39, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N2 : Ideal.span {256} * I11N2 =  Ideal.span {B.equivFun.symm ![-818, 15, -28]} * (J0 ^ 8) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8 E11RS2 


noncomputable def E13RS0 : RelationCertificate Table 16 ![![13, 0, 0], ![4, 1, 0]]
  ![590, -9, 20] ![![16, 0, 0], ![7, 1, 0]] where
    su := ![![208, 0, 0], ![64, 16, 0]]
    hsu := by decide
    w := ![![9440, -144, 320], ![4272, -64, 144]]
    hw := by decide
    g := ![![![2867403, 11032310, 7435832], ![1944018, -29743380, 23]], ![![1245107, 4790540, 3228848], ![844148, -12915414, 10]]]
    h := ![![![2444, 4008, 5456], ![1068, -17727, 0]], ![![1103, 1813, 2469], ![493, -8022, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {16} * I13N0 =  Ideal.span {B.equivFun.symm ![590, -9, 20]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 32 ![![13, 0, 0], ![-3, 1, 0]]
  ![-110, 1, -4] ![![32, 0, 0], ![-9, 1, 0]] where
    su := ![![416, 0, 0], ![-96, 32, 0]]
    hsu := by decide
    w := ![![-3520, 32, -128], ![960, 0, 32]]
    hw := by decide
    g := ![![![525933321863, -2960261937990, 1187125875679], ![-240426932307, -9496960543620, 26549607]], ![![-121326173569, 682895033995, -273854943316], ![55463456141, 2190828828375, -6124659]]]
    h := ![![![25789, -55526, 56312], ![-10221, -183015, 0]], ![![-7017, 15109, -15323], ![2783, 49800, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {32} * I13N1 =  Ideal.span {B.equivFun.symm ![-110, 1, -4]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E13RS1 


noncomputable def E13RS2 : RelationCertificate Table 4 ![![13, 0, 0], ![-2, 1, 0]]
  ![-2, 1, 0] ![![4, 0, 0], ![-1, 1, 0]] where
    su := ![![52, 0, 0], ![-8, 4, 0]]
    hsu := by decide
    w := ![![-8, 4, 0], ![4, -4, 4]]
    hw := by decide
    g := ![![![-82, 355, -13], ![110, 0, 51]], ![![7, -28, 1], ![-8, 0, -4]]]
    h := ![![![-10, 17, -24], ![14, 78, 0]], ![![7, -10, 13], ![3, -42, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N2 : Ideal.span {4} * I13N2 =  Ideal.span {B.equivFun.symm ![-2, 1, 0]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E13RS2 


noncomputable def E17RS1 : RelationCertificate Table 4 ![![17, 0, 0], ![2, 1, 0]]
  ![2, 1, 0] ![![4, 0, 0], ![-1, 1, 0]] where
    su := ![![68, 0, 0], ![8, 4, 0]]
    hsu := by decide
    w := ![![8, 4, 0], ![0, 0, 4]]
    hw := by decide
    g := ![![![13, 0, 0], ![29, 0, 1]], ![![1, 0, 0], ![0, 0, 0]]]
    h := ![![![0, 0, 0], ![1, 0, 0]], ![![-8, -4, -15], ![4, 64, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {4} * I17N1 =  Ideal.span {B.equivFun.symm ![2, 1, 0]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E17RS1 
