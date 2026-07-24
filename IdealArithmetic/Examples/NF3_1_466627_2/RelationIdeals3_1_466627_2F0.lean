import IdealArithmetic.Examples.NF3_1_466627_2.PrimesBelow3_1_466627_2F0
import IdealArithmetic.Examples.NF3_1_466627_2.ClassGroupData3_1_466627_2

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 2048 ![![2, 0, 0], ![-9, -1, 1]]
  ![101, -15, -9] ![![2048, 0, 0], ![681, 1, 0]] where
    su := ![![4096, 0, 0], ![-18432, -2048, 2048]]
    hsu := by decide
    w := ![![206848, -30720, -18432], ![67584, -10240, -6144]]
    hw := by decide
    g := ![![![-680, -1, 0], ![2045, 0, 0]], ![![-334824, 2287286465, 3358718], ![1006930, -6878654460, 0]]]
    h := ![![![10, -12, 0], ![-9, 0, 0]], ![![3, -4, 0], ![-3, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {2048} * I2N0 =  Ideal.span {B.equivFun.symm ![101, -15, -9]} * (J0 ^ 11*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_11J1_0 E2RS0 


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

lemma R2N1 : Ideal.span {1} * I2N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS1 


noncomputable def E3RS0 : RelationCertificate Table 4608 ![![3, 0, 0], ![-10, -1, 1]]
  ![899, -169, 1] ![![4608, 0, 0], ![169, 1, 0]] where
    su := ![![13824, 0, 0], ![-46080, -4608, 4608]]
    hsu := by decide
    w := ![![4142592, -778752, 4608], ![152064, -27648, 0]]
    hw := by decide
    g := ![![![-18264, 2294201087, 13575155], ![497991, -62554314242, 0]], ![![79878, -10059908230, -59526087], ![-2177977, 274296208886, 0]]]
    h := ![![![43, -82, 26], ![-77, 0, 0]], ![![11, -2, 0], ![0, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {4608} * I3N0 =  Ideal.span {B.equivFun.symm ![899, -169, 1]} * (J0 ^ 3*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_2 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 4096 ![![3, 0, 0], ![1, 1, 0]]
  ![101, -15, -9] ![![12288, 0, 0], ![-1367, 1, 0]] where
    su := ![![12288, 0, 0], ![4096, 4096, 0]]
    hsu := by decide
    w := ![![1241088, -184320, -110592], ![-139264, 20480, 12288]]
    hw := by decide
    g := ![![![-601481, -67286107204, 49221732], ![-5406729, -604836642816, 0]], ![![911, -5469, 4], ![8189, -49155, 0]]]
    h := ![![![164, 59, 2], ![-189, -33, 0]], ![![-20, -9, -1], ![26, 6, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {4096} * I3N1 =  Ideal.span {B.equivFun.symm ![101, -15, -9]} * (J0 ^ 9*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_9J1_1 E3RS1 


noncomputable def E5RS0 : RelationCertificate Table 24 ![![5, 0, 0], ![-8, -1, 1]]
  ![13, 1, -1] ![![24, 0, 0], ![1, 1, 0]] where
    su := ![![120, 0, 0], ![-192, -24, 24]]
    hsu := by decide
    w := ![![312, 24, -24], ![-120, 0, 0]]
    hw := by decide
    g := ![![![-15, 8622, 8637], ![359, -207288, 0]], ![![23, -14371, -14395], ![-577, 345480, 0]]]
    h := ![![![1, 0, 0], ![-1, 0, 0]], ![![7, 1, -1], ![5, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {24} * I5N0 =  Ideal.span {B.equivFun.symm ![13, 1, -1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 576 ![![5, 0, 0], ![1, 1, 0]]
  ![43, 31, -7] ![![576, 0, 0], ![169, 1, 0]] where
    su := ![![2880, 0, 0], ![576, 576, 0]]
    hsu := by decide
    w := ![![24768, 17856, -4032], ![6336, 5184, -1152]]
    hw := by decide
    g := ![![![36304292991, -77406982396448, -458030752750], ![-123735341792, 263825713583999, 0]], ![![-5842, 12167628, 71998], ![19911, -41470850, 0]]]
    h := ![![![7, 7, 1], ![8, -12, 0]], ![![2, 2, 0], ![1, -2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {576} * I5N1 =  Ideal.span {B.equivFun.symm ![43, 31, -7]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E5RS1 


noncomputable def E7RS0 : RelationCertificate Table 256 ![![7, 0, 0], ![0, 1, 0]]
  ![-119, 5, 3] ![![256, 0, 0], ![-87, 1, 0]] where
    su := ![![1792, 0, 0], ![0, 256, 0]]
    hsu := by decide
    w := ![![-30464, 1280, 768], ![10752, -512, -256]]
    hw := by decide
    g := ![![![728, 600727, -6905], ![2142, 1767681, 0]], ![![-230, -200271, 2302], ![-677, -589311, 0]]]
    h := ![![![-17, 0, 0], ![5, 3, 0]], ![![6, 0, 0], ![-2, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {256} * I7N0 =  Ideal.span {B.equivFun.symm ![-119, 5, 3]} * (J0 ^ 8*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8J1_0 E7RS0 


noncomputable def E13RS0 : RelationCertificate Table 24576 ![![13, 0, 0], ![-15, 5, 1]]
  ![-6869, -1697, -199] ![![24576, 0, 0], ![-1367, 1, 0]] where
    su := ![![319488, 0, 0], ![-368640, 122880, 24576]]
    hsu := by decide
    w := ![![-168812544, -41705472, -4890624], ![9363456, 2310144, 270336]]
    hw := by decide
    g := ![![![-111690962, -49501432196820, 36211728075], ![-2007986161, -889939429171203, 0]], ![![126512202, 56069566433675, -41016508066], ![2274443216, 1008021702230022, 0]]]
    h := ![![![-263, -219, -33], ![230, 0, 0]], ![![27, 8, 1], ![-2, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {24576} * I13N0 =  Ideal.span {B.equivFun.symm ![-6869, -1697, -199]} * (J0 ^ 10*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_10J1_1 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 2304 ![![13, 0, 0], ![-5, 1, 0]]
  ![167, 107, 13] ![![2304, 0, 0], ![169, 1, 0]] where
    su := ![![29952, 0, 0], ![-11520, 2304, 0]]
    hsu := by decide
    w := ![![384768, 246528, 29952], ![29952, 18432, 2304]]
    hw := by decide
    g := ![![![-3142518, 99238216553, 587208492], ![42842375, -1352928365565, 0]], ![![1047450, -33079405518, -195736164], ![-14280028, 450976121855, 0]]]
    h := ![![![2353544, -520018, 9865], ![6119181, -128232, 0]], ![![183406, -40515, 767], ![476853, -9970, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {2304} * I13N1 =  Ideal.span {B.equivFun.symm ![167, 107, 13]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E13RS1 


noncomputable def E17RS1 : RelationCertificate Table 1536 ![![17, 0, 0], ![-2, 1, 0]]
  ![185, -139, 19] ![![1536, 0, 0], ![169, 1, 0]] where
    su := ![![26112, 0, 0], ![-3072, 1536, 0]]
    hsu := by decide
    w := ![![284160, -213504, 29184], ![33792, -23040, 3072]]
    hw := by decide
    g := ![![![-44, 545869, 3230], ![401, -4961273, 0]], ![![-133, -49011, -290], ![1209, 445442, 0]]]
    h := ![![![635805, -321769, 1933], ![5404250, -32842, 0]], ![![75546, -38231, 229], ![642130, -3891, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {1536} * I17N1 =  Ideal.span {B.equivFun.symm ![185, -139, 19]} * (J0 ^ 6*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6J1_1 E17RS1 


noncomputable def E19RS0 : RelationCertificate Table 16 ![![19, 0, 0], ![0, 1, 0]]
  ![-19, -7, -1] ![![16, 0, 0], ![-7, 1, 0]] where
    su := ![![304, 0, 0], ![0, 16, 0]]
    hsu := by decide
    w := ![![-304, -112, -16], ![0, 16, 0]]
    hw := by decide
    g := ![![![-1, 0, 0], ![-7, -1, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![-1, 0, 0], ![-7, -1, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N0 : Ideal.span {16} * I19N0 =  Ideal.span {B.equivFun.symm ![-19, -7, -1]} * (J0 ^ 4*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_0 E19RS0 


noncomputable def E23RS1 : RelationCertificate Table 128 ![![23, 0, 0], ![9, 1, 0]]
  ![-9, -5, -3] ![![128, 0, 0], ![41, 1, 0]] where
    su := ![![2944, 0, 0], ![1152, 128, 0]]
    hsu := by decide
    w := ![![-1152, -640, -384], ![-768, -256, -128]]
    hw := by decide
    g := ![![![4567627525, -2012541253455, -49089089244], ![-14259910322, 6283403423233, 0]], ![![1588742908, -700015639924, -17074497311], ![-4959977859, 2185535655808, 0]]]
    h := ![![![-5040, -721, -18], ![12879, 411, 0]], ![![-3324, -477, -12], ![8494, 275, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {128} * I23N1 =  Ideal.span {B.equivFun.symm ![-9, -5, -3]} * (J0 ^ 7*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7J1_0 E23RS1 


noncomputable def E29RS1 : RelationCertificate Table 384 ![![29, 0, 0], ![-11, 1, 0]]
  ![289, 61, 11] ![![384, 0, 0], ![169, 1, 0]] where
    su := ![![11136, 0, 0], ![-4224, 384, 0]]
    hsu := by decide
    w := ![![110976, 23424, 4224], ![50304, 10752, 1920]]
    hw := by decide
    g := ![![![-559, 475395, 2813], ![1271, -1080195, 0]], ![![72, -169845, -1005], ![-164, 385921, 0]]]
    h := ![![![1311, -123, 1], ![3430, -18, 0]], ![![597, -51, 0], ![1562, 5, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {384} * I29N1 =  Ideal.span {B.equivFun.symm ![289, 61, 11]} * (J0 ^ 4*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_1 E29RS1 
