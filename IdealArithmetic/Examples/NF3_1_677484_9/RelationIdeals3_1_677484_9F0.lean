import IdealArithmetic.Examples.NF3_1_677484_9.PrimesBelow3_1_677484_9F0
import IdealArithmetic.Examples.NF3_1_677484_9.ClassGroupData3_1_677484_9

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 121 ![![2, 0, 0], ![-24, -1, 1]]
  ![30659102, 6034459, 2074267] ![![121, 0, 0], ![-29, 1, 0]] where
    su := ![![242, 0, 0], ![-2904, -121, 121]]
    hsu := by decide
    w := ![![3709751342, 730169539, 250986307], ![-353953072, -69666597, -23946989]]
    hw := by decide
    g := ![![![155, 186, -44], ![-19, 702, 0]], ![![1480, -2151, 416], ![-253, -8957, 0]]]
    h := ![![![1170945955, -8419187751, -643617470], ![-10163566057, 0, 954406272]], ![![-111721748, 803287632, 61408531], ![969721445, 0, -91061368]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {121} * I2N0 =  Ideal.span {B.equivFun.symm ![30659102, 6034459, 2074267]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E2RS0 


noncomputable def E3RS0 : RelationCertificate Table 121 ![![3, 0, 0], ![-24, -1, 1]]
  ![3, -38, 13] ![![121, 0, 0], ![-29, 1, 0]] where
    su := ![![363, 0, 0], ![-2904, -121, 121]]
    hsu := by decide
    w := ![![363, -4598, 1573], ![3267, 1573, -605]]
    hw := by decide
    g := ![![![2, 448, -93], ![19, 1872, 0]], ![![-8, -4591, 949], ![0, -19149, 0]]]
    h := ![![![-49715, 188539, 15500], ![340129, 0, -32218]], ![![17325, -65671, -5399], ![-118472, 0, 11222]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {121} * I3N0 =  Ideal.span {B.equivFun.symm ![3, -38, 13]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E3RS0 


noncomputable def E11RS0 : RelationCertificate Table 121 ![![11, 0, 0], ![-26, 3, 1]]
  ![-37651, -7410, -2547] ![![121, 0, 0], ![-29, 1, 0]] where
    su := ![![1331, 0, 0], ![-3146, 363, 121]]
    hsu := by decide
    w := ![![-4555771, -896610, -308187], ![434753, 85547, 29403]]
    hw := by decide
    g := ![![![-3382, -1813732, 375279], ![-14107, -7568128, 0]], ![![9347, 4978113, -1030021], ![38985, 20772096, 0]]]
    h := ![![![-603, -999, -340], ![1193, 0, 0]], ![![69, 94, 32], ![-109, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {121} * I11N0 =  Ideal.span {B.equivFun.symm ![-37651, -7410, -2547]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 1 ![![11, 0, 0], ![4, 1, 0]]
  ![1, 0, 0] ![![11, 0, 0], ![4, 1, 0]] where
    su := ![![11, 0, 0], ![4, 1, 0]]
    hsu := by decide
    w := ![![11, 0, 0], ![4, 1, 0]]
    hw := by decide
    g := ![![![5, 1, 0], ![-11, 0, 0]], ![![-4, -1, 0], ![12, 0, 0]]]
    h := ![![![5, 1, 0], ![-11, 0, 0]], ![![-4, -1, 0], ![12, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {1} * I11N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E11RS1 


noncomputable def E13RS0 : RelationCertificate Table 121 ![![13, 0, 0], ![-30, -1, 1]]
  ![1003, 202, 71] ![![121, 0, 0], ![-29, 1, 0]] where
    su := ![![1573, 0, 0], ![-3630, -121, 121]]
    hsu := by decide
    w := ![![121363, 24442, 8591], ![-10769, -2299, -847]]
    hw := by decide
    g := ![![![14966, 7981033, -1651355], ![62441, 33302325, 0]], ![![-33983, -18151151, 3755653], ![-141793, -75739002, 0]]]
    h := ![![![31, 14, 7], ![-20, 0, 0]], ![![7, -1, -1], ![6, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {121} * I13N0 =  Ideal.span {B.equivFun.symm ![1003, 202, 71]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 11 ![![13, 0, 0], ![6, 1, 0]]
  ![-61, -12, -4] ![![11, 0, 0], ![4, 1, 0]] where
    su := ![![143, 0, 0], ![66, 11, 0]]
    hsu := by decide
    w := ![![-671, -132, -44], ![-1276, -253, -88]]
    hw := by decide
    g := ![![![43, -1117, -1688], ![-85, 3094, 0]], ![![10, -473, -714], ![-32, 1309, 0]]]
    h := ![![![-1483, -347, -100], ![3203, 216, 0]], ![![-2816, -663, -194], ![6082, 419, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {11} * I13N1 =  Ideal.span {B.equivFun.symm ![-61, -12, -4]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E13RS1 


noncomputable def E17RS0 : RelationCertificate Table 11 ![![17, 0, 0], ![4, 1, 0]]
  ![45977, 2172, -1652] ![![11, 0, 0], ![4, 1, 0]] where
    su := ![![187, 0, 0], ![44, 11, 0]]
    hsu := by decide
    w := ![![505747, 23892, -18172], ![-242308, -4807, 6424]]
    hw := by decide
    g := ![![![641217, 252774, 246964], ![256154, -361680, 0]], ![![812948, 192811, 120992], ![313146, -106860, 0]]]
    h := ![![![1311733, 350607, 34736], ![-5563371, -98694, 0]], ![![-627788, -167777, -16658], ![2662592, 47295, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N0 : Ideal.span {11} * I17N0 =  Ideal.span {B.equivFun.symm ![45977, 2172, -1652]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E17RS0 


noncomputable def E17RS1 : RelationCertificate Table 11 ![![17, 0, 0], ![-2, 1, 0]]
  ![-103, 3, 1] ![![11, 0, 0], ![4, 1, 0]] where
    su := ![![187, 0, 0], ![-22, 11, 0]]
    hsu := by decide
    w := ![![-1133, 33, 11], ![-154, -55, 22]]
    hw := by decide
    g := ![![![7, 157, 235], ![21, -429, 0]], ![![12, -13, -22], ![4, 42, 0]]]
    h := ![![![-2409, 1216, -43], ![-20425, 122, 0]], ![![-326, 165, -8], ![-2764, 23, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {11} * I17N1 =  Ideal.span {B.equivFun.symm ![-103, 3, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E17RS1 


noncomputable def E19RS1 : RelationCertificate Table 11 ![![19, 0, 0], ![-7, 1, 0]]
  ![79, 15, 5] ![![11, 0, 0], ![4, 1, 0]] where
    su := ![![209, 0, 0], ![-77, 11, 0]]
    hsu := by decide
    w := ![![869, 165, 55], ![1606, 319, 110]]
    hw := by decide
    g := ![![![-13, 130, 199], ![16, -364, 0]], ![![7, -36, -55], ![5, 100, 0]]]
    h := ![![![7412, -1147, 77], ![20107, -243, 0]], ![![13696, -2119, 142], ![37154, -448, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {11} * I19N1 =  Ideal.span {B.equivFun.symm ![79, 15, 5]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E19RS1 


noncomputable def E29RS1 : RelationCertificate Table 11 ![![29, 0, 0], ![-2, 1, 0]]
  ![7327, 453, -300] ![![11, 0, 0], ![4, 1, 0]] where
    su := ![![319, 0, 0], ![-22, 11, 0]]
    hsu := by decide
    w := ![![80597, 4983, -3300], ![-48092, -1661, 1518]]
    hw := by decide
    g := ![![![-31513, 379539, 577716], ![23052, -1062015, 0]], ![![-10422, -15970, -21864], ![-5239, 38555, 0]]]
    h := ![![![164529, -82472, 1038], ![2382007, -5067, 0]], ![![-98184, 49221, -624], ![-1421482, 3039, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {11} * I29N1 =  Ideal.span {B.equivFun.symm ![7327, 453, -300]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E29RS1 
