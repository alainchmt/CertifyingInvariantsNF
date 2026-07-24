import IdealArithmetic.Examples.NF3_1_456435_2.PrimesBelow3_1_456435_2F0
import IdealArithmetic.Examples.NF3_1_456435_2.ClassGroupData3_1_456435_2

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 1 ![![2, 0, 0], ![0, 1, 0]]
  ![1, 0, 0] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![2, 0, 0], ![0, 1, 0]]
    hsu := by decide
    w := ![![2, 0, 0], ![0, 1, 0]]
    hw := by decide
    g := ![![![156, 13, -3], ![8, 0, -2]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![156, 13, -3], ![8, 0, -2]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {1} * I2N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 4 ![![2, 0, 0], ![1, 1, 0]]
  ![197, -1, -8] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![8, 0, 0], ![4, 4, 0]]
    hsu := by decide
    w := ![![788, -4, -32], ![-848, 56, 0]]
    hw := by decide
    g := ![![![-118, -17, -14], ![-59, 0, 0]], ![![-940, -131, -113], ![-501, 0, 0]]]
    h := ![![![82, -17, -4], ![33, 0, 0]], ![![-90, 23, 0], ![-32, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {4} * I2N1 =  Ideal.span {B.equivFun.symm ![197, -1, -8]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E2RS1 


noncomputable def E3RS0 : RelationCertificate Table 25 ![![3, 0, 0], ![-1, 1, 0]]
  ![-67, -14, -6] ![![25, 0, 0], ![1, 1, 0]] where
    su := ![![75, 0, 0], ![-25, 25, 0]]
    hsu := by decide
    w := ![![-1675, -350, -150], ![-1025, -225, -100]]
    hw := by decide
    g := ![![![-9196, -18437, -36962], ![-1097, 115506, 0]], ![![-301, -595, -1192], ![-34, 3726, 0]]]
    h := ![![![5900, 5913, 23678], ![7, -8880, 0]], ![![3589, 3597, 14404], ![4, -5402, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {25} * I3N0 =  Ideal.span {B.equivFun.symm ![-67, -14, -6]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E3RS0 


noncomputable def E5RS0 : RelationCertificate Table 1 ![![5, 0, 0], ![1, 1, 0]]
  ![1, 0, 0] ![![5, 0, 0], ![1, 1, 0]] where
    su := ![![5, 0, 0], ![1, 1, 0]]
    hsu := by decide
    w := ![![5, 0, 0], ![1, 1, 0]]
    hw := by decide
    g := ![![![6, 11, 24], ![5, -15, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![6, 11, 24], ![5, -15, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {1} * I5N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 5 ![![5, 0, 0], ![2, 1, 0]]
  ![-8, -1, 1] ![![5, 0, 0], ![1, 1, 0]] where
    su := ![![25, 0, 0], ![10, 5, 0]]
    hsu := by decide
    w := ![![-40, -5, 5], ![145, 5, -10]]
    hw := by decide
    g := ![![![-16, -30, -61], ![-4, 38, 0]], ![![-16, -20, -39], ![-3, 24, 0]]]
    h := ![![![4, 21, 37], ![9, -23, 0]], ![![-21, -82, -138], ![-19, 86, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {5} * I5N1 =  Ideal.span {B.equivFun.symm ![-8, -1, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E5RS1 


noncomputable def E7RS0 : RelationCertificate Table 100 ![![7, 0, 0], ![0, 1, 0]]
  ![97, -1, -4] ![![100, 0, 0], ![26, 1, 0]] where
    su := ![![700, 0, 0], ![0, 100, 0]]
    hsu := by decide
    w := ![![9700, -100, -400], ![1900, 0, -100]]
    hw := by decide
    g := ![![![-59977466655, -964576889603, -266159790968], ![-25239910190, 3326997588278, -69975]], ![![-7197307532, -115749411833, -31939225986], ![-3028793970, 399240348966, -8397]]]
    h := ![![![-19303, -28396, -77268], ![-4056, 67609, 0]], ![![-3781, -5563, -15135], ![-788, 13243, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {100} * I7N0 =  Ideal.span {B.equivFun.symm ![97, -1, -4]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E7RS0 


noncomputable def E11RS0 : RelationCertificate Table 100 ![![11, 0, 0], ![-7, 3, 1]]
  ![-6231, -177, 392] ![![100, 0, 0], ![26, 1, 0]] where
    su := ![![1100, 0, 0], ![-700, 300, 100]]
    hsu := by decide
    w := ![![-623100, -17700, 39200], ![-101600, -4700, 7600]]
    hw := by decide
    g := ![![![273989, 4408051, 1216324], ![115353, -15204210, 36]], ![![-175352, -2816319, -777124], ![-73666, 9713802, -23]]]
    h := ![![![-408, -84, 13], ![249, 0, 0]], ![![-65, -16, 3], ![43, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {100} * I11N0 =  Ideal.span {B.equivFun.symm ![-6231, -177, 392]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 10 ![![11, 0, 0], ![1, 1, 0]]
  ![91, -3, -2] ![![10, 0, 0], ![-4, 1, 0]] where
    su := ![![110, 0, 0], ![10, 10, 0]]
    hsu := by decide
    w := ![![910, -30, -20], ![-680, 60, -10]]
    hw := by decide
    g := ![![![-132682, 74379, -640720], ![60516, 800719, -209]], ![![20, 6, -1], ![-6, 4, 0]]]
    h := ![![![1758, 3544, 7178], ![493, -9870, 0]], ![![-1385, -2791, -5651], ![-373, 7770, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {10} * I11N1 =  Ideal.span {B.equivFun.symm ![91, -3, -2]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E11RS1 


noncomputable def E19RS1 : RelationCertificate Table 2 ![![19, 0, 0], ![4, 1, 0]]
  ![15, -1, 0] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![38, 0, 0], ![8, 2, 0]]
    hsu := by decide
    w := ![![30, -2, 0], ![-2, 12, -8]]
    hw := by decide
    g := ![![![151105, 13256, -2927], ![6629, 0, -1950]], ![![34854, 3056, -677], ![1529, 0, -450]]]
    h := ![![![-235, -891, -1024], ![-96, 2432, 0]], ![![33, 129, 148], ![19, -352, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {2} * I19N1 =  Ideal.span {B.equivFun.symm ![15, -1, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E19RS1 


noncomputable def E23RS0 : RelationCertificate Table 100 ![![23, 0, 0], ![-9, 1, 0]]
  ![-1167, 11, 44] ![![100, 0, 0], ![26, 1, 0]] where
    su := ![![2300, 0, 0], ![-900, 100, 0]]
    hsu := by decide
    w := ![![-116700, 1100, 4400], ![-23500, -100, 1100]]
    hw := by decide
    g := ![![![1400641597, 22525532337, 6215565934], ![589422179, -77694574394, 69]], ![![-568377027, -9140807088, -2522261774], ![-239186074, 31528272250, -28]]]
    h := ![![![958307, -3469487, 4656468], ![-525828, -13387340, 0]], ![![192455, -696747, 935117], ![-105580, -2688460, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N0 : Ideal.span {100} * I23N0 =  Ideal.span {B.equivFun.symm ![-1167, 11, 44]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E23RS0 


noncomputable def E23RS1 : RelationCertificate Table 100 ![![23, 0, 0], ![-7, 1, 0]]
  ![3, 1, 4] ![![100, 0, 0], ![26, 1, 0]] where
    su := ![![2300, 0, 0], ![-700, 100, 0]]
    hsu := by decide
    w := ![![300, 100, 400], ![700, 100, 100]]
    hw := by decide
    g := ![![![-410317, -6600184, -1821204], ![-172617, 22765248, -69]], ![![130541, 2100058, 579474], ![54978, -7243488, 22]]]
    h := ![![![6749, -15017, 30268], ![-2688, -87020, 0]], ![![15973, -35565, 71687], ![-6404, -206100, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {100} * I23N1 =  Ideal.span {B.equivFun.symm ![3, 1, 4]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E23RS1 


noncomputable def E29RS0 : RelationCertificate Table 50 ![![29, 0, 0], ![6, 1, 0]]
  ![49539, 10663, 4702] ![![50, 0, 0], ![-24, 1, 0]] where
    su := ![![1450, 0, 0], ![300, 50, 0]]
    hsu := by decide
    w := ![![2476950, 533150, 235100], ![-438800, -94450, -41650]]
    hw := by decide
    g := ![![![-9267033345, 132984266181, -50714814879], ![7107861390, 316967700594, 31889]], ![![-2527372747, 36268436195, -13831313134], ![1938507664, 86445736440, 8697]]]
    h := ![![![-13541, -73011, -65226], ![-5306, 237032, 0]], ![![2398, 12934, 11555], ![944, -41991, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N0 : Ideal.span {50} * I29N0 =  Ideal.span {B.equivFun.symm ![49539, 10663, 4702]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E29RS0 


noncomputable def E29RS2 : RelationCertificate Table 20 ![![29, 0, 0], ![-1, 1, 0]]
  ![-289, -83, 68] ![![20, 0, 0], ![6, 1, 0]] where
    su := ![![580, 0, 0], ![-20, 20, 0]]
    hsu := by decide
    w := ![![-5780, -1660, 1360], ![8640, 120, -460]]
    hw := by decide
    g := ![![![-11049253297384, -57966697081701, -51805081413579], ![-6213110843281, 129514555258718, -4937932221]], ![![762011566939, 3997672282688, 3572736562434], ![428487084228, -8931969110148, 340544412]]]
    h := ![![![-316503, -316497, -1265972], ![16, 4589157, 0]], ![![477779, 477763, 1911053], ![19, -6927570, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N2 : Ideal.span {20} * I29N2 =  Ideal.span {B.equivFun.symm ![-289, -83, 68]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E29RS2 
