import IdealArithmetic.Examples.NF3_1_936684_4.PrimesBelow3_1_936684_4F0
import IdealArithmetic.Examples.NF3_1_936684_4.ClassGroupData3_1_936684_4

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 1 ![![2, 0, 0], ![0, 1, 0]]
  ![1, 0, 0] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![2, 0, 0], ![0, 1, 0]]
    hsu := by decide
    w := ![![2, 0, 0], ![0, 1, 0]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {1} * I2N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 0*J2^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_0J2_1 E2RS0 


noncomputable def E3RS0 : RelationCertificate Table 10 ![![3, 0, 0], ![1, 1, 0]]
  ![-30, -8, 1] ![![10, 0, 0], ![-2, 1, 0]] where
    su := ![![30, 0, 0], ![10, 10, 0]]
    hsu := by decide
    w := ![![-300, -80, 10], ![410, 70, -10]]
    hw := by decide
    g := ![![![66, 3162, -1596], ![313, 15961, 0]], ![![13, 5, 0], ![1, 4, 0]]]
    h := ![![![-9, -9, -7], ![-3, 22, 0]], ![![22, 11, 0], ![-25, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {10} * I3N0 =  Ideal.span {B.equivFun.symm ![-30, -8, 1]} * (J0 ^ 1*J1^ 0*J2^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0J2_1 E3RS0 


noncomputable def E5RS0 : RelationCertificate Table 25 ![![5, 0, 0], ![0, 1, 0]]
  ![125, 10, -2] ![![25, 0, 0], ![-59, 0, 1]] where
    su := ![![125, 0, 0], ![0, 25, 0]]
    hsu := by decide
    w := ![![3125, 250, -50], ![-3875, -450, 75]]
    hw := by decide
    g := ![![![51, 6, 0], ![14, 0, 0]], ![![51, 13, 1], ![5, 0, 0]]]
    h := ![![![25, 2, -1], ![0, 3, 0]], ![![-31, -4, 0], ![2, 3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {25} * I5N0 =  Ideal.span {B.equivFun.symm ![125, 10, -2]} * (J0 ^ 2*J1^ 2*J2^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2J2_0 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 1 ![![5, 0, 0], ![2, 1, 0]]
  ![1, 0, 0] ![![5, 0, 0], ![2, 1, 0]] where
    su := ![![5, 0, 0], ![2, 1, 0]]
    hsu := by decide
    w := ![![5, 0, 0], ![2, 1, 0]]
    hw := by decide
    g := ![![![3, 1, 0], ![-5, 0, 0]], ![![-2, -1, 0], ![6, 0, 0]]]
    h := ![![![3, 1, 0], ![-5, 0, 0]], ![![-2, -1, 0], ![6, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {1} * I5N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1*J2^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1J2_0 E5RS1 


noncomputable def E5RS2 : RelationCertificate Table 1 ![![5, 0, 0], ![-2, 1, 0]]
  ![1, 0, 0] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![5, 0, 0], ![-2, 1, 0]]
    hsu := by decide
    w := ![![5, 0, 0], ![-2, 1, 0]]
    hw := by decide
    g := ![![![11, -5, 0], ![25, 0, 0]], ![![-2, 3, -1], ![-4, 5, 0]]]
    h := ![![![11, -5, 0], ![25, 0, 0]], ![![-2, 3, -1], ![-4, 5, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N2 : Ideal.span {1} * I5N2 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0*J2^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0J2_0 E5RS2 


noncomputable def E7RS0 : RelationCertificate Table 50 ![![7, 0, 0], ![0, 1, 0]]
  ![0, -1, 0] ![![50, 0, 0], ![-34, 0, 1]] where
    su := ![![350, 0, 0], ![0, 50, 0]]
    hsu := by decide
    w := ![![0, -50, 0], ![-350, -50, 0]]
    hw := by decide
    g := ![![![1, 0, 0], ![-1, 0, 0]], ![![-1, 0, 0], ![0, 0, 0]]]
    h := ![![![0, 0, 0], ![-1, 0, 0]], ![![-1, 0, 0], ![-1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {50} * I7N0 =  Ideal.span {B.equivFun.symm ![0, -1, 0]} * (J0 ^ 2*J1^ 2*J2^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2J2_2 E7RS0 


noncomputable def E11RS0 : RelationCertificate Table 25 ![![11, 0, 0], ![-59, -5, 1]]
  ![-225, -75, -7] ![![25, 0, 0], ![-59, 0, 1]] where
    su := ![![275, 0, 0], ![-1475, -125, 25]]
    hsu := by decide
    w := ![![-5625, -1875, -175], ![-12975, -4325, -400]]
    hw := by decide
    g := ![![![56, -1, -1], ![31, 0, 0]], ![![48, 4, -1], ![11, 0, 0]]]
    h := ![![![1, -5, -1], ![4, 0, 0]], ![![44, -8, -3], ![17, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {25} * I11N0 =  Ideal.span {B.equivFun.symm ![-225, -75, -7]} * (J0 ^ 2*J1^ 2*J2^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2J2_0 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 5 ![![11, 0, 0], ![5, 1, 0]]
  ![5, 1, 0] ![![5, 0, 0], ![-54, -5, 1]] where
    su := ![![55, 0, 0], ![25, 5, 0]]
    hsu := by decide
    w := ![![25, 5, 0], ![80, 5, 0]]
    hw := by decide
    g := ![![![53, 5, -1], ![6, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    h := ![![![40, 8, 0], ![-87, 0, 0]], ![![146, 39, 2], ![-318, -22, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {5} * I11N1 =  Ideal.span {B.equivFun.symm ![5, 1, 0]} * (J0 ^ 1*J1^ 1*J2^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1J2_0 E11RS1 


noncomputable def E13RS0 : RelationCertificate Table 10 ![![13, 0, 0], ![-55, -4, 1]]
  ![-360, 1, 3] ![![10, 0, 0], ![-56, -4, 1]] where
    su := ![![130, 0, 0], ![-550, -40, 10]]
    hsu := by decide
    w := ![![-3600, 10, 30], ![16310, 1510, -280]]
    hw := by decide
    g := ![![![-51, -15, -10], ![313, 52, 0]], ![![233, 88, 46], ![-1325, -218, 0]]]
    h := ![![![40, 5, -1], ![16, 0, 0]], ![![7, 3, 0], ![-28, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {10} * I13N0 =  Ideal.span {B.equivFun.symm ![-360, 1, 3]} * (J0 ^ 1*J1^ 0*J2^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0J2_2 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 50 ![![13, 0, 0], ![4, 1, 0]]
  ![300, 98, 9] ![![50, 0, 0], ![-22, 1, 0]] where
    su := ![![650, 0, 0], ![200, 50, 0]]
    hsu := by decide
    w := ![![15000, 4900, 450], ![-3450, -1100, -100]]
    hw := by decide
    g := ![![![428, 57159, -2599], ![973, 129952, 0]], ![![25142914, 3410292112, -155065226], ![57142984, 7753261299, 0]]]
    h := ![![![34892, 10006, 321], ![-113324, -4164, 0]], ![![-8021, -2301, -74], ![26051, 960, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {50} * I13N1 =  Ideal.span {B.equivFun.symm ![300, 98, 9]} * (J0 ^ 2*J1^ 0*J2^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0J2_1 E13RS1 


noncomputable def E17RS0 : RelationCertificate Table 50 ![![17, 0, 0], ![-8, 1, 0]]
  ![50, 6, -1] ![![50, 0, 0], ![-506, -25, 9]] where
    su := ![![850, 0, 0], ![-400, 50, 0]]
    hsu := by decide
    w := ![![2500, 300, -50], ![2350, -800, 50]]
    hw := by decide
    g := ![![![109, 5, -2], ![11, 0, 0]], ![![530, 213, 52], ![-564, -99, 0]]]
    h := ![![![21666, -3156, 56], ![46034, -953, 0]], ![![20751, -3018, 53], ![44090, -900, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N0 : Ideal.span {50} * I17N0 =  Ideal.span {B.equivFun.symm ![50, 6, -1]} * (J0 ^ 2*J1^ 2*J2^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2J2_1 E17RS0 


noncomputable def E17RS1 : RelationCertificate Table 10 ![![17, 0, 0], ![-7, 1, 0]]
  ![230, 76, 7] ![![10, 0, 0], ![2, 1, 0]] where
    su := ![![170, 0, 0], ![-70, 10, 0]]
    hsu := by decide
    w := ![![2300, 760, 70], ![2910, 970, 90]]
    hw := by decide
    g := ![![![-58354, 3033242, 1531206], ![291657, -15312055, 0]], ![![27467, -1427405, -720566], ![-137237, 7205656, 0]]]
    h := ![![![716, -100, 1], ![1706, -10, 0]], ![![902, -131, 2], ![2149, -25, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {10} * I17N1 =  Ideal.span {B.equivFun.symm ![230, 76, 7]} * (J0 ^ 0*J1^ 1*J2^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1J2_1 E17RS1 


noncomputable def E17RS2 : RelationCertificate Table 10 ![![17, 0, 0], ![-2, 1, 0]]
  ![-40, -12, -1] ![![10, 0, 0], ![-2, 1, 0]] where
    su := ![![170, 0, 0], ![-20, 10, 0]]
    hsu := by decide
    w := ![![-400, -120, -10], ![-270, -100, -10]]
    hw := by decide
    g := ![![![255, 12768, -6445], ![1229, 64448, 0]], ![![102350, 5322432, -2686805], ![511776, 26868051, 0]]]
    h := ![![![-844, 426, -3], ![-7154, 50, 0]], ![![-567, 286, -2], ![-4806, 33, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N2 : Ideal.span {10} * I17N2 =  Ideal.span {B.equivFun.symm ![-40, -12, -1]} * (J0 ^ 1*J1^ 0*J2^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0J2_1 E17RS2 


noncomputable def E19RS0 : RelationCertificate Table 50 ![![19, 0, 0], ![2, 1, 0]]
  ![150, -3, -1] ![![50, 0, 0], ![-72, -4, 1]] where
    su := ![![950, 0, 0], ![100, 50, 0]]
    hsu := by decide
    w := ![![7500, -150, -50], ![-10450, -650, 150]]
    hw := by decide
    g := ![![![757529, -7418, -4795], ![-1090191, -332486, 0]], ![![270584, -2647, -1713], ![-389328, -118745, 0]]]
    h := ![![![13238, 6695, 40], ![-125686, -761, 0]], ![![-18465, -9342, -57], ![175313, 1086, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N0 : Ideal.span {50} * I19N0 =  Ideal.span {B.equivFun.symm ![150, -3, -1]} * (J0 ^ 0*J1^ 2*J2^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2J2_2 E19RS0 


noncomputable def E19RS1 : RelationCertificate Table 50 ![![19, 0, 0], ![8, 1, 0]]
  ![-50, -3, 1] ![![50, 0, 0], ![-46, -4, 1]] where
    su := ![![950, 0, 0], ![400, 50, 0]]
    hsu := by decide
    w := ![![-2500, -150, 50], ![-150, 100, 0]]
    hw := by decide
    g := ![![![-2752, -350, 7], ![2577, 732, 0]], ![![-1353, -173, 3], ![1314, 366, 0]]]
    h := ![![![-10966, -1747, -47], ![26038, 894, 0]], ![![-633, -103, -3], ![1503, 57, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {50} * I19N1 =  Ideal.span {B.equivFun.symm ![-50, -3, 1]} * (J0 ^ 2*J1^ 0*J2^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0J2_2 E19RS1 


noncomputable def E19RS2 : RelationCertificate Table 10 ![![19, 0, 0], ![9, 1, 0]]
  ![10, -1, 0] ![![10, 0, 0], ![-54, 0, 1]] where
    su := ![![190, 0, 0], ![90, 10, 0]]
    hsu := by decide
    w := ![![100, -10, 0], ![-890, -30, 10]]
    hw := by decide
    g := ![![![47, -1, -1], ![9, 0, 0]], ![![46, -1, -1], ![9, 0, 0]]]
    h := ![![![262, 47, 2], ![-552, -38, 0]], ![![-2465, -436, -18], ![5194, 343, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N2 : Ideal.span {10} * I19N2 =  Ideal.span {B.equivFun.symm ![10, -1, 0]} * (J0 ^ 1*J1^ 1*J2^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1J2_2 E19RS2 


noncomputable def E23RS1 : RelationCertificate Table 5 ![![23, 0, 0], ![-3, 1, 0]]
  ![95, 2, -1] ![![5, 0, 0], ![2, 1, 0]] where
    su := ![![115, 0, 0], ![-15, 5, 0]]
    hsu := by decide
    w := ![![475, 10, -5], ![-160, 15, 0]]
    hw := by decide
    g := ![![![17, -6, -5], ![6, 28, 0]], ![![5, 1, 0], ![4, 1, 0]]]
    h := ![![![121, -39, 0], ![896, -1, 0]], ![![-40, 16, -1], ![-296, 23, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {5} * I23N1 =  Ideal.span {B.equivFun.symm ![95, 2, -1]} * (J0 ^ 0*J1^ 1*J2^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1J2_0 E23RS1 


noncomputable def E29RS0 : RelationCertificate Table 10 ![![29, 0, 0], ![-14, 1, 0]]
  ![-40, -7, 1] ![![10, 0, 0], ![-52, -4, 1]] where
    su := ![![290, 0, 0], ![-140, 10, 0]]
    hsu := by decide
    w := ![![-400, -70, 10], ![-1770, -50, 20]]
    hw := by decide
    g := ![![![94517, 46969, 19535], ![-508117, -78192, 0]], ![![-45439, -22609, -9407], ![244662, 37648, 0]]]
    h := ![![![-5836, 501, -6], ![-12086, 175, 0]], ![![-25909, 2187, -24], ![-53656, 698, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N0 : Ideal.span {10} * I29N0 =  Ideal.span {B.equivFun.symm ![-40, -7, 1]} * (J0 ^ 0*J1^ 1*J2^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1J2_2 E29RS0 


noncomputable def E29RS1 : RelationCertificate Table 10 ![![29, 0, 0], ![-9, 1, 0]]
  ![130, 43, 4] ![![10, 0, 0], ![-56, -4, 1]] where
    su := ![![290, 0, 0], ![-90, 10, 0]]
    hsu := by decide
    w := ![![1300, 430, 40], ![2170, 740, 70]]
    hw := by decide
    g := ![![![23, 1, 1], ![-33, -5, 0]], ![![17, 3, 0], ![-7, -2, 0]]]
    h := ![![![704, -75, 0], ![2254, 4, 0]], ![![1166, -133, 1], ![3733, -22, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {10} * I29N1 =  Ideal.span {B.equivFun.symm ![130, 43, 4]} * (J0 ^ 1*J1^ 0*J2^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0J2_2 E29RS1 


noncomputable def E29RS2 : RelationCertificate Table 50 ![![29, 0, 0], ![-6, 1, 0]]
  ![-100, -33, -3] ![![50, 0, 0], ![-34, 0, 1]] where
    su := ![![1450, 0, 0], ![-300, 50, 0]]
    hsu := by decide
    w := ![![-5000, -1650, -150], ![-8150, -2700, -250]]
    hw := by decide
    g := ![![![56, 3, -1], ![17, 0, 0]], ![![-9, -1, 0], ![12, 0, 0]]]
    h := ![![![-140, 27, -1], ![-660, 26, 0]], ![![-221, 39, -1], ![-1041, 24, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N2 : Ideal.span {50} * I29N2 =  Ideal.span {B.equivFun.symm ![-100, -33, -3]} * (J0 ^ 2*J1^ 2*J2^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2J2_2 E29RS2 


noncomputable def E31RS1 : RelationCertificate Table 2 ![![31, 0, 0], ![6, 1, 0]]
  ![6, 1, 0] ![![2, 0, 0], ![-56, -4, 1]] where
    su := ![![62, 0, 0], ![12, 2, 0]]
    hsu := by decide
    w := ![![12, 2, 0], ![14, 4, 2]]
    hw := by decide
    g := ![![![4, -1, 0], ![1, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    h := ![![![42, 7, 0], ![-216, 0, 0]], ![![43, 7, 0], ![-221, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {2} * I31N1 =  Ideal.span {B.equivFun.symm ![6, 1, 0]} * (J0 ^ 0*J1^ 0*J2^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_0J2_2 E31RS1 
