import IdealArithmetic.Examples.NF3_3_455700_1.PrimesBelow3_3_455700_1F0
import IdealArithmetic.Examples.NF3_3_455700_1.ClassGroupData3_3_455700_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 33 ![![2, 0, 0], ![1, 1, 0]]
  ![-95, 29, -6] ![![33, 0, 0], ![-14, 1, 0]] where
    su := ![![66, 0, 0], ![33, 33, 0]]
    hsu := by decide
    w := ![![-3135, 957, -198], ![2871, -825, 165]]
    hw := by decide
    g := ![![![-242615, 4853537, -1041676], ![250039, 11457585, -196]], ![![-242604, 4853528, -1041675], ![250024, 11457567, -196]]]
    h := ![![![-172, -110, -588], ![-141, 390, 0]], ![![146, 90, 490], ![120, -325, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {33} * I2N0 =  Ideal.span {B.equivFun.symm ![-95, 29, -6]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E2RS0 


noncomputable def E3RS0 : RelationCertificate Table 1 ![![3, 0, 0], ![1, 1, 0]]
  ![1, 0, 0] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![3, 0, 0], ![1, 1, 0]]
    hsu := by decide
    w := ![![3, 0, 0], ![1, 1, 0]]
    hw := by decide
    g := ![![![0, -1, -1], ![2, 1, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![0, -1, -1], ![2, 1, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {1} * I3N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 3 ![![3, 0, 0], ![-38, 2, 1]]
  ![-10, 1, 0] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![9, 0, 0], ![-114, 6, 3]]
    hsu := by decide
    w := ![![-30, 3, 0], ![-9, -9, 3]]
    hw := by decide
    g := ![![![-617, 190, 5], ![-141, 0, -8]], ![![8153, -2505, -71], ![1885, 0, 104]]]
    h := ![![![12, 9, 1], ![67, -10, 0]], ![![33, 1, 0], ![29, -4, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {3} * I3N1 =  Ideal.span {B.equivFun.symm ![-10, 1, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E3RS1 


noncomputable def E5RS0 : RelationCertificate Table 121 ![![5, 0, 0], ![-2, 1, 0]]
  ![-6024, 689, 236] ![![121, 0, 0], ![41, 1, 0]] where
    su := ![![605, 0, 0], ![-242, 121, 0]]
    hsu := by decide
    w := ![![-728904, 83369, 28556], ![-305767, 34969, 11979]]
    hw := by decide
    g := ![![![-64359, -3322328, -243127], ![-49231, 9806120, 0]], ![![10086, 520663, 38102], ![7723, -1536780, 0]]]
    h := ![![![1127294, -2872056, 4615936], ![-1025327, -7693148, 0]], ![![472885, -1204789, 1936323], ![-430110, -3227172, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {121} * I5N0 =  Ideal.span {B.equivFun.symm ![-6024, 689, 236]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E5RS0 


noncomputable def E7RS0 : RelationCertificate Table 363 ![![7, 0, 0], ![2, 1, 0]]
  ![-791, 32, 15] ![![363, 0, 0], ![-80, 1, 0]] where
    su := ![![2541, 0, 0], ![726, 363, 0]]
    hsu := by decide
    w := ![![-287133, 11616, 5445], ![59532, -2541, -1089]]
    hw := by decide
    g := ![![![1134810741, -100052341391, 3752017111], ![-525722129, -453994070592, -6]], ![![567271652, -50014381227, 1875566444], ![-262799122, -226943539808, -3]]]
    h := ![![![987001, 2231729, 3476337], ![600825, -8111448, 0]], ![![-204752, -462966, -721155], ![-124633, 1682694, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {363} * I7N0 =  Ideal.span {B.equivFun.symm ![-791, 32, 15]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E7RS0 


noncomputable def E11RS0 : RelationCertificate Table 3 ![![11, 0, 0], ![3, 1, 0]]
  ![-14, -1, 0] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![33, 0, 0], ![9, 3, 0]]
    hsu := by decide
    w := ![![-42, -3, 0], ![-15, -15, -3]]
    hw := by decide
    g := ![![![7649, -2354, -65], ![1765, 0, 98]], ![![15282, -4702, -131], ![3527, 0, 196]]]
    h := ![![![1, 14, 15], ![10, -55, 0]], ![![-1, 3, 4], ![7, -15, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {3} * I11N0 =  Ideal.span {B.equivFun.symm ![-14, -1, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 1 ![![11, 0, 0], ![-3, 1, 0]]
  ![1, 0, 0] ![![11, 0, 0], ![-3, 1, 0]] where
    su := ![![11, 0, 0], ![-3, 1, 0]]
    hsu := by decide
    w := ![![11, 0, 0], ![-3, 1, 0]]
    hw := by decide
    g := ![![![-57, 206, -210], ![44, 770, 0]], ![![17, -59, 60], ![-10, -220, 0]]]
    h := ![![![-57, 206, -210], ![44, 770, 0]], ![![17, -59, 60], ![-10, -220, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {1} * I11N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E11RS1 


noncomputable def E11RS2 : RelationCertificate Table 1089 ![![11, 0, 0], ![-1, 1, 0]]
  ![4799, -542, -186] ![![1089, 0, 0], ![-80, 1, 0]] where
    su := ![![11979, 0, 0], ![-1089, 1089, 0]]
    hsu := by decide
    w := ![![5226111, -590238, -202554], ![-337590, 38115, 13068]]
    hw := by decide
    g := ![![![64, 239, -9], ![907, 3265, 0]], ![![16, -27, 1], ![212, -365, 0]]]
    h := ![![![499, -112, 186], ![-54, -744, 0]], ![![-32, 7, -12], ![6, 48, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N2 : Ideal.span {1089} * I11N2 =  Ideal.span {B.equivFun.symm ![4799, -542, -186]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E11RS2 


noncomputable def E13RS1 : RelationCertificate Table 99 ![![13, 0, 0], ![-3, 1, 0]]
  ![-112, 13, 3] ![![99, 0, 0], ![19, 1, 0]] where
    su := ![![1287, 0, 0], ![-297, 99, 0]]
    hsu := by decide
    w := ![![-11088, 1287, 297], ![-2871, 297, 99]]
    hw := by decide
    g := ![![![-2974184552342, -60819104326863, -9604906660639], ![-1185137482981, 316961918848955, 142820]], ![![643066897393, 13150075939921, 2076736469259], ![256245929262, -68532303279680, -30880]]]
    h := ![![![57, -210, 213], ![-23, -922, 0]], ![![17, -55, 55], ![4, -238, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {99} * I13N1 =  Ideal.span {B.equivFun.symm ![-112, 13, 3]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E13RS1 


noncomputable def E17RS0 : RelationCertificate Table 1089 ![![17, 0, 0], ![1, 1, 0]]
  ![-2462, 581, -102] ![![1089, 0, 0], ![-80, 1, 0]] where
    su := ![![18513, 0, 0], ![1089, 1089, 0]]
    hsu := by decide
    w := ![![-2681118, 632709, -111078], ![223245, -54450, 9801]]
    hw := by decide
    g := ![![![-608, 49470, -1855], ![183, 673408, 0]], ![![-23, 2962, -111], ![217, 40320, 0]]]
    h := ![![![-109, 70, 102], ![3, -612, 0]], ![![8, -7, -9], ![15, 54, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N0 : Ideal.span {1089} * I17N0 =  Ideal.span {B.equivFun.symm ![-2462, 581, -102]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E17RS0 


noncomputable def E17RS1 : RelationCertificate Table 11 ![![17, 0, 0], ![2, 1, 0]]
  ![60, -5, -2] ![![11, 0, 0], ![-3, 1, 0]] where
    su := ![![187, 0, 0], ![22, 11, 0]]
    hsu := by decide
    w := ![![660, -55, -22], ![319, -33, -11]]
    hw := by decide
    g := ![![![-2575, 8826, -8963], ![1507, 32864, 0]], ![![-1768, 6067, -6162], ![1043, 22594, 0]]]
    h := ![![![-153, -319, -481], ![-32, 2725, 0]], ![![-75, -155, -233], ![-8, 1320, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {11} * I17N1 =  Ideal.span {B.equivFun.symm ![60, -5, -2]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E17RS1 


noncomputable def E17RS2 : RelationCertificate Table 3 ![![17, 0, 0], ![-4, 1, 0]]
  ![-4, 1, 0] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![51, 0, 0], ![-12, 3, 0]]
    hsu := by decide
    w := ![![-12, 3, 0], ![-3, -3, 3]]
    hw := by decide
    g := ![![![795, -242, -7], ![185, 0, 10]], ![![0, -1, 0], ![3, 0, 0]]]
    h := ![![![45, -195, 147], ![-16, -833, 0]], ![![10, -35, 26], ![6, -147, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N2 : Ideal.span {3} * I17N2 =  Ideal.span {B.equivFun.symm ![-4, 1, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E17RS2 


noncomputable def E29RS1 : RelationCertificate Table 363 ![![29, 0, 0], ![-11, 1, 0]]
  ![-160, -5, 9] ![![363, 0, 0], ![-80, 1, 0]] where
    su := ![![10527, 0, 0], ![-3993, 363, 0]]
    hsu := by decide
    w := ![![-58080, -1815, 3267], ![10527, 726, -726]]
    hw := by decide
    g := ![![![167084, -14720967, 552061], ![-77068, -66797298, 79]], ![![-61305, 5403651, -202646], ![28412, 24519402, -29]]]
    h := ![![![-910947, 13355992, -3650124], ![806112, 35284535, 0]], ![![164819, -2416420, 660395], ![-145827, -6383819, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {363} * I29N1 =  Ideal.span {B.equivFun.symm ![-160, -5, 9]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E29RS1 


noncomputable def E29RS2 : RelationCertificate Table 99 ![![29, 0, 0], ![-2, 1, 0]]
  ![-514, 19, 12] ![![99, 0, 0], ![19, 1, 0]] where
    su := ![![2871, 0, 0], ![-198, 99, 0]]
    hsu := by decide
    w := ![![-50886, 1881, 1188], ![-12771, 495, 297]]
    hw := by decide
    g := ![![![-522466538, -10708841751, -1691259084], ![-208441433, 55808277213, 490884]], ![![27498223, 563623224, 89013632], ![10970676, -2937277616, -25836]]]
    h := ![![![705296, -1420725, 2136138], ![-97616, -20649330, 0]], ![![177033, -356609, 536181], ![-24498, -5183082, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N2 : Ideal.span {99} * I29N2 =  Ideal.span {B.equivFun.symm ![-514, 19, 12]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E29RS2 


noncomputable def E31RS0 : RelationCertificate Table 1089 ![![31, 0, 0], ![-14, 1, 0]]
  ![-14825, 1658, 573] ![![1089, 0, 0], ![-80, 1, 0]] where
    su := ![![33759, 0, 0], ![-15246, 1089, 0]]
    hsu := by decide
    w := ![![-16144425, 1805562, 623997], ![1043262, -116523, -40293]]
    hw := by decide
    g := ![![![3021388063306909, -244333648099433362, 9162527172873153], ![-446322032289810, -3325997363779623874, -1012760]], ![![-1208555219685418, 97733458783893677, -3665010852053745], ![178528812083390, 1330398939306177164, 405104]]]
    h := ![![![17184, -371288, 79728], ![-19724, -823665, 0]], ![![-1103, 23992, -5152], ![1291, 53225, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N0 : Ideal.span {1089} * I31N0 =  Ideal.span {B.equivFun.symm ![-14825, 1658, 573]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E31RS0 


noncomputable def E31RS1 : RelationCertificate Table 1089 ![![31, 0, 0], ![-9, 1, 0]]
  ![-52, -47, 12] ![![1089, 0, 0], ![-80, 1, 0]] where
    su := ![![33759, 0, 0], ![-9801, 1089, 0]]
    hsu := by decide
    w := ![![-56628, -51183, 13068], ![1089, 4356, -1089]]
    hw := by decide
    g := ![![![458881397500, -37108826649399, 1391583333598], ![-67786352920, -505144750094310, 67]], ![![-116440090581, 9416278721242, -353111044356], ![17200630779, 128179309100780, -17]]]
    h := ![![![-487, 5218, -1743], ![330, 18015, 0]], ![![10, -87, 29], ![1, -300, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {1089} * I31N1 =  Ideal.span {B.equivFun.symm ![-52, -47, 12]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E31RS1 
