import IdealArithmetic.Examples.NF3_1_120204_1.PrimesBelow3_1_120204_1F0
import IdealArithmetic.Examples.NF3_1_120204_1.ClassGroupData3_1_120204_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 11 ![![2, 0, 0], ![0, 1, 0]]
  ![110, 13, 8] ![![11, 0, 0], ![2, 1, 0]] where
    su := ![![22, 0, 0], ![0, 11, 0]]
    hsu := by decide
    w := ![![1210, 143, 88], ![748, 88, 55]]
    hw := by decide
    g := ![![![0, 3, 5], ![1, -18, 0]], ![![1, 1, 3], ![11, -12, 0]]]
    h := ![![![55, 10, 1], ![-7, 2, 0]], ![![34, 6, -2], ![-4, 3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {11} * I2N0 =  Ideal.span {B.equivFun.symm ![110, 13, 8]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E2RS0 


noncomputable def E3RS0 : RelationCertificate Table 77 ![![3, 0, 0], ![3, 0, 1]]
  ![33, 3, 1] ![![77, 0, 0], ![-9, 1, 0]] where
    su := ![![231, 0, 0], ![231, 0, 77]]
    hsu := by decide
    w := ![![2541, 231, 77], ![-231, 0, 0]]
    hw := by decide
    g := ![![![0, 0, 0], ![-1, 0, 0]], ![![1, -693, 231], ![10, -5928, 0]]]
    h := ![![![112, 5061, -656], ![-101, 0, -690]], ![![-1, 0, 0], ![0, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {77} * I3N0 =  Ideal.span {B.equivFun.symm ![33, 3, 1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E3RS0 


noncomputable def E7RS0 : RelationCertificate Table 7 ![![7, 0, 0], ![1, 1, 0]]
  ![67, 8, 5] ![![7, 0, 0], ![-2, 1, 0]] where
    su := ![![49, 0, 0], ![7, 7, 0]]
    hsu := by decide
    w := ![![469, 56, 35], ![196, 21, 14]]
    hw := by decide
    g := ![![![-117, -3051, 4663], ![-401, -10880, 0]], ![![-37, -1050, 1603], ![-133, -3740, 0]]]
    h := ![![![18, 9, -1], ![-59, 4, 0]], ![![6, 2, -1], ![-14, 3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {7} * I7N0 =  Ideal.span {B.equivFun.symm ![67, 8, 5]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 1 ![![7, 0, 0], ![-2, 1, 0]]
  ![1, 0, 0] ![![7, 0, 0], ![-2, 1, 0]] where
    su := ![![7, 0, 0], ![-2, 1, 0]]
    hsu := by decide
    w := ![![7, 0, 0], ![-2, 1, 0]]
    hw := by decide
    g := ![![![13, -6, 0], ![42, 0, 0]], ![![-2, 3, -3], ![-6, 7, 0]]]
    h := ![![![13, -6, 0], ![42, 0, 0]], ![![-2, 3, -3], ![-6, 7, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {1} * I7N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E7RS1 


noncomputable def E11RS0 : RelationCertificate Table 7 ![![11, 0, 0], ![0, 1, 0]]
  ![-11, -1, 2] ![![7, 0, 0], ![-2, 1, 0]] where
    su := ![![77, 0, 0], ![0, 7, 0]]
    hsu := by decide
    w := ![![-77, -7, 14], ![154, -21, -7]]
    hw := by decide
    g := ![![![-13, -2, -1], ![3, 0, 0]], ![![-4, -6, 6], ![7, -15, 0]]]
    h := ![![![-1, 0, -2], ![-1, 8, 0]], ![![2, 0, 1], ![-3, -4, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {7} * I11N0 =  Ideal.span {B.equivFun.symm ![-11, -1, 2]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 1 ![![11, 0, 0], ![2, 1, 0]]
  ![1, 0, 0] ![![11, 0, 0], ![2, 1, 0]] where
    su := ![![11, 0, 0], ![2, 1, 0]]
    hsu := by decide
    w := ![![11, 0, 0], ![2, 1, 0]]
    hw := by decide
    g := ![![![9, 4, 0], ![-44, 0, 0]], ![![-2, -1, 0], ![12, 0, 0]]]
    h := ![![![9, 4, 0], ![-44, 0, 0]], ![![-2, -1, 0], ![12, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {1} * I11N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E11RS1 


noncomputable def E11RS2 : RelationCertificate Table 5929 ![![11, 0, 0], ![-2, 1, 0]]
  ![649, -235, 50] ![![5929, 0, 0], ![607, 1, 0]] where
    su := ![![65219, 0, 0], ![-11858, 5929, 0]]
    hsu := by decide
    w := ![![3847921, -1393315, 296450], ![397243, -142296, 29645]]
    hw := by decide
    g := ![![![-312, 8420102, 41615], ![3047, -82245120, 0]], ![![-305, -413772, -2045], ![2979, 4041600, 0]]]
    h := ![![![9005235, -4617463, 172285], ![49528468, -631695, 0]], ![![929565, -476638, 17785], ![5112574, -65210, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N2 : Ideal.span {5929} * I11N2 =  Ideal.span {B.equivFun.symm ![649, -235, 50]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E11RS2 


noncomputable def E13RS1 : RelationCertificate Table 77 ![![13, 0, 0], ![-3, 1, 0]]
  ![11, -6, -2] ![![77, 0, 0], ![-9, 1, 0]] where
    su := ![![1001, 0, 0], ![-231, 77, 0]]
    hsu := by decide
    w := ![![847, -462, -154], ![-231, 77, 0]]
    hw := by decide
    g := ![![![-19, -17950, 5984], ![-162, -153590, 0]], ![![9, 4832, -1611], ![78, 41349, 0]]]
    h := ![![![2918, -1013, 40], ![12641, -174, 0]], ![![-786, 274, -12], ![-3405, 52, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {77} * I13N1 =  Ideal.span {B.equivFun.symm ![11, -6, -2]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E13RS1 


noncomputable def E23RS1 : RelationCertificate Table 77 ![![23, 0, 0], ![7, 1, 0]]
  ![55, -9, -3] ![![77, 0, 0], ![-9, 1, 0]] where
    su := ![![1771, 0, 0], ![539, 77, 0]]
    hsu := by decide
    w := ![![4235, -693, -231], ![-693, 154, 0]]
    hw := by decide
    g := ![![![4370, 2916009, -972165], ![37395, 24952233, 0]], ![![3103, 2071482, -690609], ![26552, 17725630, 0]]]
    h := ![![![115, 16, 0], ![-370, -1, 0]], ![![-29, -11, -3], ![94, 23, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {77} * I23N1 =  Ideal.span {B.equivFun.symm ![55, -9, -3]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E23RS1 


noncomputable def E29RS0 : RelationCertificate Table 7 ![![29, 0, 0], ![6, 1, 0]]
  ![-23, 3, 1] ![![7, 0, 0], ![-2, 1, 0]] where
    su := ![![203, 0, 0], ![42, 7, 0]]
    hsu := by decide
    w := ![![-161, 21, 7], ![112, -35, 7]]
    hw := by decide
    g := ![![![-15, -6, 4], ![5, -12, 0]], ![![-4, -4, 3], ![7, -8, 0]]]
    h := ![![![-25, -6, -1], ![117, 10, 0]], ![![8, -1, -1], ![-36, 10, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N0 : Ideal.span {7} * I29N0 =  Ideal.span {B.equivFun.symm ![-23, 3, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E29RS0 


noncomputable def E29RS1 : RelationCertificate Table 5929 ![![29, 0, 0], ![7, 1, 0]]
  ![-1661, -102, 274] ![![5929, 0, 0], ![607, 1, 0]] where
    su := ![![171941, 0, 0], ![41503, 5929, 0]]
    hsu := by decide
    w := ![![-9848069, -604758, 1624546], ![-990143, -65219, 166012]]
    hw := by decide
    g := ![![![-1022, 25772819, 127378], ![9979, -251741440, 0]], ![![-506, 6882572, 34016], ![4941, -67226976, 0]]]
    h := ![![![-41922652, -6525709, -230032], ![173679321, 2223734, 0]], ![![-4215476, -656178, -23128], ![17464091, 223580, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {5929} * I29N1 =  Ideal.span {B.equivFun.symm ![-1661, -102, 274]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E29RS1 


noncomputable def E29RS2 : RelationCertificate Table 11 ![![29, 0, 0], ![-13, 1, 0]]
  ![11, 3, 1] ![![11, 0, 0], ![2, 1, 0]] where
    su := ![![319, 0, 0], ![-143, 11, 0]]
    hsu := by decide
    w := ![![121, 33, 11], ![88, 11, 11]]
    hw := by decide
    g := ![![![-3, 119, 181], ![16, -663, 0]], ![![1, -51, -77], ![-3, 282, 0]]]
    h := ![![![86, -2, -1], ![191, 10, 0]], ![![72, -1, -1], ![160, 10, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N2 : Ideal.span {11} * I29N2 =  Ideal.span {B.equivFun.symm ![11, 3, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E29RS2 


noncomputable def E31RS0 : RelationCertificate Table 49 ![![31, 0, 0], ![1, 1, 0]]
  ![397, 45, 29] ![![49, 0, 0], ![19, 1, 0]] where
    su := ![![1519, 0, 0], ![49, 49, 0]]
    hsu := by decide
    w := ![![19453, 2205, 1421], ![9457, 1078, 686]]
    hw := by decide
    g := ![![![-12, 216, 34], ![31, -558, 0]], ![![-5, 6, 1], ![12, -16, 0]]]
    h := ![![![24, 12, -1], ![-347, 20, 0]], ![![6, 6, 17], ![7, -171, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N0 : Ideal.span {49} * I31N0 =  Ideal.span {B.equivFun.symm ![397, 45, 29]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E31RS0 


noncomputable def E31RS1 : RelationCertificate Table 77 ![![31, 0, 0], ![3, 1, 0]]
  ![-55, -12, -4] ![![77, 0, 0], ![-9, 1, 0]] where
    su := ![![2387, 0, 0], ![231, 77, 0]]
    hsu := by decide
    w := ![![-4235, -924, -308], ![231, 77, 0]]
    hw := by decide
    g := ![![![24254, 16192667, -5398454], ![207507, 138560318, 0]], ![![2484, 1653627, -551301], ![21253, 14150059, 0]]]
    h := ![![![-11032, -3717, -40], ![113979, 412, 0]], ![![600, 200, 0], ![-6199, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {77} * I31N1 =  Ideal.span {B.equivFun.symm ![-55, -12, -4]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E31RS1 


noncomputable def E31RS2 : RelationCertificate Table 121 ![![31, 0, 0], ![-4, 1, 0]]
  ![-55, -6, 9] ![![121, 0, 0], ![2, 1, 0]] where
    su := ![![3751, 0, 0], ![-484, 121, 0]]
    hsu := by decide
    w := ![![-6655, -726, 1089], ![484, -121, 0]]
    hw := by decide
    g := ![![![-3, 801, 1203], ![115, -48524, 0]], ![![-2, -85, -126], ![120, 5082, 0]]]
    h := ![![![-65, 16, 0], ![-490, 3, 0]], ![![12, -3, 0], ![92, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N2 : Ideal.span {121} * I31N2 =  Ideal.span {B.equivFun.symm ![-55, -6, 9]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E31RS2 
