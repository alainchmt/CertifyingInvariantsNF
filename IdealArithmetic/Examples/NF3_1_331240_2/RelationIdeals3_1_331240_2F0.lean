import IdealArithmetic.Examples.NF3_1_331240_2.PrimesBelow3_1_331240_2F0
import IdealArithmetic.Examples.NF3_1_331240_2.ClassGroupData3_1_331240_2

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

lemma R2N0 : Ideal.span {1} * I2N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 2 ![![2, 0, 0], ![1, 1, 0]]
  ![146966, 8664, 15983] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![4, 0, 0], ![2, 2, 0]]
    hsu := by decide
    w := ![![293932, 17328, 31966], ![1758130, 103646, 191202]]
    hw := by decide
    g := ![![![37, -43, 44], ![-20, -3, 0]], ![![1531, 87, -154], ![45, 0, 0]]]
    h := ![![![152992, 94183, -20449], ![-159018, 5171, 0]], ![![915118, 563351, -122298], ![-951171, 30927, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {2} * I2N1 =  Ideal.span {B.equivFun.symm ![146966, 8664, 15983]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS1 


noncomputable def E3RS0 : RelationCertificate Table 9 ![![3, 0, 0], ![-2, -2, 1]]
  ![-239, -14, -26] ![![9, 0, 0], ![4, 1, 0]] where
    su := ![![27, 0, 0], ![-18, -18, 9]]
    hsu := by decide
    w := ![![-2151, -126, -234], ![-3816, -225, -414]]
    hw := by decide
    g := ![![![-5, 2, -34], ![8, 28, 0]], ![![-14, -1, 27], ![-3, -22, 0]]]
    h := ![![![-61, 14, -18], ![28, 0, 0]], ![![-108, 25, -32], ![50, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {9} * I3N0 =  Ideal.span {B.equivFun.symm ![-239, -14, -26]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 1 ![![3, 0, 0], ![1, 1, 0]]
  ![1, 0, 0] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![3, 0, 0], ![1, 1, 0]]
    hsu := by decide
    w := ![![3, 0, 0], ![1, 1, 0]]
    hw := by decide
    g := ![![![2, 5, -11], ![-3, 3, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![2, 5, -11], ![-3, 3, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {1} * I3N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E3RS1 


noncomputable def E5RS0 : RelationCertificate Table 6 ![![5, 0, 0], ![0, 1, 0]]
  ![-25, -1, 2] ![![6, 0, 0], ![-2, -1, 1]] where
    su := ![![30, 0, 0], ![0, 6, 0]]
    hsu := by decide
    w := ![![-150, -6, 12], ![-60, 42, -24]]
    hw := by decide
    g := ![![![-579, 14, -6], ![193, 34, 0]], ![![-42, 0, -8], ![17, 0, 0]]]
    h := ![![![-5, -56, 128], ![-11, -58, 0]], ![![-2, 112, -256], ![27, 116, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {6} * I5N0 =  Ideal.span {B.equivFun.symm ![-25, -1, 2]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 6 ![![5, 0, 0], ![-1, 1, 0]]
  ![-1747, -103, -190] ![![6, 0, 0], ![-2, -1, 1]] where
    su := ![![30, 0, 0], ![-6, 6, 0]]
    hsu := by decide
    w := ![![-10482, -618, -1140], ![-7836, -462, -852]]
    hw := by decide
    g := ![![![-39, 1, -1], ![13, 4, 0]], ![![-65, 8, -3], ![21, 1, 0]]]
    h := ![![![17074, -17384, -148], ![87117, 50, 0]], ![![12764, -12995, -112], ![65126, 38, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {6} * I5N1 =  Ideal.span {B.equivFun.symm ![-1747, -103, -190]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E5RS1 


noncomputable def E7RS0 : RelationCertificate Table 2 ![![7, 0, 0], ![2, 1, 0]]
  ![2731, 161, 297] ![![2, 0, 0], ![-2, -1, 1]] where
    su := ![![14, 0, 0], ![4, 2, 0]]
    hsu := by decide
    w := ![![5462, 322, 594], ![12248, 722, 1332]]
    hw := by decide
    g := ![![![47, -27, 18], ![-25, 0, 0]], ![![58, -8, 8], ![-49, 0, 0]]]
    h := ![![![4811, 2458, -781], ![-15473, 524, 0]], ![![10792, 5509, -1734], ![-34710, 1164, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {2} * I7N0 =  Ideal.span {B.equivFun.symm ![2731, 161, 297]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E7RS0 


noncomputable def E11RS0 : RelationCertificate Table 3 ![![11, 0, 0], ![0, 1, 0]]
  ![-11, 4, -2] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![33, 0, 0], ![0, 3, 0]]
    hsu := by decide
    w := ![![-33, 12, -6], ![-231, -27, 30]]
    hw := by decide
    g := ![![![-61, 0, 0], ![-20, -2, 0]], ![![-67, 2, -8], ![-19, 0, 0]]]
    h := ![![![39, 0, 2], ![4, 0, -4]], ![![-207, -1, -10], ![2, 0, 20]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {3} * I11N0 =  Ideal.span {B.equivFun.symm ![-11, 4, -2]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 3 ![![11, 0, 0], ![-2, -1, 1]]
  ![3941, 218, -355] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![33, 0, 0], ![-6, -3, 3]]
    hsu := by decide
    w := ![![11823, 654, -1065], ![-35109, 3069, -87]]
    hw := by decide
    g := ![![![988449, -40828, 118988], ![315876, -11, 0]], ![![402996, -16639, 48492], ![128786, 1, 0]]]
    h := ![![![906879, 10278, -27329], ![-168296, -93712, 0]], ![![-2757655, -31100, 83002], ![511769, 284964, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {3} * I11N1 =  Ideal.span {B.equivFun.symm ![3941, 218, -355]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E11RS1 


noncomputable def E11RS2 : RelationCertificate Table 3 ![![11, 0, 0], ![-3, -1, 1]]
  ![17, 14, -10] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![33, 0, 0], ![-9, -3, 3]]
    hsu := by decide
    w := ![![51, 42, -30], ![-1083, -39, 84]]
    hw := by decide
    g := ![![![736, -137, 410], ![201, -88, 0]], ![![227, 9, -31], ![82, 16, 0]]]
    h := ![![![14071, -74, -338], ![-3852, -1512, 0]], ![![-372809, 2015, 8914], ![102314, 40068, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N2 : Ideal.span {3} * I11N2 =  Ideal.span {B.equivFun.symm ![17, 14, -10]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E11RS2 


noncomputable def E17RS1 : RelationCertificate Table 2 ![![17, 0, 0], ![3, 1, 0]]
  ![-1323, 547, -283] ![![2, 0, 0], ![-2, -1, 1]] where
    su := ![![34, 0, 0], ![6, 2, 0]]
    hsu := by decide
    w := ![![-2646, 1094, -566], ![62816, 134, -3492]]
    hw := by decide
    g := ![![![3404687, -759503, 1695604], ![-2177129, 0, 0]], ![![2996691, -668490, 1492415], ![-1916238, 0, 0]]]
    h := ![![![-957, -265, 6], ![4982, -35, 0]], ![![23426, 7299, -665], ![-122278, 869, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {2} * I17N1 =  Ideal.span {B.equivFun.symm ![-1323, 547, -283]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E17RS1 


noncomputable def E29RS1 : RelationCertificate Table 18 ![![29, 0, 0], ![7, 1, 0]]
  ![225419, 13289, 24515] ![![18, 0, 0], ![-2, -1, 1]] where
    su := ![![522, 0, 0], ![126, 18, 0]]
    hsu := by decide
    w := ![![4057542, 239202, 441270], ![1010952, 59598, 109944]]
    hw := by decide
    g := ![![![865, -9, -14], ![-89, -160, 0]], ![![349, 0, -11], ![-36, -46, 0]]]
    h := ![![![25097119, 3601301, 92423], ![-103941576, -241432, 0]], ![![6253040, 897277, 23025], ![-25897428, -60147, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {18} * I29N1 =  Ideal.span {B.equivFun.symm ![225419, 13289, 24515]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E29RS1 


noncomputable def E31RS1 : RelationCertificate Table 18 ![![31, 0, 0], ![-1, 1, 0]]
  ![-31334, -158, 1801] ![![18, 0, 0], ![4, 1, 0]] where
    su := ![![558, 0, 0], ![-18, 18, 0]]
    hsu := by decide
    w := ![![-564012, -2844, 32418], ![72774, -31176, 16272]]
    hw := by decide
    g := ![![![7179912368, -610169389429, 6731605012685], ![-32302763319, -11015353386530, 0]], ![![-288942092, 24603632717, -271435622185], ![1302659137, 444167477449, 0]]]
    h := ![![![-210940, 209964, -15], ![-6507806, 206, 0]], ![![27608, -27529, 21], ![851805, 23, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {18} * I31N1 =  Ideal.span {B.equivFun.symm ![-31334, -158, 1801]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E31RS1 
