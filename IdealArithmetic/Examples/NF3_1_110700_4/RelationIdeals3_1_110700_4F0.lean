import IdealArithmetic.Examples.NF3_1_110700_4.PrimesBelow3_1_110700_4F0
import IdealArithmetic.Examples.NF3_1_110700_4.ClassGroupData3_1_110700_4

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 1183 ![![2, 0, 0], ![0, 1, 0]]
  ![1942, 15, 64] ![![1183, 0, 0], ![314, 1, 0]] where
    su := ![![2366, 0, 0], ![0, 1183, 0]]
    hsu := by decide
    w := ![![2297386, 17745, 75712], ![610428, 4732, 20111]]
    hw := by decide
    g := ![![![-219886, 1048383756, 3338804], ![828424, -3949805133, 0]], ![![72947, -349461045, -1112934], ![-274829, 1316600927, 0]]]
    h := ![![![971, 12, 25], ![-9, 14, 0]], ![![258, 2, 6], ![0, 5, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {1183} * I2N0 =  Ideal.span {B.equivFun.symm ![1942, 15, 64]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E2RS0 


noncomputable def E3RS0 : RelationCertificate Table 49 ![![3, 0, 0], ![-1, 1, 0]]
  ![3, -13, 1] ![![49, 0, 0], ![13, 1, 0]] where
    su := ![![147, 0, 0], ![-49, 49, 0]]
    hsu := by decide
    w := ![![147, -637, 49], ![49, -196, 0]]
    hw := by decide
    g := ![![![-1394, 273128, 21018], ![5245, -1029886, 0]], ![![-22, 1909, 147], ![85, -7202, 0]]]
    h := ![![![4, -7, 0], ![9, 1, 0]], ![![0, 1, -2], ![-1, 6, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {49} * I3N0 =  Ideal.span {B.equivFun.symm ![3, -13, 1]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E3RS0 


noncomputable def E5RS0 : RelationCertificate Table 637 ![![5, 0, 0], ![0, 1, 0]]
  ![605, 8, 22] ![![637, 0, 0], ![-232, 1, 0]] where
    su := ![![3185, 0, 0], ![0, 637, 0]]
    hsu := by decide
    w := ![![385385, 5096, 14014], ![-140140, -1911, -5096]]
    hw := by decide
    g := ![![![169, 464, -2], ![464, 1276, 0]], ![![-4, 0, 0], ![-11, 0, 0]]]
    h := ![![![121, 2, 4], ![-2, 2, 0]], ![![-44, -2, -2], ![7, 2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {637} * I5N0 =  Ideal.span {B.equivFun.symm ![605, 8, 22]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E5RS0 


noncomputable def E7RS0 : RelationCertificate Table 49 ![![7, 0, 0], ![17, 1, 1]]
  ![9, 10, 3] ![![49, 0, 0], ![13, 1, 0]] where
    su := ![![343, 0, 0], ![833, 49, 49]]
    hsu := by decide
    w := ![![441, 490, 147], ![147, 49, 49]]
    hw := by decide
    g := ![![![-5170, 1020531, 78533], ![19489, -3848116, 0]], ![![-12537, 2477797, 190674], ![47260, -9343024, 0]]]
    h := ![![![-6, 1, 0], ![3, 0, 0]], ![![-2, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {49} * I7N0 =  Ideal.span {B.equivFun.symm ![9, 10, 3]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 1 ![![7, 0, 0], ![-1, 1, 0]]
  ![1, 0, 0] ![![7, 0, 0], ![-1, 1, 0]] where
    su := ![![7, 0, 0], ![-1, 1, 0]]
    hsu := by decide
    w := ![![7, 0, 0], ![-1, 1, 0]]
    hw := by decide
    g := ![![![4, -3, 0], ![21, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![4, -3, 0], ![21, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {1} * I7N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E7RS1 


noncomputable def E13RS1 : RelationCertificate Table 1 ![![13, 0, 0], ![2, 1, 0]]
  ![1, 0, 0] ![![13, 0, 0], ![2, 1, 0]] where
    su := ![![13, 0, 0], ![2, 1, 0]]
    hsu := by decide
    w := ![![13, 0, 0], ![2, 1, 0]]
    hw := by decide
    g := ![![![11, 5, 0], ![-65, 0, 0]], ![![-2, -1, 0], ![14, 0, 0]]]
    h := ![![![11, 5, 0], ![-65, 0, 0]], ![![-2, -1, 0], ![14, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {1} * I13N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E13RS1 


noncomputable def E19RS1 : RelationCertificate Table 8281 ![![19, 0, 0], ![5, 1, 0]]
  ![-1249, 153, -57] ![![8281, 0, 0], ![-869, 1, 0]] where
    su := ![![157339, 0, 0], ![41405, 8281, 0]]
    hsu := by decide
    w := ![![-10342969, 1266993, -472017], ![1084811, -132496, 49686]]
    hw := by decide
    g := ![![![319, -842062, 969], ![3040, -8024295, 0]], ![![595, -241583, 278], ![5670, -2302121, 0]]]
    h := ![![![-1241, -247, -7], ![4466, 76, 0]], ![![129, 22, 0], ![-464, 6, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {8281} * I19N1 =  Ideal.span {B.equivFun.symm ![-1249, 153, -57]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E19RS1 


noncomputable def E23RS1 : RelationCertificate Table 169 ![![23, 0, 0], ![-9, 1, 0]]
  ![17, -1, 7] ![![169, 0, 0], ![-24, 1, 0]] where
    su := ![![3887, 0, 0], ![-1521, 169, 0]]
    hsu := by decide
    w := ![![2873, -169, 1183], ![-338, -169, -169]]
    hw := by decide
    g := ![![![-15739, -19122831, 796812], ![-110838, -134661220, 0]], ![![-5435, -6623030, 275969], ![-38268, -46638764, 0]]]
    h := ![![![29689, -3674, 42], ![75870, -959, 0]], ![![-3424, 434, -6], ![-8750, 137, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {169} * I23N1 =  Ideal.span {B.equivFun.symm ![17, -1, 7]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E23RS1 


noncomputable def E29RS0 : RelationCertificate Table 91 ![![29, 0, 0], ![6, 1, 0]]
  ![-1, 23, -5] ![![91, 0, 0], ![41, 1, 0]] where
    su := ![![2639, 0, 0], ![546, 91, 0]]
    hsu := by decide
    w := ![![-91, 2093, -455], ![-91, 1092, -182]]
    hw := by decide
    g := ![![![-66, 9504, 232], ![157, -21098, 0]], ![![-26, 2294, 56], ![60, -5093, 0]]]
    h := ![![![-11, -6, -1], ![53, 24, 0]], ![![-11, -7, -1], ![53, 27, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N0 : Ideal.span {91} * I29N0 =  Ideal.span {B.equivFun.symm ![-1, 23, -5]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E29RS0 


noncomputable def E29RS1 : RelationCertificate Table 13 ![![29, 0, 0], ![-4, 1, 0]]
  ![21, -2, 1] ![![13, 0, 0], ![2, 1, 0]] where
    su := ![![377, 0, 0], ![-52, 13, 0]]
    hsu := by decide
    w := ![![273, -26, 13], ![52, -13, 0]]
    hw := by decide
    g := ![![![-25, 2209, 1111], ![171, -14442, 0]], ![![2, -331, -166], ![-14, 2158, 0]]]
    h := ![![![1145, -290, 1], ![8296, -28, 0]], ![![220, -55, 0], ![1594, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {13} * I29N1 =  Ideal.span {B.equivFun.symm ![21, -2, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E29RS1 


noncomputable def E29RS2 : RelationCertificate Table 637 ![![29, 0, 0], ![-2, 1, 0]]
  ![-3041, -36, -99] ![![637, 0, 0], ![-232, 1, 0]] where
    su := ![![18473, 0, 0], ![-1274, 637, 0]]
    hsu := by decide
    w := ![![-1937117, -22932, -63063], ![704522, 8281, 22932]]
    hw := by decide
    g := ![![![-38410313, -76091247099, 327980227], ![-105462799, -208923404590, 0]], ![![1378076, 2729942236, -11767018], ![3783769, 7495590466, 0]]]
    h := ![![![-4127439, 2072819, -4580], ![-59846345, 132721, 0]], ![![1501138, -753877, 1665], ![21765948, -48249, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N2 : Ideal.span {637} * I29N2 =  Ideal.span {B.equivFun.symm ![-3041, -36, -99]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E29RS2 
