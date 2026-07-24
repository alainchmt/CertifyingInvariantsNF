import IdealArithmetic.Examples.NF3_1_933107_3.PrimesBelow3_1_933107_3F0
import IdealArithmetic.Examples.NF3_1_933107_3.ClassGroupData3_1_933107_3

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 1 ![![2, 0, 0], ![0, 1, 0]]
  ![1, 0, 0] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![2, 0, 0], ![0, 1, 0]]
    hsu := by decide
    w := ![![2, 0, 0], ![0, 1, 0]]
    hw := by decide
    g := ![![![24, -25, 1], ![-12, 0, -2]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![24, -25, 1], ![-12, 0, -2]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {1} * I2N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 4 ![![2, 0, 0], ![1, 1, 0]]
  ![1, -1, 0] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![8, 0, 0], ![4, 4, 0]]
    hsu := by decide
    w := ![![4, -4, 0], ![0, 0, -8]]
    hw := by decide
    g := ![![![-56, 0, -2], ![93, 0, 3]], ![![-57, 0, -2], ![93, 0, 3]]]
    h := ![![![0, -1, 0], ![1, 0, 0]], ![![0, 0, -1], ![0, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {4} * I2N1 =  Ideal.span {B.equivFun.symm ![1, -1, 0]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E2RS1 


noncomputable def E5RS0 : RelationCertificate Table 25 ![![5, 0, 0], ![22, -1, 1]]
  ![33, -44, 4] ![![25, 0, 0], ![12, 1, 0]] where
    su := ![![125, 0, 0], ![550, -25, 25]]
    hsu := by decide
    w := ![![825, -1100, 100], ![400, -575, -300]]
    hw := by decide
    g := ![![![113, -59, -36], ![63, 128, 0]], ![![490, -274, -171], ![233, 600, 0]]]
    h := ![![![-11, -8, 0], ![4, 0, 0]], ![![-10, -4, -3], ![3, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {25} * I5N0 =  Ideal.span {B.equivFun.symm ![33, -44, 4]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 1 ![![5, 0, 0], ![2, 1, 0]]
  ![1, 0, 0] ![![5, 0, 0], ![2, 1, 0]] where
    su := ![![5, 0, 0], ![2, 1, 0]]
    hsu := by decide
    w := ![![5, 0, 0], ![2, 1, 0]]
    hw := by decide
    g := ![![![-1, -1, 0], ![5, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![-1, -1, 0], ![5, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {1} * I5N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E5RS1 


noncomputable def E7RS0 : RelationCertificate Table 25 ![![7, 0, 0], ![0, 1, 0]]
  ![6, -8, 3] ![![25, 0, 0], ![12, 1, 0]] where
    su := ![![175, 0, 0], ![0, 25, 0]]
    hsu := by decide
    w := ![![150, -200, 75], ![125, -175, -25]]
    hw := by decide
    g := ![![![25898, 195271, 142603], ![20244, -445638, 0]], ![![3545, 26801, 19573], ![2801, -61166, 0]]]
    h := ![![![-294, 143, -1179], ![23, 1032, 0]], ![![-245, 119, -983], ![20, 860, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {25} * I7N0 =  Ideal.span {B.equivFun.symm ![6, -8, 3]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E7RS0 


noncomputable def E13RS0 : RelationCertificate Table 20 ![![13, 0, 0], ![0, 1, 0]]
  ![17, -21, 16] ![![20, 0, 0], ![2, 1, 0]] where
    su := ![![260, 0, 0], ![0, 20, 0]]
    hsu := by decide
    w := ![![340, -420, 320], ![360, -500, -120]]
    hw := by decide
    g := ![![![1969068, 917890, 7831465], ![242821, -19566908, -31170]], ![![131262, 61192, 522098], ![16203, -1304462, -2078]]]
    h := ![![![-663, 328, -2656], ![33, 4318, 0]], ![![-702, 347, -2814], ![36, 4572, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {20} * I13N0 =  Ideal.span {B.equivFun.symm ![17, -21, 16]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 50 ![![13, 0, 0], ![26, -5, 1]]
  ![13, -9, -6] ![![50, 0, 0], ![12, 1, 0]] where
    su := ![![650, 0, 0], ![1300, -250, 50]]
    hsu := by decide
    w := ![![650, -450, -300], ![0, 100, -150]]
    hw := by decide
    g := ![![![-41091400, -245198691, -178541027], ![-14765899, 1115881580, -99]], ![![-287709789, -1716808454, -1250091277], ![-103386472, 7813071608, -693]]]
    h := ![![![-13, 2, -1], ![7, 0, 0]], ![![-20, 4, -1], ![10, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {50} * I13N1 =  Ideal.span {B.equivFun.symm ![13, -9, -6]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E13RS1 


noncomputable def E17RS1 : RelationCertificate Table 25 ![![17, 0, 0], ![2, 1, 0]]
  ![-1764, 2, -57] ![![25, 0, 0], ![12, 1, 0]] where
    su := ![![425, 0, 0], ![50, 25, 0]]
    hsu := by decide
    w := ![![-44100, 50, -1425], ![-22475, 25, -725]]
    hw := by decide
    g := ![![![-52, -361, -263], ![-28, 822, 0]], ![![-11, -40, -29], ![8, 90, 0]]]
    h := ![![![2684, 1394, 11343], ![415, -24111, 0]], ![![1365, 709, 5771], ![215, -12267, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {25} * I17N1 =  Ideal.span {B.equivFun.symm ![-1764, 2, -57]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E17RS1 


noncomputable def E19RS1 : RelationCertificate Table 5 ![![19, 0, 0], ![9, 1, 0]]
  ![1919, -2, 62] ![![5, 0, 0], ![2, 1, 0]] where
    su := ![![95, 0, 0], ![45, 5, 0]]
    hsu := by decide
    w := ![![9595, -10, 310], ![5260, -5, 170]]
    hw := by decide
    g := ![![![303, 151, 1458], ![155, -912, 0]], ![![133, 69, 652], ![72, -408, 0]]]
    h := ![![![20297, 109086, 109898], ![15364, -261000, 0]], ![![11128, 59801, 60246], ![8420, -143080, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {5} * I19N1 =  Ideal.span {B.equivFun.symm ![1919, -2, 62]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E19RS1 


noncomputable def E29RS1 : RelationCertificate Table 50 ![![29, 0, 0], ![-3, 1, 0]]
  ![-44929, 47, -1452] ![![50, 0, 0], ![12, 1, 0]] where
    su := ![![1450, 0, 0], ![-150, 50, 0]]
    hsu := by decide
    w := ![![-2246450, 2350, -72600], ![-572450, 600, -18500]]
    hw := by decide
    g := ![![![-79165395950590, -472391459522880, -343971207207930], ![-28447524218577, 2149820045209728, -98566]], ![![4656789413980, 27787741367938, 20233606580367], ![1673384286754, -126460041136716, 5798]]]
    h := ![![![-83346035, 169181361, -339359724], ![14455850, 1230178818, 0]], ![![-21238593, 43111522, -86477106], ![3683726, 313479463, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {50} * I29N1 =  Ideal.span {B.equivFun.symm ![-44929, 47, -1452]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E29RS1 


noncomputable def E31RS1 : RelationCertificate Table 4 ![![31, 0, 0], ![-11, 1, 0]]
  ![-2847, 3, -92] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![124, 0, 0], ![-44, 4, 0]]
    hsu := by decide
    w := ![![-11388, 12, -368], ![-7804, 8, -252]]
    hw := by decide
    g := ![![![189535, -278654, 26360], ![25104, 0, -35145]], ![![-58730, 86342, -8169], ![-7776, 0, 10890]]]
    h := ![![![-249007, 1800593, -1203548], ![146464, 4663737, 0]], ![![-170642, 1233913, -824769], ![100363, 3195972, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {4} * I31N1 =  Ideal.span {B.equivFun.symm ![-2847, 3, -92]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E31RS1 
