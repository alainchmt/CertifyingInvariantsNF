import IdealArithmetic.Examples.NF3_1_933107_3.PrimesBelow3_1_933107_3F3
import IdealArithmetic.Examples.NF3_1_933107_3.ClassGroupData3_1_933107_3

set_option linter.all false

noncomputable section


noncomputable def E151RS1 : RelationCertificate Table 4 ![![151, 0, 0], ![42, 1, 0]]
  ![-18195, 19, -588] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![604, 0, 0], ![168, 4, 0]]
    hsu := by decide
    w := ![![-72780, 76, -2352], ![-49876, 52, -1612]]
    hw := by decide
    g := ![![![2424, -3567, 343], ![325, 0, -453]], ![![670, -985, 96], ![89, 0, -125]]]
    h := ![![![-2224163, -51040470, -9960356], ![-956497, 188001646, 0]], ![![-1524219, -34977937, -6825813], ![-655470, 128837170, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N1 : Ideal.span {4} * I151N1 =  Ideal.span {B.equivFun.symm ![-18195, 19, -588]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E151RS1 


noncomputable def E163RS1 : RelationCertificate Table 2 ![![163, 0, 0], ![24, 1, 0]]
  ![-929, 1, -30] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![326, 0, 0], ![48, 2, 0]]
    hsu := by decide
    w := ![![-1858, 2, -60], ![-688, 0, -22]]
    hw := by decide
    g := ![![![5629, -6070, 250], ![-3033, 0, -489]], ![![795, -858, 35], ![-427, 0, -69]]]
    h := ![![![10879, 129240, 44958], ![2410, -916023, 0]], ![![4008, 47854, 16647], ![1030, -339184, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R163N1 : Ideal.span {2} * I163N1 =  Ideal.span {B.equivFun.symm ![-929, 1, -30]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E163RS1 


noncomputable def E191RS1 : RelationCertificate Table 5 ![![191, 0, 0], ![-71, 1, 0]]
  ![6714, -7, 217] ![![5, 0, 0], ![2, 1, 0]] where
    su := ![![955, 0, 0], ![-355, 5, 0]]
    hsu := by decide
    w := ![![33570, -35, 1085], ![18405, -20, 595]]
    hw := by decide
    g := ![![![294, 139, 1399], ![147, -870, 0]], ![![-109, -53, -518], ![-52, 322, 0]]]
    h := ![![![4139995, -182398708, 20267975], ![-2493851, -483897876, 0]], ![![2269790, -100001493, 11112073], ![-1367257, -265300728, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R191N1 : Ideal.span {5} * I191N1 =  Ideal.span {B.equivFun.symm ![6714, -7, 217]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E191RS1 
