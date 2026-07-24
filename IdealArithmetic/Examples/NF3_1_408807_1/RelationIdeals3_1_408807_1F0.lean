import IdealArithmetic.Examples.NF3_1_408807_1.PrimesBelow3_1_408807_1F0
import IdealArithmetic.Examples.NF3_1_408807_1.ClassGroupData3_1_408807_1

set_option linter.all false

noncomputable section


noncomputable def E3RS0 : RelationCertificate Table 11 ![![3, 0, 0], ![15, 0, 1]]
  ![24, 1, 1] ![![11, 0, 0], ![-3, 1, 0]] where
    su := ![![33, 0, 0], ![165, 0, 11]]
    hsu := by decide
    w := ![![264, 11, 11], ![33, 0, 0]]
    hw := by decide
    g := ![![![0, 0, 0], ![1, 0, 0]], ![![4, -2, 1], ![8, -4, 0]]]
    h := ![![![-12, 12, -3], ![4, 0, -1]], ![![1, 0, 0], ![0, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {11} * I3N0 =  Ideal.span {B.equivFun.symm ![24, 1, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E3RS0 


noncomputable def E5RS0 : RelationCertificate Table 1 ![![5, 0, 0], ![0, 1, 0]]
  ![1, 0, 0] ![![5, 0, 0], ![0, 1, 0]] where
    su := ![![5, 0, 0], ![0, 1, 0]]
    hsu := by decide
    w := ![![5, 0, 0], ![0, 1, 0]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {1} * I5N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 25 ![![5, 0, 0], ![16, 0, 1]]
  ![-88, -5, -3] ![![25, 0, 0], ![-5, 1, 0]] where
    su := ![![125, 0, 0], ![400, 0, 25]]
    hsu := by decide
    w := ![![-2200, -125, -75], ![125, 0, 0]]
    hw := by decide
    g := ![![![0, 10, -6], ![1, 50, 0]], ![![3, 31, -19], ![14, 158, 0]]]
    h := ![![![-8, -1, 0], ![-3, 0, 0]], ![![-15, 0, -1], ![5, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {25} * I5N1 =  Ideal.span {B.equivFun.symm ![-88, -5, -3]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E5RS1 


noncomputable def E7RS0 : RelationCertificate Table 275 ![![7, 0, 0], ![0, 1, 0]]
  ![-91, 15, 4] ![![275, 0, 0], ![-80, 1, 0]] where
    su := ![![1925, 0, 0], ![0, 275, 0]]
    hsu := by decide
    w := ![![-25025, 4125, 1100], ![7700, -1375, -275]]
    hw := by decide
    g := ![![![1212, 1186571, -44497], ![4168, 4078890, 0]], ![![-5865, -6042727, 226605], ![-20160, -20772126, 0]]]
    h := ![![![-13, 4, -2], ![-13, 6, 0]], ![![4, -2, -1], ![9, 2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {275} * I7N0 =  Ideal.span {B.equivFun.symm ![-91, 15, 4]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E7RS0 


noncomputable def E11RS0 : RelationCertificate Table 121 ![![11, 0, 0], ![13, 1, 1]]
  ![127, -8, 3] ![![121, 0, 0], ![8, 1, 0]] where
    su := ![![1331, 0, 0], ![1573, 121, 121]]
    hsu := by decide
    w := ![![15367, -968, 363], ![1331, 0, 0]]
    hw := by decide
    g := ![![![4200, -7727859, -2898144], ![-63524, 116891808, 0]], ![![4987, -9175502, -3441047], ![-75426, 138788896, 0]]]
    h := ![![![-5, -2, -1], ![14, 0, 0]], ![![-12, -1, -1], ![11, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {121} * I11N0 =  Ideal.span {B.equivFun.symm ![127, -8, 3]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 1 ![![11, 0, 0], ![-3, 1, 0]]
  ![1, 0, 0] ![![11, 0, 0], ![-3, 1, 0]] where
    su := ![![11, 0, 0], ![-3, 1, 0]]
    hsu := by decide
    w := ![![11, 0, 0], ![-3, 1, 0]]
    hw := by decide
    g := ![![![19, -6, 0], ![66, 0, 0]], ![![-3, 4, -3], ![-10, 11, 0]]]
    h := ![![![19, -6, 0], ![66, 0, 0]], ![![-3, 4, -3], ![-10, 11, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {1} * I11N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E11RS1 


noncomputable def E31RS1 : RelationCertificate Table 11 ![![31, 0, 0], ![-6, 1, 0]]
  ![13, 1, 1] ![![11, 0, 0], ![-3, 1, 0]] where
    su := ![![341, 0, 0], ![-66, 11, 0]]
    hsu := by decide
    w := ![![143, 11, 11], ![66, -11, 0]]
    hw := by decide
    g := ![![![1, -5, 5], ![3, -18, 0]], ![![3, -1, 0], ![10, 0, 0]]]
    h := ![![![907, -153, 1], ![4684, -10, 0]], ![![426, -71, 0], ![2200, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {11} * I31N1 =  Ideal.span {B.equivFun.symm ![13, 1, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E31RS1 
