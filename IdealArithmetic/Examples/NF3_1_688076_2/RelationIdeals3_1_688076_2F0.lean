import IdealArithmetic.Examples.NF3_1_688076_2.PrimesBelow3_1_688076_2F0
import IdealArithmetic.Examples.NF3_1_688076_2.ClassGroupData3_1_688076_2

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 77 ![![2, 0, 0], ![-13, 1, 1]]
  ![-20, 0, 1] ![![77, 0, 0], ![-1, 1, 0]] where
    su := ![![154, 0, 0], ![-1001, 77, 77]]
    hsu := by decide
    w := ![![-1540, 0, 77], ![-154, 0, 0]]
    hw := by decide
    g := ![![![0, 0, -2], ![76, 77, 0]], ![![-2045916, 235161, 1], ![121, -39, -905378]]]
    h := ![![![-19670, -121076, -16653], ![59011, 0, -3213]], ![![-1861, -11532, -1587], ![5622, 0, -306]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {77} * I2N0 =  Ideal.span {B.equivFun.symm ![-20, 0, 1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E2RS0 


noncomputable def E7RS0 : RelationCertificate Table 49 ![![7, 0, 0], ![-13, 0, 1]]
  ![2, -7, 2] ![![49, 0, 0], ![6, 1, 0]] where
    su := ![![343, 0, 0], ![-637, 0, 49]]
    hsu := by decide
    w := ![![98, -343, 98], ![-343, 0, 0]]
    hw := by decide
    g := ![![![-12, -2, 0], ![97, 0, 0]], ![![0, -3, -1], ![2, 24, 0]]]
    h := ![![![4, -1, 0], ![2, 0, 0]], ![![12, 0, -1], ![7, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {49} * I7N0 =  Ideal.span {B.equivFun.symm ![2, -7, 2]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 1 ![![7, 0, 0], ![-1, 1, 0]]
  ![1, 0, 0] ![![7, 0, 0], ![-1, 1, 0]] where
    su := ![![7, 0, 0], ![-1, 1, 0]]
    hsu := by decide
    w := ![![7, 0, 0], ![-1, 1, 0]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {1} * I7N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E7RS1 


noncomputable def E11RS0 : RelationCertificate Table 121 ![![11, 0, 0], ![-9, 0, 1]]
  ![-14, -33, -7] ![![121, 0, 0], ![-45, 1, 0]] where
    su := ![![1331, 0, 0], ![-1089, 0, 121]]
    hsu := by decide
    w := ![![-1694, -3993, -847], ![1815, 1331, 242]]
    hw := by decide
    g := ![![![-165, 10776, -479], ![200, 28980, 0]], ![![164, -8819, 392], ![-87, -23715, 0]]]
    h := ![![![2, -3, -1], ![4, 0, 0]], ![![3, 1, 0], ![2, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {121} * I11N0 =  Ideal.span {B.equivFun.symm ![-14, -33, -7]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 1 ![![11, 0, 0], ![-1, 1, 0]]
  ![1, 0, 0] ![![11, 0, 0], ![-1, 1, 0]] where
    su := ![![11, 0, 0], ![-1, 1, 0]]
    hsu := by decide
    w := ![![11, 0, 0], ![-1, 1, 0]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {1} * I11N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E11RS1 


noncomputable def E23RS1 : RelationCertificate Table 77 ![![23, 0, 0], ![9, 1, 0]]
  ![177, 0, -5] ![![77, 0, 0], ![-1, 1, 0]] where
    su := ![![1771, 0, 0], ![693, 77, 0]]
    hsu := by decide
    w := ![![13629, 0, -385], ![693, 77, 0]]
    hw := by decide
    g := ![![![17, -18, 35], ![61, -1350, 0]], ![![27, -27, 54], ![1, -2079, 0]]]
    h := ![![![-179763, -2194458, -489259], ![-165750, 5626476, 0]], ![![-9086, -110894, -24724], ![-8371, 284326, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {77} * I23N1 =  Ideal.span {B.equivFun.symm ![177, 0, -5]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E23RS1 


noncomputable def E31RS0 : RelationCertificate Table 121 ![![31, 0, 0], ![10, 1, 0]]
  ![399, -88, 18] ![![121, 0, 0], ![-45, 1, 0]] where
    su := ![![3751, 0, 0], ![1210, 121, 0]]
    hsu := by decide
    w := ![![48279, -10648, 2178], ![-21175, 4719, -968]]
    hw := by decide
    g := ![![![161, -8144, 362], ![-56, -21900, 0]], ![![82, -2745, 122], ![56, -7380, 0]]]
    h := ![![![-1102331, -13555440, -2716202], ![-792848, 42101140, 0]], ![![483516, 5945854, 1191414], ![347775, -18466921, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N0 : Ideal.span {121} * I31N0 =  Ideal.span {B.equivFun.symm ![399, -88, 18]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E31RS0 
