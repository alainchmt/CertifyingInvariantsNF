import IdealArithmetic.Examples.NF3_1_278343_2.PrimesBelow3_1_278343_2F3
import IdealArithmetic.Examples.NF3_1_278343_2.ClassGroupData3_1_278343_2

set_option linter.all false

noncomputable section


noncomputable def E139RS1 : RelationCertificate Table 2 ![![139, 0, 0], ![-32, 1, 0]]
  ![18, 1, 1] ![![2, 0, 0], ![11, 1, 1]] where
    su := ![![278, 0, 0], ![-64, 2, 0]]
    hsu := by decide
    w := ![![36, 2, 2], ![338, 12, 20]]
    hw := by decide
    g := ![![![-2, -4, 0], ![3, 0, 0]], ![![-8, 0, -1], ![1, 0, 0]]]
    h := ![![![-724, 12417, -3205], ![335, 55687, 0]], ![![-6955, 116767, -30138], ![2512, 523649, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N1 : Ideal.span {2} * I139N1 =  Ideal.span {B.equivFun.symm ![18, 1, 1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E139RS1 


noncomputable def E149RS1 : RelationCertificate Table 4 ![![149, 0, 0], ![63, 1, 0]]
  ![193, -51, 24] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![596, 0, 0], ![252, 4, 0]]
    hsu := by decide
    w := ![![772, -204, 96], ![2228, -320, -384]]
    hw := by decide
    g := ![![![-3377061, 1102652, -51747], ![-1412867, 0, 200172]], ![![-1447934, 472608, -22221], ![-605810, 0, 85788]]]
    h := ![![![2159, 91955, 11496], ![1694, -214110, 0]], ![![6361, 265126, 33144], ![4562, -617319, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R149N1 : Ideal.span {4} * I149N1 =  Ideal.span {B.equivFun.symm ![193, -51, 24]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E149RS1 
