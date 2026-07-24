import IdealArithmetic.Examples.NF3_1_343980_3.PrimesBelow3_1_343980_3F3
import IdealArithmetic.Examples.NF3_1_343980_3.ClassGroupData3_1_343980_3

set_option linter.all false

noncomputable section


noncomputable def E151RS1 : RelationCertificate Table 5 ![![151, 0, 0], ![-74, 1, 0]]
  ![-3, -2, 0] ![![5, 0, 0], ![-26, -4, 1]] where
    su := ![![755, 0, 0], ![-370, 5, 0]]
    hsu := by decide
    w := ![![-15, -10, 0], ![-230, -20, 5]]
    hw := by decide
    g := ![![![11, -2, 0], ![-4, 0, 0]], ![![20, 5, -1], ![7, 0, 0]]]
    h := ![![![-1185, 90, -1], ![-2418, 151, 0]], ![![-20094, 346, -1], ![-41002, 152, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N1 : Ideal.span {5} * I151N1 =  Ideal.span {B.equivFun.symm ![-3, -2, 0]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E151RS1 


noncomputable def E157RS1 : RelationCertificate Table 605 ![![157, 0, 0], ![41, 1, 0]]
  ![6523, 2593, 329] ![![605, 0, 0], ![-212, 1, 0]] where
    su := ![![94985, 0, 0], ![24805, 605, 0]]
    hsu := by decide
    w := ![![3946415, 1568765, 199045], ![-1332210, -529375, -67155]]
    hw := by decide
    g := ![![![2873, 5309544, -25045], ![8199, 15152277, 0]], ![![785, 1396656, -6588], ![2240, 3985751, 0]]]
    h := ![![![36384, 940, 3], ![-139165, -142, 0]], ![![-12372, -360, -2], ![47322, 203, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R157N1 : Ideal.span {605} * I157N1 =  Ideal.span {B.equivFun.symm ![6523, 2593, 329]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E157RS1 
