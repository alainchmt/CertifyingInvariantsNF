import IdealArithmetic.Examples.NF3_1_387731_1.PrimesBelow3_1_387731_1F3
import IdealArithmetic.Examples.NF3_1_387731_1.ClassGroupData3_1_387731_1

set_option linter.all false

noncomputable section


noncomputable def E157RS1 : RelationCertificate Table 5 ![![157, 0, 0], ![-34, 1, 0]]
  ![-51, 367, -11] ![![5, 0, 0], ![17, -2, 1]] where
    su := ![![785, 0, 0], ![-170, 5, 0]]
    hsu := by decide
    w := ![![-255, 1835, -55], ![700, -5685, -2855]]
    hw := by decide
    g := ![![![-291971, -341424, 59680], ![-844141, 0, 0]], ![![62953, 73641, -12873], ![182071, 0, 0]]]
    h := ![![![-9401, 303, -3], ![-43409, 115, 0]], ![![26028, -778, -3], ![120184, -25, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R157N1 : Ideal.span {5} * I157N1 =  Ideal.span {B.equivFun.symm ![-51, 367, -11]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E157RS1 


noncomputable def E167RS1 : RelationCertificate Table 5 ![![167, 0, 0], ![30, 1, 0]]
  ![-158, 970, -809] ![![5, 0, 0], ![17, -2, 1]] where
    su := ![![835, 0, 0], ![150, 5, 0]]
    hsu := by decide
    w := ![![-790, 4850, -4045], ![8475, -60995, 1790]]
    hw := by decide
    g := ![![![12518599, 14639761, -2559015], ![36195532, 0, 0]], ![![2259184, 2642003, -461820], ![6532122, 0, 0]]]
    h := ![![![986, 22, -7], ![-5494, 90, 0]], ![![-11325, -452, 2], ![63099, 6, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R167N1 : Ideal.span {5} * I167N1 =  Ideal.span {B.equivFun.symm ![-158, 970, -809]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E167RS1 
