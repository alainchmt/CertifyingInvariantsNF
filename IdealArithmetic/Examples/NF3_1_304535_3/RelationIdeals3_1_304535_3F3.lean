import IdealArithmetic.Examples.NF3_1_304535_3.PrimesBelow3_1_304535_3F3
import IdealArithmetic.Examples.NF3_1_304535_3.ClassGroupData3_1_304535_3

set_option linter.all false

noncomputable section


noncomputable def E149RS1 : RelationCertificate Table 3 ![![149, 0, 0], ![-2, 1, 0]]
  ![-2, 1, 0] ![![3, 0, 0], ![6, 1, 1]] where
    su := ![![447, 0, 0], ![-6, 3, 0]]
    hsu := by decide
    w := ![![-6, 3, 0], ![93, -3, 3]]
    hw := by decide
    g := ![![![-3, -2, -1], ![8, 0, 0]], ![![-5, -1, -1], ![3, 0, 0]]]
    h := ![![![-10, 7, -5], ![-744, 149, 0]], ![![161, -80, -1], ![11979, 30, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R149N1 : Ideal.span {3} * I149N1 =  Ideal.span {B.equivFun.symm ![-2, 1, 0]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E149RS1 


noncomputable def E151RS0 : RelationCertificate Table 9 ![![151, 0, 0], ![48, 1, 0]]
  ![-239, -20, -15] ![![9, 0, 0], ![3, 1, 1]] where
    su := ![![1359, 0, 0], ![432, 9, 0]]
    hsu := by decide
    w := ![![-2151, -180, -135], ![-4392, -369, -279]]
    hw := by decide
    g := ![![![-48, 7, 2], ![-8, 0, 0]], ![![-14, 2, 1], ![-4, 0, 0]]]
    h := ![![![-51545, -1313, -25], ![162147, 752, 0]], ![![-105176, -2631, -46], ![330856, 1383, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N0 : Ideal.span {9} * I151N0 =  Ideal.span {B.equivFun.symm ![-239, -20, -15]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E151RS0 


noncomputable def E151RS1 : RelationCertificate Table 3 ![![151, 0, 0], ![-31, 1, 0]]
  ![-11, 0, 1] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![453, 0, 0], ![-93, 3, 0]]
    hsu := by decide
    w := ![![-33, 0, 3], ![105, -18, 0]]
    hw := by decide
    g := ![![![-36, -3, -2], ![2, 0, 0]], ![![6, 0, 2], ![1, -1, 0]]]
    h := ![![![-98, 28, -4], ![-477, 121, 0]], ![![402, -13, 0], ![1957, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N1 : Ideal.span {3} * I151N1 =  Ideal.span {B.equivFun.symm ![-11, 0, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E151RS1 


noncomputable def E151RS2 : RelationCertificate Table 3 ![![151, 0, 0], ![-17, 1, 0]]
  ![-774, -65, -49] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![453, 0, 0], ![-51, 3, 0]]
    hsu := by decide
    w := ![![-2322, -195, -147], ![-4371, -366, -276]]
    hw := by decide
    g := ![![![89, 91, -524], ![4, 314, 0]], ![![-10, -10, 58], ![1, -35, 0]]]
    h := ![![![-36758, 2191, -9], ![-326452, 262, 0]], ![![-69201, 4125, -17], ![-614582, 495, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N2 : Ideal.span {3} * I151N2 =  Ideal.span {B.equivFun.symm ![-774, -65, -49]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E151RS2 
