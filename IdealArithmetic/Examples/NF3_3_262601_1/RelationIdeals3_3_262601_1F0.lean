import IdealArithmetic.Examples.NF3_3_262601_1.PrimesBelow3_3_262601_1F0
import IdealArithmetic.Examples.NF3_3_262601_1.ClassGroupData3_3_262601_1

set_option linter.all false

noncomputable section


noncomputable def E2RS1 : RelationCertificate Table 2 ![![2, 0, 0], ![-29, -1, 1]]
  ![-861, -25, 22] ![![2, 0, 0], ![-30, -2, 1]] where
    su := ![![4, 0, 0], ![-58, -2, 2]]
    hsu := by decide
    w := ![![-1722, -50, 44], ![14182, 410, -362]]
    hw := by decide
    g := ![![![22, 11, 2], ![0, 0, 0]], ![![24, 57, 15], ![-7, 0, 0]]]
    h := ![![![-418, -12709, -1862], ![11693, 2649, 0]], ![![3579, 104670, 15330], ![-96289, -21816, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {2} * I2N1 =  Ideal.span {B.equivFun.symm ![-861, -25, 22]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS1 


noncomputable def E2RS2 : RelationCertificate Table 2 ![![2, 0, 0], ![-29, -2, 1]]
  ![1449, 42, -37] ![![2, 0, 0], ![-30, -2, 1]] where
    su := ![![4, 0, 0], ![-58, -4, 2]]
    hsu := by decide
    w := ![![2898, 84, -74], ![-23886, -692, 610]]
    hw := by decide
    g := ![![![9, 14, -3], ![-7, 0, 0]], ![![9, 110, -23], ![-62, 0, 0]]]
    h := ![![![45, 237, -32], ![-603, -126, 0]], ![![-179, -1939, 257], ![4981, 1038, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N2 : Ideal.span {2} * I2N2 =  Ideal.span {B.equivFun.symm ![1449, 42, -37]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS2 


noncomputable def E3RS0 : RelationCertificate Table 2 ![![3, 0, 0], ![-29, -3, 1]]
  ![13, 6, 1] ![![2, 0, 0], ![-30, -2, 1]] where
    su := ![![6, 0, 0], ![-58, -6, 2]]
    hsu := by decide
    w := ![![26, 12, 2], ![-6, 0, 0]]
    hw := by decide
    g := ![![![0, 0, 0], ![-1, 0, 0]], ![![28, 7, -2], ![3, 0, 0]]]
    h := ![![![14, 3, 0], ![1, 0, 0]], ![![28, 3, -1], ![3, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {2} * I3N0 =  Ideal.span {B.equivFun.symm ![13, 6, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 2 ![![3, 0, 0], ![1, 1, 0]]
  ![11303, 5462, 939] ![![2, 0, 0], ![-30, -2, 1]] where
    su := ![![6, 0, 0], ![2, 2, 0]]
    hsu := by decide
    w := ![![22606, 10924, 1878], ![-530, -256, -44]]
    hw := by decide
    g := ![![![28, -46, 9], ![-7, 0, 0]], ![![9, 81, -17], ![-18, 0, 0]]]
    h := ![![![2978, 1415, 697], ![2369, -576, 0]], ![![-70, -35, -18], ![-55, 16, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {2} * I3N1 =  Ideal.span {B.equivFun.symm ![11303, 5462, 939]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E3RS1 


noncomputable def E19RS1 : RelationCertificate Table 2 ![![19, 0, 0], ![-8, 1, 0]]
  ![75, 6, -1] ![![2, 0, 0], ![-30, -2, 1]] where
    su := ![![38, 0, 0], ![-16, 2, 0]]
    hsu := by decide
    w := ![![150, 12, -2], ![-1098, -32, 28]]
    hw := by decide
    g := ![![![6, -116, 24], ![67, 0, 0]], ![![13, 95, -20], ![-53, 0, 0]]]
    h := ![![![1201, -160, 3], ![2843, -29, 0]], ![![-8767, 1199, -30], ![-20753, 292, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {2} * I19N1 =  Ideal.span {B.equivFun.symm ![75, 6, -1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E19RS1 


noncomputable def E23RS1 : RelationCertificate Table 2 ![![23, 0, 0], ![9, 1, 0]]
  ![227, 110, 19] ![![2, 0, 0], ![-30, -2, 1]] where
    su := ![![46, 0, 0], ![18, 2, 0]]
    hsu := by decide
    w := ![![454, 220, 38], ![-26, -8, 0]]
    hw := by decide
    g := ![![![-24, 128, -26], ![229, 0, 0]], ![![9, 33, -7], ![58, 0, 0]]]
    h := ![![![3280, 429, 13], ![-8357, -140, 0]], ![![-206, -33, -2], ![525, 23, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {2} * I23N1 =  Ideal.span {B.equivFun.symm ![227, 110, 19]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E23RS1 
