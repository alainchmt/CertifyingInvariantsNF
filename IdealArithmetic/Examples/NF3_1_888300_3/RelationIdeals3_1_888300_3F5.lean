import IdealArithmetic.Examples.NF3_1_888300_3.PrimesBelow3_1_888300_3F5
import IdealArithmetic.Examples.NF3_1_888300_3.ClassGroupData3_1_888300_3

set_option linter.all false

noncomputable section


noncomputable def E263RS1 : RelationCertificate Table 21 ![![263, 0, 0], ![-68, 1, 0]]
  ![211, 13, -2] ![![21, 0, 0], ![-93, -1, 1]] where
    su := ![![5523, 0, 0], ![-1428, 21, 0]]
    hsu := by decide
    w := ![![4431, 273, -42], ![-8673, -630, 84]]
    hw := by decide
    g := ![![![169, 128, 16], ![-388, -55, 0]], ![![-20, -30, -4], ![96, 13, 0]]]
    h := ![![![330041, -5126, 4], ![1276479, -1054, 0]], ![![-645871, 10043, -8], ![-2497995, 2108, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R263N1 : Ideal.span {21} * I263N1 =  Ideal.span {B.equivFun.symm ![211, 13, -2]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E263RS1 
