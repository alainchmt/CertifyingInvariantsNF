import IdealArithmetic.Examples.NF3_1_117288_3.PrimesBelow3_1_117288_3F2
import IdealArithmetic.Examples.NF3_1_117288_3.ClassGroupData3_1_117288_3

set_option linter.all false

noncomputable section


noncomputable def E83RS1 : RelationCertificate Table 20 ![![83, 0, 0], ![-23, 1, 0]]
  ![-40849, -4978, -1811] ![![20, 0, 0], ![2, 1, 0]] where
    su := ![![1660, 0, 0], ![-460, 20, 0]]
    hsu := by decide
    w := ![![-816980, -99560, -36220], ![-193980, -23640, -8600]]
    hw := by decide
    g := ![![![15300, -3100647, -1554162], ![-153483, 31083302, 0]], ![![-4332, 877892, 440034], ![43477, -8800695, 0]]]
    h := ![![![-20647519, 955279, -2528], ![-74508836, 208013, 0]], ![![-4902415, 226833, -601], ![-17690902, 49453, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {20} * I83N1 =  Ideal.span {B.equivFun.symm ![-40849, -4978, -1811]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E83RS1 
