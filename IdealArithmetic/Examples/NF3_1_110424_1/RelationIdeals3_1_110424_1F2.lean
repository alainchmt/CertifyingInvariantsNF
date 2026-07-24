import IdealArithmetic.Examples.NF3_1_110424_1.PrimesBelow3_1_110424_1F2
import IdealArithmetic.Examples.NF3_1_110424_1.ClassGroupData3_1_110424_1

set_option linter.all false

noncomputable section


noncomputable def E83RS0 : RelationCertificate Table 3 ![![83, 0, 0], ![5, 1, 0]]
  ![-295265, 191505, -345584] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![249, 0, 0], ![15, 3, 0]]
    hsu := by decide
    w := ![![-885795, 574515, -1036752], ![-19365597, 3352080, 2185782]]
    hw := by decide
    g := ![![![6237613814592, 1148353990916, 525671132210], ![-1696419941225, 0, 0]], ![![725441146976, 133554795321, 61136113972], ![-197295450549, 0, 0]]]
    h := ![![![-80227080, -282417214, -242163088], ![-8235573, 3349865120, 0]], ![![-1737490273, -6116387292, -5244462362], ![-178359484, 72548517440, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N0 : Ideal.span {3} * I83N0 =  Ideal.span {B.equivFun.symm ![-295265, 191505, -345584]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E83RS0 


noncomputable def E83RS1 : RelationCertificate Table 3 ![![83, 0, 0], ![16, 1, 0]]
  ![-11037933, 2518394, -394492] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![249, 0, 0], ![48, 3, 0]]
    hsu := by decide
    w := ![![-33113799, 7555182, -1183476], ![-6805815, -4574619, 16293840]]
    hw := by decide
    g := ![![![-155166379082038, -28566361427831, -13076552764804], ![42200005884739, 0, 0]], ![![-38610234483765, -7108201658128, -3253854162708], ![10500677608549, 0, 0]]]
    h := ![![![144753377, 1380744829, 460412284], ![44539779, -6369102344, 0]], ![![28728773, 274016180, 91445788], ![8839559, -1264094854, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {3} * I83N1 =  Ideal.span {B.equivFun.symm ![-11037933, 2518394, -394492]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E83RS1 
