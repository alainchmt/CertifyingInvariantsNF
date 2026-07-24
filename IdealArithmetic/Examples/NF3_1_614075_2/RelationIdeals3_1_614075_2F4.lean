import IdealArithmetic.Examples.NF3_1_614075_2.PrimesBelow3_1_614075_2F4
import IdealArithmetic.Examples.NF3_1_614075_2.ClassGroupData3_1_614075_2

set_option linter.all false

noncomputable section


noncomputable def E199RS1 : RelationCertificate Table 8 ![![199, 0, 0], ![47, 1, 0]]
  ![-28265, 2149, -621] ![![8, 0, 0], ![0, 1, 0]] where
    su := ![![1592, 0, 0], ![376, 8, 0]]
    hsu := by decide
    w := ![![-226120, 17192, -4968], ![69552, -5288, 1528]]
    hw := by decide
    g := ![![![87, 41, -1251211], ![9, 10009710, 0]], ![![19, 9, -307231], ![7, 2457855, 0]]]
    h := ![![![-402907, -9117, -15], ![1705324, 2364, 0]], ![![123862, 2774, 4], ![-524252, -605, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R199N1 : Ideal.span {8} * I199N1 =  Ideal.span {B.equivFun.symm ![-28265, 2149, -621]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E199RS1 


noncomputable def E211RS1 : RelationCertificate Table 32 ![![211, 0, 0], ![-66, 1, 0]]
  ![-1493, 113, -33] ![![32, 0, 0], ![16, 1, 0]] where
    su := ![![6752, 0, 0], ![-2112, 32, 0]]
    hsu := by decide
    w := ![![-47776, 3616, -1056], ![-20192, 1536, -448]]
    hw := by decide
    g := ![![![-66, 4543, 284], ![145, -9090, 0]], ![![2, -1409, -88], ![-8, 2817, 0]]]
    h := ![![![-11411, 229, -1], ![-36458, 178, 0]], ![![-4765, 134, -1], ![-15224, 197, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R211N1 : Ideal.span {32} * I211N1 =  Ideal.span {B.equivFun.symm ![-1493, 113, -33]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E211RS1 
