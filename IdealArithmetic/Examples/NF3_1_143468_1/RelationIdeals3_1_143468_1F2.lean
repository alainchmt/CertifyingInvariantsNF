import IdealArithmetic.Examples.NF3_1_143468_1.PrimesBelow3_1_143468_1F2
import IdealArithmetic.Examples.NF3_1_143468_1.ClassGroupData3_1_143468_1

set_option linter.all false

noncomputable section


noncomputable def E83RS1 : RelationCertificate Table 5 ![![83, 0, 0], ![-20, 1, 0]]
  ![-625, 274, -36] ![![5, 0, 0], ![-23, 4, 1]] where
    su := ![![415, 0, 0], ![-100, 5, 0]]
    hsu := by decide
    w := ![![-3125, 1370, -180], ![3565, -1560, 205]]
    hw := by decide
    g := ![![![8, 14, 3], ![41, 0, 0]], ![![5, -5, -1], ![-5, 0, 0]]]
    h := ![![![-67515, 3550, -9], ![-280156, 711, 0]], ![![77051, -4026, 9], ![319726, -706, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {5} * I83N1 =  Ideal.span {B.equivFun.symm ![-625, 274, -36]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E83RS1 


noncomputable def E107RS0 : RelationCertificate Table 5 ![![107, 0, 0], ![43, 1, 0]]
  ![38990, -17082, 2243] ![![5, 0, 0], ![-23, 4, 1]] where
    su := ![![535, 0, 0], ![215, 5, 0]]
    hsu := by decide
    w := ![![194950, -85410, 11215], ![-222065, 97290, -12775]]
    hw := by decide
    g := ![![![-204, -308, -23], ![726, 0, 0]], ![![-88, -141, -11], ![319, 0, 0]]]
    h := ![![![75788, 1854, 27], ![-187682, -646, 0]], ![![-86442, -2168, -32], ![214067, 869, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N0 : Ideal.span {5} * I107N0 =  Ideal.span {B.equivFun.symm ![38990, -17082, 2243]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E107RS0 


noncomputable def E107RS1 : RelationCertificate Table 5 ![![107, 0, 0], ![-26, 1, 0]]
  ![11125, -4874, 640] ![![5, 0, 0], ![-23, 4, 1]] where
    su := ![![535, 0, 0], ![-130, 5, 0]]
    hsu := by decide
    w := ![![55625, -24370, 3200], ![-63365, 27760, -3645]]
    hw := by decide
    g := ![![![126, 210, 19], ![-379, 0, 0]], ![![-16, -43, -4], ![82, 0, 0]]]
    h := ![![![1562495, -62998, 116], ![6429840, -11772, 0]], ![![-1779851, 71810, -134], ![-7324284, 13609, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {5} * I107N1 =  Ideal.span {B.equivFun.symm ![11125, -4874, 640]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E107RS1 
