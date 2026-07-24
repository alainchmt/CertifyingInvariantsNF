import IdealArithmetic.Examples.NF3_3_936117_1.PrimesBelow3_3_936117_1F2
import IdealArithmetic.Examples.NF3_3_936117_1.ClassGroupData3_3_936117_1

set_option linter.all false

noncomputable section


noncomputable def E83RS1 : RelationCertificate Table 2 ![![83, 0, 0], ![14, 1, 0]]
  ![13, 9, 1] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![166, 0, 0], ![28, 2, 0]]
    hsu := by decide
    w := ![![26, 18, 2], ![102, 88, 10]]
    hw := by decide
    g := ![![![-1276, 6472, 7779], ![2599, -15557, 0]], ![![-217, 1102, 1324], ![443, -2648, 0]]]
    h := ![![![-13, -1, 0], ![78, 1, 0]], ![![33, 2, 0], ![-192, 5, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {2} * I83N1 =  Ideal.span {B.equivFun.symm ![13, 9, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E83RS1 


noncomputable def E97RS1 : RelationCertificate Table 2 ![![97, 0, 0], ![17, 1, 0]]
  ![617, 165, -27] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![194, 0, 0], ![34, 2, 0]]
    hsu := by decide
    w := ![![1234, 330, -54], ![-1786, -1000, 138]]
    hw := by decide
    g := ![![![5866, 13796, 10539], ![9833, -18963, 0]], ![![1685, 3015, 2022], ![2350, -3483, 0]]]
    h := ![![![3705, 224, 0], ![-21104, -27, 0]], ![![-5411, -335, 0], ![30822, 69, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {2} * I97N1 =  Ideal.span {B.equivFun.symm ![617, 165, -27]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E97RS1 


noncomputable def E103RS1 : RelationCertificate Table 4 ![![103, 0, 0], ![-41, 1, 0]]
  ![-7595, -6503, -745] ![![4, 0, 0], ![1, 1, 0]] where
    su := ![![412, 0, 0], ![-164, 4, 0]]
    hsu := by decide
    w := ![![-30380, -26012, -2980], ![-73900, -63268, -7248]]
    hw := by decide
    g := ![![![1929706336, -32805016932, -34734723353], ![-7718827648, 138938893641, 0]], ![![-786870487, 13376802730, 14163673265], ![3147483063, -56654693168, 0]]]
    h := ![![![-1264460, 34907, -108], ![-3176385, 10379, 0]], ![![-3075952, 84886, -262], ![-7726941, 25174, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {4} * I103N1 =  Ideal.span {B.equivFun.symm ![-7595, -6503, -745]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E103RS1 


noncomputable def E131RS1 : RelationCertificate Table 4 ![![131, 0, 0], ![-25, 1, 0]]
  ![-87, -51, 7] ![![4, 0, 0], ![1, 1, 0]] where
    su := ![![524, 0, 0], ![-100, 4, 0]]
    hsu := by decide
    w := ![![-348, -204, 28], ![536, 324, -44]]
    hw := by decide
    g := ![![![6183, -105849, -112081], ![-24915, 448330, 0]], ![![-1126, 19290, 20426], ![4543, -81705, 0]]]
    h := ![![![-452, 19, 0], ![-2365, 7, 0]], ![![714, -5, -1], ![3736, 120, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {4} * I131N1 =  Ideal.span {B.equivFun.symm ![-87, -51, 7]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E131RS1 
