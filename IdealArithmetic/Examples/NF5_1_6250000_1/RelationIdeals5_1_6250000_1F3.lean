import IdealArithmetic.Examples.NF5_1_6250000_1.PrimesBelow5_1_6250000_1F3
import IdealArithmetic.Examples.NF5_1_6250000_1.ClassGroupData5_1_6250000_1

set_option linter.all false

noncomputable section


noncomputable def E127RS2 : RelationCertificate Table 2 ![![127, 0, 0, 0, 0], ![-24, 1, 0, 0, 0]]
  ![2, 1, 1, 0, 3] ![![2, 0, 0, 0, 0], ![2, 0, -2, -1, -3]] where
    su := ![![254, 0, 0, 0, 0], ![-48, 2, 0, 0, 0]]
    hsu := by decide
    w := ![![4, 2, 2, 0, 6], ![-2, 0, -4, -4, -6]]
    hw := by decide
    g := ![![![216321, -29298, 69476, 37631, 112971], ![-41425, 104949, 11661, 0, 0]], ![![-28225, 3832, -9066, -4909, -14742], ![5410, -13692, -1521, 0, 0]]]
    h := ![![![-9872845, 721076, -7809283, 656855, -3471], ![-52239213, -84328, -41324575, 36735, 0]], ![![9873140, -721058, 7809593, -656881, 3471], ![52240774, 84557, 41326225, -36735, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N2 : Ideal.span {2} * I127N2 =  Ideal.span {B.equivFun.symm ![2, 1, 1, 0, 3]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E127RS2 


noncomputable def E131RS2 : RelationCertificate Table 4 ![![131, 0, 0, 0, 0], ![61, 1, 0, 0, 0]]
  ![-2, 5, -3, -2, -9] ![![4, 0, 0, 0, 0], ![2, 11, -9, -3, -14]] where
    su := ![![524, 0, 0, 0, 0], ![244, 4, 0, 0, 0]]
    hsu := by decide
    w := ![![-8, 20, -12, -8, -36], ![-52, -4, 12, 16, 16]]
    hw := by decide
    g := ![![![33683, -4664, -3825, 1636, 1119], ![7533, 16515, -367, 0, 0]], ![![15999, -2222, -1811, 779, 541], ![3581, 7845, -174, 0, 0]]]
    h := ![![![-105816473, -4734057, -279726540, -9273182, -18951], ![227235038, -3403933, 600773228, 206881, 0]], ![![-258935719, -11584286, -684500494, -22691788, -46372], ![556050172, -8329759, 1470112820, 506228, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N2 : Ideal.span {4} * I131N2 =  Ideal.span {B.equivFun.symm ![-2, 5, -3, -2, -9]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E131RS2 


noncomputable def E139RS2 : RelationCertificate Table 2 ![![139, 0, 0, 0, 0], ![-15, 1, 0, 0, 0]]
  ![4, 3, 3, 2, 5] ![![2, 0, 0, 0, 0], ![2, 0, -2, -1, -3]] where
    su := ![![278, 0, 0, 0, 0], ![-30, 2, 0, 0, 0]]
    hsu := by decide
    w := ![![8, 6, 6, 4, 10], ![-10, -8, -16, -8, -20]]
    hw := by decide
    g := ![![![7054238, -1557429, 2357573, 1212624, 3637924], ![-1366527, 3656340, 135420, 0, 0]], ![![-751689, 165958, -251217, -129214, -387648], ![145617, -389613, -14430, 0, 0]]]
    h := ![![![56512588, -11324512, 115850792, -15462250, 14303], ![523650180, 1556067, 1073632320, -165676, 0]], ![![-78318368, 15694161, -160552546, 21428456, -19822], ![-725704289, -2156372, -1487900070, 229604, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N2 : Ideal.span {2} * I139N2 =  Ideal.span {B.equivFun.symm ![4, 3, 3, 2, 5]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E139RS2 
