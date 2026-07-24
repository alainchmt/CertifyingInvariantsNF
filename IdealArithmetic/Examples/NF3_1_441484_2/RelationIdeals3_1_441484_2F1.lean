import IdealArithmetic.Examples.NF3_1_441484_2.PrimesBelow3_1_441484_2F1
import IdealArithmetic.Examples.NF3_1_441484_2.ClassGroupData3_1_441484_2

set_option linter.all false

noncomputable section


noncomputable def E43RS1 : RelationCertificate Table 9 ![![43, 0, 0], ![13, 1, 0]]
  ![-261516113, 13696103, -21800387] ![![9, 0, 0], ![-3, 1, 0]] where
    su := ![![387, 0, 0], ![117, 9, 0]]
    hsu := by decide
    w := ![![-2353645017, 123264927, -196203483], ![3637886571, -190523133, 303259842]]
    hw := by decide
    g := ![![![4559, 1603, 703], ![-1334, -2, 0]], ![![-414, 670, 526], ![215, -6, 0]]]
    h := ![![![2891900288, 19777423350, 12104463529], ![1334235545, -47319430194, 0]], ![![-4469835173, -30568765595, -18709136256], ![-2062247000, 73138777686, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {9} * I43N1 =  Ideal.span {B.equivFun.symm ![-261516113, 13696103, -21800387]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E43RS1 


noncomputable def E43RS2 : RelationCertificate Table 3 ![![43, 0, 0], ![-20, 1, 0]]
  ![20056, 1733, -74] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![129, 0, 0], ![-60, 3, 0]]
    hsu := by decide
    w := ![![60168, 5199, -222], ![14745, 28869, 19359]]
    hw := by decide
    g := ![![![47564416, -2242070, 3964735], ![-747354, 86, 0]], ![![-34191928, 1611690, -2850145], ![537233, -41, 0]]]
    h := ![![![81547, -520495, 382577], ![-50007, -1495535, 0]], ![![17495, -111333, 82141], ![-10708, -320510, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N2 : Ideal.span {3} * I43N2 =  Ideal.span {B.equivFun.symm ![20056, 1733, -74]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E43RS2 


noncomputable def E59RS1 : RelationCertificate Table 9 ![![59, 0, 0], ![-13, 1, 0]]
  ![-23, -1, 1] ![![9, 0, 0], ![-3, 1, 0]] where
    su := ![![531, 0, 0], ![-117, 9, 0]]
    hsu := by decide
    w := ![![-207, -9, 9], ![-63, -27, -18]]
    hw := by decide
    g := ![![![102, 70, 377], ![-17, -308, 0]], ![![-13, -11, -54], ![12, 44, 0]]]
    h := ![![![267, -753, 1037], ![-70, -5562, 0]], ![![86, -220, 302], ![17, -1620, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {9} * I59N1 =  Ideal.span {B.equivFun.symm ![-23, -1, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E59RS1 


noncomputable def E71RS1 : RelationCertificate Table 9 ![![71, 0, 0], ![-30, 1, 0]]
  ![-3426664, 179461, -285652] ![![9, 0, 0], ![-3, 1, 0]] where
    su := ![![639, 0, 0], ![-270, 9, 0]]
    hsu := by decide
    w := ![![-30839976, 1615149, -2570868], ![47667483, -2496438, 3973635]]
    hw := by decide
    g := ![![![-1450, -376, -831], ![448, 648, 0]], ![![669, 128, 318], ![-204, -268, 0]]]
    h := ![![![-1883067749, 19442621079, -8561384087], ![1069502227, 55259816775, 0]], ![![2910543815, -30051281811, 13232812841], ![-1653064701, -85411751836, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {9} * I71N1 =  Ideal.span {B.equivFun.symm ![-3426664, 179461, -285652]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E71RS1 
