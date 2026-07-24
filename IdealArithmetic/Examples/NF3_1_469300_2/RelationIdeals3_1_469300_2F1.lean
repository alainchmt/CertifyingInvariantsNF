import IdealArithmetic.Examples.NF3_1_469300_2.PrimesBelow3_1_469300_2F1
import IdealArithmetic.Examples.NF3_1_469300_2.ClassGroupData3_1_469300_2

set_option linter.all false

noncomputable section


noncomputable def E37RS1 : RelationCertificate Table 6 ![![37, 0, 0], ![11, 1, 0]]
  ![26, 10, 1] ![![6, 0, 0], ![-61, -6, 1]] where
    su := ![![222, 0, 0], ![66, 6, 0]]
    hsu := by decide
    w := ![![156, 60, 6], ![-66, -6, 0]]
    hw := by decide
    g := ![![![54, -37, 2], ![-463, -74, 0]], ![![49, -7, 0], ![-127, -21, 0]]]
    h := ![![![980, 100, 1], ![-3294, -36, 0]], ![![-429, -50, -1], ![1442, 37, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {6} * I37N1 =  Ideal.span {B.equivFun.symm ![26, 10, 1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E37RS1 


noncomputable def E41RS1 : RelationCertificate Table 96 ![![41, 0, 0], ![-19, 1, 0]]
  ![-436, -41, 7] ![![96, 0, 0], ![2425, 236, -39]] where
    su := ![![3936, 0, 0], ![-1824, 96, 0]]
    hsu := by decide
    w := ![![-41856, -3936, 672], ![178080, 2784, -1632]]
    hw := by decide
    g := ![![![2355941574, -9670173863, 104997634], ![35696909579, 5856354664, 0]], ![![-1120511621, 4599233625, -49937924], ![-16977815945, -2785342293, 0]]]
    h := ![![![-3996, 250, -2], ![-8600, 89, 0]], ![![17028, -996, 5], ![36647, -222, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {96} * I41N1 =  Ideal.span {B.equivFun.symm ![-436, -41, 7]} * (J0 ^ 8*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8J1_1 E41RS1 


noncomputable def E43RS1 : RelationCertificate Table 12 ![![43, 0, 0], ![10, 1, 0]]
  ![-64, -5, 1] ![![12, 0, 0], ![-61, -6, 1]] where
    su := ![![516, 0, 0], ![120, 12, 0]]
    hsu := by decide
    w := ![![-768, -60, 12], ![-276, 24, 0]]
    hw := by decide
    g := ![![![2055777, -281778, -809], ![-10309057, -1719794, 0]], ![![451118, -61826, -178], ![-2262054, -377365, 0]]]
    h := ![![![-188, -29, -1], ![802, 44, 0]], ![![-71, -17, -1], ![303, 43, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {12} * I43N1 =  Ideal.span {B.equivFun.symm ![-64, -5, 1]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E43RS1 


noncomputable def E47RS0 : RelationCertificate Table 72 ![![47, 0, 0], ![-22, 1, 0]]
  ![-64, -2, 1] ![![72, 0, 0], ![-39, -4, 1]] where
    su := ![![3384, 0, 0], ![-1584, 72, 0]]
    hsu := by decide
    w := ![![-4608, -144, 72], ![216, 144, 0]]
    hw := by decide
    g := ![![![441, 70, -3], ![-203, -104, 0]], ![![-173, -28, 1], ![102, 43, 0]]]
    h := ![![![-652, 52, -1], ![-1390, 48, 0]], ![![67, -3, 0], ![143, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N0 : Ideal.span {72} * I47N0 =  Ideal.span {B.equivFun.symm ![-64, -2, 1]} * (J0 ^ 4*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_2 E47RS0 


noncomputable def E47RS1 : RelationCertificate Table 96 ![![47, 0, 0], ![-14, 1, 0]]
  ![-116, -13, 2] ![![96, 0, 0], ![-15, -4, 1]] where
    su := ![![4512, 0, 0], ![-1344, 96, 0]]
    hsu := by decide
    w := ![![-11136, -1248, 192], ![-6240, -576, 96]]
    hw := by decide
    g := ![![![4596173, 960961, -41727], ![-758535, -1191080, 0]], ![![-1253486, -262076, 11379], ![206978, 324840, 0]]]
    h := ![![![-173444, 13299, -65], ![-582268, 3057, 0]], ![![-97215, 7462, -37], ![-326360, 1740, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {96} * I47N1 =  Ideal.span {B.equivFun.symm ![-116, -13, 2]} * (J0 ^ 9*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_9J1_1 E47RS1 


noncomputable def E47RS2 : RelationCertificate Table 64 ![![47, 0, 0], ![-11, 1, 0]]
  ![-44, -7, 1] ![![64, 0, 0], ![-1213, -108, 19]] where
    su := ![![3008, 0, 0], ![-704, 64, 0]]
    hsu := by decide
    w := ![![-2816, -448, 64], ![-38208, -2432, 512]]
    hw := by decide
    g := ![![![92887, -182841, 17686], ![-1427195, -240600, 0]], ![![-19836, 41234, -3996], ![321175, 54135, 0]]]
    h := ![![![-35684, 3398, -14], ![-152464, 659, 0]], ![![-484716, 46045, -180], ![-2071005, 8468, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N2 : Ideal.span {64} * I47N2 =  Ideal.span {B.equivFun.symm ![-44, -7, 1]} * (J0 ^ 11*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_11J1_0 E47RS2 


noncomputable def E61RS0 : RelationCertificate Table 64 ![![61, 0, 0], ![3, 1, 0]]
  ![12, 7, 1] ![![64, 0, 0], ![-1213, -108, 19]] where
    su := ![![3904, 0, 0], ![192, 64, 0]]
    hsu := by decide
    w := ![![768, 448, 64], ![-5056, -192, 64]]
    hw := by decide
    g := ![![![262933, -522295, 50537], ![-4075375, -687016, 0]], ![![15285, -29645, 2866], ![-231537, -39035, 0]]]
    h := ![![![2142, 714, 0], ![-43550, 1, 0]], ![![-14101, -4715, -5], ![286694, 306, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N0 : Ideal.span {64} * I61N0 =  Ideal.span {B.equivFun.symm ![12, 7, 1]} * (J0 ^ 11*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_11J1_0 E61RS0 


noncomputable def E61RS1 : RelationCertificate Table 288 ![![61, 0, 0], ![13, 1, 0]]
  ![-44, -7, -1] ![![288, 0, 0], ![4473, 524, -71]] where
    su := ![![17568, 0, 0], ![3744, 288, 0]]
    hsu := by decide
    w := ![![-12672, -2016, -288], ![-207072, -29952, 1728]]
    hw := by decide
    g := ![![![-5119, 9552, 1175], ![-19515, -3290, 0]], ![![-4199, 1776, 311], ![-4163, -735, 0]]]
    h := ![![![-113102, -9259, -43], ![530706, 2622, 0]], ![![-1847663, -151126, -692], ![8669748, 42218, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {288} * I61N1 =  Ideal.span {B.equivFun.symm ![-44, -7, -1]} * (J0 ^ 7*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7J1_2 E61RS1 


noncomputable def E61RS2 : RelationCertificate Table 48 ![![61, 0, 0], ![-16, 1, 0]]
  ![28, -1, -1] ![![48, 0, 0], ![-433, -36, 7]] where
    su := ![![2928, 0, 0], ![-768, 48, 0]]
    hsu := by decide
    w := ![![1344, -48, -48], ![-1104, -480, 0]]
    hw := by decide
    g := ![![![9023040, 3877538, 1873326], ![-84029707, -13841342, 0]], ![![-2450288, -1053026, -508748], ![22820264, 3758943, 0]]]
    h := ![![![24652, -1621, 5], ![93984, -306, 0]], ![![-20147, 1339, -5], ![-76809, 305, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N2 : Ideal.span {48} * I61N2 =  Ideal.span {B.equivFun.symm ![28, -1, -1]} * (J0 ^ 6*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6J1_1 E61RS2 


noncomputable def E73RS1 : RelationCertificate Table 192 ![![73, 0, 0], ![-5, 1, 0]]
  ![88, 2, -1] ![![192, 0, 0], ![-15, -4, 1]] where
    su := ![![14016, 0, 0], ![-960, 192, 0]]
    hsu := by decide
    w := ![![16896, 384, -192], ![960, -192, 0]]
    hw := by decide
    g := ![![![-14965934, -3145304, 152117], ![1235565, 7610507, 0]], ![![992230, 208532, -10086], ![-81745, -504564, 0]]]
    h := ![![![88876, -17850, 15], ![1297572, -1096, 0]], ![![5060, -1012, 0], ![73875, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {192} * I73N1 =  Ideal.span {B.equivFun.symm ![88, 2, -1]} * (J0 ^ 11*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_11J1_1 E73RS1 


noncomputable def E79RS1 : RelationCertificate Table 18 ![![79, 0, 0], ![-1, 1, 0]]
  ![-62, -16, -1] ![![18, 0, 0], ![-61, -6, 1]] where
    su := ![![1422, 0, 0], ![-18, 18, 0]]
    hsu := by decide
    w := ![![-1116, -288, -18], ![-18, 18, 0]]
    hw := by decide
    g := ![![![3400034, -42422, -30127], ![-11509667, -2008657, 0]], ![![-43264, 545, 383], ![146629, 25587, 0]]]
    h := ![![![0, 0, -1], ![62, 78, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {18} * I79N1 =  Ideal.span {B.equivFun.symm ![-62, -16, -1]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E79RS1 
