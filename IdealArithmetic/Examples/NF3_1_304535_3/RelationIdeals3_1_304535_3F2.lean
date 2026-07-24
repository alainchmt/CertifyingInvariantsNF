import IdealArithmetic.Examples.NF3_1_304535_3.PrimesBelow3_1_304535_3F2
import IdealArithmetic.Examples.NF3_1_304535_3.ClassGroupData3_1_304535_3

set_option linter.all false

noncomputable section


noncomputable def E83RS1 : RelationCertificate Table 9 ![![83, 0, 0], ![24, 1, 0]]
  ![-9, -4, 4] ![![9, 0, 0], ![18, -2, 4]] where
    su := ![![747, 0, 0], ![216, 9, 0]]
    hsu := by decide
    w := ![![-81, -36, 36], ![-2682, 450, -36]]
    hw := by decide
    g := ![![![-1911, -494, 1514], ![-3008, 167, 0]], ![![-560, -147, 446], ![-888, 49, 0]]]
    h := ![![![-1323, -65, -2], ![4575, 34, 0]], ![![-43358, -2012, -43], ![149934, 713, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {9} * I83N1 =  Ideal.span {B.equivFun.symm ![-9, -4, 4]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E83RS1 


noncomputable def E83RS2 : RelationCertificate Table 9 ![![83, 0, 0], ![-35, 1, 0]]
  ![4, 0, 1] ![![9, 0, 0], ![-21, -1, -4]] where
    su := ![![747, 0, 0], ![-315, 9, 0]]
    hsu := by decide
    w := ![![36, 0, 9], ![-189, -81, -9]]
    hw := by decide
    g := ![![![5, 1, 1], ![2, 0, 0]], ![![28, -2, -3], ![-8, 1, 0]]]
    h := ![![![108, 18, -3], ![256, 50, 0]], ![![-252, 21, -2], ![-597, 33, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N2 : Ideal.span {9} * I83N2 =  Ideal.span {B.equivFun.symm ![4, 0, 1]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E83RS2 


noncomputable def E89RS1 : RelationCertificate Table 3 ![![89, 0, 0], ![-8, 1, 0]]
  ![-8, 1, 0] ![![3, 0, 0], ![6, 1, 1]] where
    su := ![![267, 0, 0], ![-24, 3, 0]]
    hsu := by decide
    w := ![![-24, 3, 0], ![57, -9, -3]]
    hw := by decide
    g := ![![![-11, 1, 2], ![-11, 0, 0]], ![![-5, -1, -1], ![3, 0, 0]]]
    h := ![![![-184, 31, -5], ![-2046, 89, 0]], ![![459, -51, -4], ![5104, 71, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {3} * I89N1 =  Ideal.span {B.equivFun.symm ![-8, 1, 0]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E89RS1 


noncomputable def E97RS1 : RelationCertificate Table 9 ![![97, 0, 0], ![-28, 1, 0]]
  ![-394, -33, -25] ![![9, 0, 0], ![-21, -1, -4]] where
    su := ![![873, 0, 0], ![-252, 9, 0]]
    hsu := by decide
    w := ![![-3546, -297, -225], ![24759, 2088, 1566]]
    hw := by decide
    g := ![![![-3464338, 1068104, 2765340], ![6735795, -411026, 0]], ![![948850, -292537, -757383], ![-1844828, 112574, 0]]]
    h := ![![![-117402, 4471, -50], ![-406700, 965, 0]], ![![819791, -31068, 322], ![2839892, -6212, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {9} * I97N1 =  Ideal.span {B.equivFun.symm ![-394, -33, -25]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E97RS1 


noncomputable def E107RS1 : RelationCertificate Table 9 ![![107, 0, 0], ![-4, 1, 0]]
  ![102, -14, -1] ![![9, 0, 0], ![2, 1, 0]] where
    su := ![![963, 0, 0], ![-36, 9, 0]]
    hsu := by decide
    w := ![![918, -126, -9], ![99, 81, -72]]
    hw := by decide
    g := ![![![28637, -1208498, -3056806], ![-127907, 5502275, 0]], ![![-937, 39966, 101092], ![4240, -181965, 0]]]
    h := ![![![114, -26, -3], ![3024, 64, 0]], ![![13, 0, -4], ![345, 84, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {9} * I107N1 =  Ideal.span {B.equivFun.symm ![102, -14, -1]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E107RS1 


noncomputable def E109RS1 : RelationCertificate Table 9 ![![109, 0, 0], ![-20, 1, 0]]
  ![86, -1, -9] ![![9, 0, 0], ![3, 1, 1]] where
    su := ![![981, 0, 0], ![-180, 9, 0]]
    hsu := by decide
    w := ![![774, -9, -81], ![-792, -36, 117]]
    hw := by decide
    g := ![![![2121, 117, 68], ![734, 0, 0]], ![![-262, -15, -9], ![-84, 0, 0]]]
    h := ![![![17094, -871, 4], ![93158, -89, 0]], ![![-17432, 904, -8], ![-95000, 177, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {9} * I109N1 =  Ideal.span {B.equivFun.symm ![86, -1, -9]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E109RS1 


noncomputable def E113RS0 : RelationCertificate Table 9 ![![113, 0, 0], ![34, 1, 0]]
  ![4, 6, -5] ![![9, 0, 0], ![-21, -1, -4]] where
    su := ![![1017, 0, 0], ![306, 9, 0]]
    hsu := by decide
    w := ![![36, 54, -45], ![-2079, 423, -81]]
    hw := by decide
    g := ![![![1472, -472, -1175], ![-2835, 178, 0]], ![![460, -149, -369], ![-889, 56, 0]]]
    h := ![![![-12, -34, -5], ![40, 112, 0]], ![![-667, -39, -3], ![2210, 66, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N0 : Ideal.span {9} * I113N0 =  Ideal.span {B.equivFun.symm ![4, 6, -5]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E113RS0 


noncomputable def E113RS1 : RelationCertificate Table 9 ![![113, 0, 0], ![45, 1, 0]]
  ![-19, 0, 2] ![![9, 0, 0], ![-21, -1, -4]] where
    su := ![![1017, 0, 0], ![405, 9, 0]]
    hsu := by decide
    w := ![![-171, 0, 18], ![189, -135, 90]]
    hw := by decide
    g := ![![![4, -1, 6], ![19, 0, 0]], ![![222, -68, -172], ![-417, 26, 0]]]
    h := ![![![-2693, -114, -6], ![6762, 136, 0]], ![![2787, 61, 0], ![-6998, 2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {9} * I113N1 =  Ideal.span {B.equivFun.symm ![-19, 0, 2]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E113RS1 


noncomputable def E127RS0 : RelationCertificate Table 9 ![![127, 0, 0], ![30, 1, 0]]
  ![-1249, -105, -79] ![![9, 0, 0], ![-21, -1, -4]] where
    su := ![![1143, 0, 0], ![270, 9, 0]]
    hsu := by decide
    w := ![![-11241, -945, -711], ![78624, 6597, 4968]]
    hw := by decide
    g := ![![![-3322702, 1024438, 2652261], ![6460374, -394220, 0]], ![![-866778, 267246, 691898], ![1685323, -102840, 0]]]
    h := ![![![-239707, -8569, -97], ![1014718, 2448, 0]], ![![1676388, 59823, 661], ![-7096418, -16679, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N0 : Ideal.span {9} * I127N0 =  Ideal.span {B.equivFun.symm ![-1249, -105, -79]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E127RS0 


noncomputable def E127RS2 : RelationCertificate Table 9 ![![127, 0, 0], ![53, 1, 0]]
  ![-24, 2, 1] ![![9, 0, 0], ![18, -2, 4]] where
    su := ![![1143, 0, 0], ![477, 9, 0]]
    hsu := by decide
    w := ![![-216, 18, 9], ![198, 126, -126]]
    hw := by decide
    g := ![![![-1610281, -407655, 1295223], ![-2554316, 143976, 0]], ![![-766804, -194121, 616772], ![-1216339, 68560, 0]]]
    h := ![![![-198, -25, -2], ![474, 51, 0]], ![![102, -18, -2], ![-244, 48, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N2 : Ideal.span {9} * I127N2 =  Ideal.span {B.equivFun.symm ![-24, 2, 1]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E127RS2 


noncomputable def E131RS1 : RelationCertificate Table 9 ![![131, 0, 0], ![-3, 1, 0]]
  ![64, -15, 4] ![![9, 0, 0], ![3, 1, 0]] where
    su := ![![1179, 0, 0], ![-27, 9, 0]]
    hsu := by decide
    w := ![![576, -135, 36], ![612, -9, -63]]
    hw := by decide
    g := ![![![-133, -1238, -2081], ![-174, 3724, 0]], ![![-7, 19, 33], ![5, -60, 0]]]
    h := ![![![68, -22, -1], ![2948, 27, 0]], ![![76, -24, -2], ![3296, 51, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {9} * I131N1 =  Ideal.span {B.equivFun.symm ![64, -15, 4]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E131RS1 


noncomputable def E137RS0 : RelationCertificate Table 9 ![![137, 0, 0], ![18, 1, 0]]
  ![8, 1, 1] ![![9, 0, 0], ![3, 1, 1]] where
    su := ![![1233, 0, 0], ![162, 9, 0]]
    hsu := by decide
    w := ![![72, 9, 9], ![234, 18, 9]]
    hw := by decide
    g := ![![![-9, 1, 0], ![4, 0, 0]], ![![-1, 0, 0], ![1, 0, 0]]]
    h := ![![![1012, 49, -2], ![-7702, 55, 0]], ![![3298, 176, -2], ![-25100, 55, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N0 : Ideal.span {9} * I137N0 =  Ideal.span {B.equivFun.symm ![8, 1, 1]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E137RS0 


noncomputable def E137RS1 : RelationCertificate Table 3 ![![137, 0, 0], ![54, 1, 0]]
  ![18, 2, 1] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![411, 0, 0], ![162, 3, 0]]
    hsu := by decide
    w := ![![54, 6, 3], ![87, 9, 9]]
    hw := by decide
    g := ![![![-4, -95, 516], ![-29, -309, 0]], ![![-1, -38, 207], ![-12, -124, 0]]]
    h := ![![![90, -20, -2], ![-228, 55, 0]], ![![271, -6, -1], ![-687, 28, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {3} * I137N1 =  Ideal.span {B.equivFun.symm ![18, 2, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E137RS1 


noncomputable def E137RS2 : RelationCertificate Table 3 ![![137, 0, 0], ![65, 1, 0]]
  ![-823, -69, -52] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![411, 0, 0], ![195, 3, 0]]
    hsu := by decide
    w := ![![-2469, -207, -156], ![-5460, -459, -345]]
    hw := by decide
    g := ![![![-64, 0, 7], ![1, 0, 0]], ![![-25, -1, -10], ![1, 8, 0]]]
    h := ![![![-76929, -1582, -31], ![162130, 839, 0]], ![![-170170, -3518, -70], ![358638, 1895, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N2 : Ideal.span {3} * I137N2 =  Ideal.span {B.equivFun.symm ![-823, -69, -52]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E137RS2 
