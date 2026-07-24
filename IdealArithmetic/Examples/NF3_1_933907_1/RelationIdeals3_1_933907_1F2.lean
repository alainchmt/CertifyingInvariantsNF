import IdealArithmetic.Examples.NF3_1_933907_1.PrimesBelow3_1_933907_1F2
import IdealArithmetic.Examples.NF3_1_933907_1.ClassGroupData3_1_933907_1

set_option linter.all false

noncomputable section


noncomputable def E89RS1 : RelationCertificate Table 3 ![![89, 0, 0], ![-19, 1, 0]]
  ![-865, 174, -20] ![![3, 0, 0], ![-80, 4, 1]] where
    su := ![![267, 0, 0], ![-57, 3, 0]]
    hsu := by decide
    w := ![![-2595, 522, -60], ![-9216, 1854, -213]]
    hw := by decide
    g := ![![![23, -2, -2], ![74, 0, 0]], ![![11, -1, 0], ![-8, 0, 0]]]
    h := ![![![-30, -12419, 1380], ![-95, -61420, 0]], ![![-134, -44104, 4901], ![-466, -218130, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {3} * I89N1 =  Ideal.span {B.equivFun.symm ![-865, 174, -20]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E89RS1 


noncomputable def E101RS1 : RelationCertificate Table 3 ![![101, 0, 0], ![47, 1, 0]]
  ![-2187162, 439742, -50509] ![![3, 0, 0], ![-80, 4, 1]] where
    su := ![![303, 0, 0], ![141, 3, 0]]
    hsu := by decide
    w := ![![-6561486, 1319226, -151527], ![-23299257, 4684455, -538059]]
    hw := by decide
    g := ![![![151, -1305, -61], ![-3688, 0, 0]], ![![55, -706, -31], ![-2078, 0, 0]]]
    h := ![![![-30174600, -809540, -7681], ![64796754, 362636, 0]], ![![-107147256, -2874518, -27271], ![230087371, 1287509, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {3} * I101N1 =  Ideal.span {B.equivFun.symm ![-2187162, 439742, -50509]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E101RS1 


noncomputable def E103RS0 : RelationCertificate Table 27 ![![103, 0, 0], ![35, 1, 0]]
  ![-119, 25, -3] ![![27, 0, 0], ![-89, 10, 1]] where
    su := ![![2781, 0, 0], ![945, 27, 0]]
    hsu := by decide
    w := ![![-3213, 675, -81], ![13230, -2619, 297]]
    hw := by decide
    g := ![![![45, -16, 0], ![85, 0, 0]], ![![19, -7, 0], ![37, 0, 0]]]
    h := ![![![-74298, -2500, -21], ![218645, 1080, 0]], ![![305900, 10123, 77], ![-900206, -3960, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N0 : Ideal.span {27} * I103N0 =  Ideal.span {B.equivFun.symm ![-119, 25, -3]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E103RS0 


noncomputable def E103RS1 : RelationCertificate Table 27 ![![103, 0, 0], ![-33, 1, 0]]
  ![-481826, 96874, -11127] ![![27, 0, 0], ![-89, 10, 1]] where
    su := ![![2781, 0, 0], ![-891, 27, 0]]
    hsu := by decide
    w := ![![-13009302, 2615598, -300429], ![49542219, -9960759, 1144098]]
    hw := by decide
    g := ![![![-801, -673, -9], ![2488, 0, 0]], ![![245, 158, 1], ![-616, 0, 0]]]
    h := ![![![-5778224, 186120, -747], ![-18020462, 32907, 0]], ![![22004878, -708714, 2840], ![68626289, -125073, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {27} * I103N1 =  Ideal.span {B.equivFun.symm ![-481826, 96874, -11127]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E103RS1 


noncomputable def E109RS0 : RelationCertificate Table 9 ![![109, 0, 0], ![18, 1, 0]]
  ![-38227940, 7685956, -882813] ![![9, 0, 0], ![-80, 1, 1]] where
    su := ![![981, 0, 0], ![162, 9, 0]]
    hsu := by decide
    w := ![![-344051460, 69173604, -7945317], ![-2404155123, 483369768, -55520109]]
    hw := by decide
    g := ![![![-3221, 12013, -7], ![30556, 0, 0]], ![![-804, 2951, -8], ![7652, 0, 0]]]
    h := ![![![-6108731648, -349366312, -1069397], ![36989640094, 57840730, 0]], ![![-42686458753, -2441294051, -7472701], ![258475381985, 404177754, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N0 : Ideal.span {9} * I109N0 =  Ideal.span {B.equivFun.symm ![-38227940, 7685956, -882813]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E109RS0 


noncomputable def E109RS1 : RelationCertificate Table 243 ![![109, 0, 0], ![37, 1, 0]]
  ![-64132, 12894, -1481] ![![243, 0, 0], ![-89, 37, 1]] where
    su := ![![26487, 0, 0], ![8991, 243, 0]]
    hsu := by decide
    w := ![![-15584076, 3133242, -359883], ![36744273, -7387686, 848556]]
    hw := by decide
    g := ![![![939, -69, -15], ![-112, 0, 0]], ![![455, -44, -7], ![42, 0, 0]]]
    h := ![![![-389896578, -12222558, -88695], ![1148612510, 4833137, 0]], ![![919301523, 28818418, 209124], ![-2708208508, -11395512, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {243} * I109N1 =  Ideal.span {B.equivFun.symm ![-64132, 12894, -1481]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E109RS1 


noncomputable def E109RS2 : RelationCertificate Table 243 ![![109, 0, 0], ![53, 1, 0]]
  ![-57, 11, -1] ![![243, 0, 0], ![-89, 37, 1]] where
    su := ![![26487, 0, 0], ![12879, 243, 0]]
    hsu := by decide
    w := ![![-13851, 2673, -243], ![24300, -5346, 729]]
    hw := by decide
    g := ![![![94, -26, -1], ![164, 0, 0]], ![![92, -31, -1], ![200, 0, 0]]]
    h := ![![![-343565, -9209, -101], ![706576, 5504, 0]], ![![602290, 16142, 177], ![-1238670, -9645, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N2 : Ideal.span {243} * I109N2 =  Ideal.span {B.equivFun.symm ![-57, 11, -1]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E109RS2 


noncomputable def E113RS1 : RelationCertificate Table 27 ![![113, 0, 0], ![-32, 1, 0]]
  ![-2504, 160, 33] ![![27, 0, 0], ![-89, 10, 1]] where
    su := ![![3051, 0, 0], ![-864, 27, 0]]
    hsu := by decide
    w := ![![-67608, 4320, 891], ![-134163, 7209, 1620]]
    hw := by decide
    g := ![![![-62, 169, -62], ![535, 0, 0]], ![![126, -85, 26], ![-204, 0, 0]]]
    h := ![![![-611848, 19234, -7], ![-2160510, 412, 0]], ![![-1214041, 38103, -10], ![-4286927, 595, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {27} * I113N1 =  Ideal.span {B.equivFun.symm ![-2504, 160, 33]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E113RS1 


noncomputable def E127RS1 : RelationCertificate Table 81 ![![127, 0, 0], ![42, 1, 0]]
  ![-1987, 400, -46] ![![81, 0, 0], ![-89, 37, 1]] where
    su := ![![10287, 0, 0], ![3402, 81, 0]]
    hsu := by decide
    w := ![![-160947, 32400, -3726], ![1141209, -229311, 26325]]
    hw := by decide
    g := ![![![-231, -78, 4], ![250, 0, 0]], ![![-39, -56, 1], ![155, 0, 0]]]
    h := ![![![-2747149, -81952, -770], ![8306808, 48872, 0]], ![![19478443, 581018, 5457], ![-58898766, -346357, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N1 : Ideal.span {81} * I127N1 =  Ideal.span {B.equivFun.symm ![-1987, 400, -46]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E127RS1 
