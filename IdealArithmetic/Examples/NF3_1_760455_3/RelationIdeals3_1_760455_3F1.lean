import IdealArithmetic.Examples.NF3_1_760455_3.PrimesBelow3_1_760455_3F1
import IdealArithmetic.Examples.NF3_1_760455_3.ClassGroupData3_1_760455_3

set_option linter.all false

noncomputable section


noncomputable def E37RS1 : RelationCertificate Table 25 ![![37, 0, 0], ![9, 1, 0]]
  ![4496, -3893, 2814] ![![25, 0, 0], ![8, 1, 0]] where
    su := ![![925, 0, 0], ![225, 25, 0]]
    hsu := by decide
    w := ![![112400, -97325, 70350], ![132300, -107175, -1925]]
    hw := by decide
    g := ![![![13492841, -156788, 493780], ![4311464, 2697, 0]], ![![3731498, -43348, 136570], ![1192372, 699, 0]]]
    h := ![![![53082, 229827, 201719], ![19124, -1065827, 0]], ![![62376, 270079, 236950], ![22478, -1252461, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {25} * I37N1 =  Ideal.span {B.equivFun.symm ![4496, -3893, 2814]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E37RS1 


noncomputable def E41RS1 : RelationCertificate Table 5 ![![41, 0, 0], ![12, 1, 0]]
  ![-7, 6, -3] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![205, 0, 0], ![60, 5, 0]]
    hsu := by decide
    w := ![![-35, 30, -15], ![-85, 65, 45]]
    hw := by decide
    g := ![![![412, 172, -323], ![-125, 244, 0]], ![![133, 56, -106], ![-39, 80, 0]]]
    h := ![![![73, 466, 297], ![40, -1740, 0]], ![![171, 1127, 719], ![116, -4210, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {5} * I41N1 =  Ideal.span {B.equivFun.symm ![-7, 6, -3]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E41RS1 


noncomputable def E43RS0 : RelationCertificate Table 25 ![![43, 0, 0], ![-19, 1, 0]]
  ![-127082206, -140352, -4225629] ![![25, 0, 0], ![8, 1, 0]] where
    su := ![![1075, 0, 0], ![-475, 25, 0]]
    hsu := by decide
    w := ![![-3177055150, -3508800, -105640725], ![-1173286625, -1295800, -39013125]]
    hw := by decide
    g := ![![![-873635, -3511220, -3528142], ![-419987, 12600154, 0]], ![![348253, 1400063, 1406749], ![167458, -5023942, 0]]]
    h := ![![![676423936, -9030583082, 3164746863], ![-508898506, -19441191534, 0]], ![![249803401, -3334994782, 1168741174], ![-187936226, -7179633001, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N0 : Ideal.span {25} * I43N0 =  Ideal.span {B.equivFun.symm ![-127082206, -140352, -4225629]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E43RS0 


noncomputable def E43RS1 : RelationCertificate Table 25 ![![43, 0, 0], ![-5, 1, 0]]
  ![-495291, -547, -16469] ![![25, 0, 0], ![8, 1, 0]] where
    su := ![![1075, 0, 0], ![-125, 25, 0]]
    hsu := by decide
    w := ![![-12382275, -13675, -411725], ![-4572775, -5050, -152050]]
    hw := by decide
    g := ![![![-68159913910, -273950423242, -275261190814], ![-32769189367, 983075681462, 0]], ![![8718127408, 35040165977, 35207822269], ![4191407431, -125742222392, 0]]]
    h := ![![![5354078, -16423852, 19188017], ![-1004511, -117871600, 0]], ![![1977263, -6065330, 7086136], ![-370952, -43529990, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {25} * I43N1 =  Ideal.span {B.equivFun.symm ![-495291, -547, -16469]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E43RS1 


noncomputable def E59RS1 : RelationCertificate Table 25 ![![59, 0, 0], ![21, 1, 0]]
  ![-28, -1, -2] ![![25, 0, 0], ![8, 1, 0]] where
    su := ![![1475, 0, 0], ![525, 25, 0]]
    hsu := by decide
    w := ![![-700, -25, -50], ![-300, 25, -25]]
    hw := by decide
    g := ![![![-9075, -36449, -36623], ![-4346, 130796, 0]], ![![-3158, -12668, -12728], ![-1498, 45457, 0]]]
    h := ![![![-589, -6824, -2390], ![-265, 20144, 0]], ![![-247, -2932, -1027], ![-131, 8656, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {25} * I59N1 =  Ideal.span {B.equivFun.symm ![-28, -1, -2]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E59RS1 


noncomputable def E61RS1 : RelationCertificate Table 25 ![![61, 0, 0], ![-22, 1, 0]]
  ![-78, -1, -2] ![![25, 0, 0], ![8, 1, 0]] where
    su := ![![1525, 0, 0], ![-550, 25, 0]]
    hsu := by decide
    w := ![![-1950, -25, -50], ![-700, -25, -25]]
    hw := by decide
    g := ![![![-44147, -177432, -178281], ![-21223, 636718, 0]], ![![15957, 64162, 64470], ![7698, -230250, 0]]]
    h := ![![![-115068, 1603388, -488326], ![67807, 4255412, 0]], ![![-41280, 575209, -175185], ![24326, 1526612, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {25} * I61N1 =  Ideal.span {B.equivFun.symm ![-78, -1, -2]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E61RS1 


noncomputable def E73RS1 : RelationCertificate Table 5 ![![73, 0, 0], ![16, 1, 0]]
  ![-156, 123, 41] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![365, 0, 0], ![80, 5, 0]]
    hsu := by decide
    w := ![![-780, 615, 205], ![2075, -1755, 820]]
    hw := by decide
    g := ![![![-179997, -14422, -6053], ![69120, -614, 0]], ![![-42491, -3403, -1433], ![16318, -142, 0]]]
    h := ![![![390, 3153, 1472], ![129, -15345, 0]], ![![-1043, -8403, -3919], ![-327, 40893, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {5} * I73N1 =  Ideal.span {B.equivFun.symm ![-156, 123, 41]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E73RS1 


noncomputable def E79RS1 : RelationCertificate Table 25 ![![79, 0, 0], ![-21, 1, 0]]
  ![277043, 306, 9212] ![![25, 0, 0], ![8, 1, 0]] where
    su := ![![1975, 0, 0], ![-525, 25, 0]]
    hsu := by decide
    w := ![![6926075, 7650, 230300], ![2557800, 2825, 85050]]
    hw := by decide
    g := ![![![5004013, 20112222, 20208468], ![2405780, -72173092, 0]], ![![-1314331, -5282555, -5307834], ![-631862, 18956544, 0]]]
    h := ![![![-3592297, 43953828, -13991278], ![1511298, 157902882, 0]], ![![-1326616, 16232151, -5166980], ![558196, 58313546, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {25} * I79N1 =  Ideal.span {B.equivFun.symm ![277043, 306, 9212]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E79RS1 
