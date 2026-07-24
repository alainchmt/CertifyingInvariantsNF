import IdealArithmetic.Examples.NF3_1_344763_1.PrimesBelow3_1_344763_1F0
import IdealArithmetic.Examples.NF3_1_344763_1.ClassGroupData3_1_344763_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 1 ![![2, 0, 0], ![1, 1, 1]]
  ![1, 0, 0] ![![2, 0, 0], ![1, 1, 1]] where
    su := ![![2, 0, 0], ![1, 1, 1]]
    hsu := by decide
    w := ![![2, 0, 0], ![1, 1, 1]]
    hw := by decide
    g := ![![![0, -1, -1], ![2, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![0, -1, -1], ![2, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {1} * I2N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 2 ![![2, 0, 0], ![1, 1, 0]]
  ![-93119, -19261, -3984] ![![2, 0, 0], ![1, 1, 1]] where
    su := ![![4, 0, 0], ![2, 2, 0]]
    hsu := by decide
    w := ![![-186238, -38522, -7968], ![-2719804, -562572, -116364]]
    hw := by decide
    g := ![![![-29, 61, -17], ![9, 0, 0]], ![![-623, 116, 122], ![-191, 0, 0]]]
    h := ![![![-62080, -30974, -7815], ![31041, 11646, 0]], ![![-906602, -452331, -114128], ![453302, 170074, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {2} * I2N1 =  Ideal.span {B.equivFun.symm ![-93119, -19261, -3984]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS1 


noncomputable def E5RS0 : RelationCertificate Table 1 ![![5, 0, 0], ![-1, 2, 1]]
  ![1, 0, 0] ![![5, 0, 0], ![-1, 2, 1]] where
    su := ![![5, 0, 0], ![-1, 2, 1]]
    hsu := by decide
    w := ![![5, 0, 0], ![-1, 2, 1]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {1} * I5N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 5 ![![5, 0, 0], ![-2, 1, 0]]
  ![98208, -1860, -3817] ![![5, 0, 0], ![-1, 2, 1]] where
    su := ![![25, 0, 0], ![-10, 5, 0]]
    hsu := by decide
    w := ![![491040, -9300, -19085], ![-1171030, -233045, 98305]]
    hw := by decide
    g := ![![![-1737503122, -427819265, -106671626], ![155038594, 0, 0]], ![![-985021144, -242538282, -60474025], ![87894112, 0, 0]]]
    h := ![![![1161088, -631330, 29354], ![2853616, -150587, 0]], ![![-2707698, 1466259, -68644], ![-6652142, 362881, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {5} * I5N1 =  Ideal.span {B.equivFun.symm ![98208, -1860, -3817]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E5RS1 


noncomputable def E7RS0 : RelationCertificate Table 5 ![![7, 0, 0], ![3, 1, 0]]
  ![743, -86, -14] ![![5, 0, 0], ![-1, 2, 1]] where
    su := ![![35, 0, 0], ![15, 5, 0]]
    hsu := by decide
    w := ![![3715, -430, -70], ![-13625, -10, 585]]
    hw := by decide
    g := ![![![81741, 20126, 5018], ![-7292, 0, 0]], ![![91487, 22525, 5616], ![-8160, 0, 0]]]
    h := ![![![5114, 2191, 176], ![-11685, -1246, 0]], ![![-19222, -8239, -637], ![43943, 4576, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {5} * I7N0 =  Ideal.span {B.equivFun.symm ![743, -86, -14]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 5 ![![7, 0, 0], ![-2, 1, 0]]
  ![1595738, 330067, 68272] ![![5, 0, 0], ![-1, 2, 1]] where
    su := ![![35, 0, 0], ![-10, 5, 0]]
    hsu := by decide
    w := ![![7978690, 1650335, 341360], ![51131305, 10576145, 2187600]]
    hw := by decide
    g := ![![![-495, 272, -88], ![193, 0, 0]], ![![-633, -200, 52], ![60, 0, 0]]]
    h := ![![![17805886, -9285295, 281496], ![61522732, -1902200, 0]], ![![114108723, -59504667, 1803967], ![394267400, -12190249, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {5} * I7N1 =  Ideal.span {B.equivFun.symm ![1595738, 330067, 68272]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E7RS1 


noncomputable def E11RS0 : RelationCertificate Table 10 ![![11, 0, 0], ![4, -2, 1]]
  ![-12, 17, -3] ![![10, 0, 0], ![-1, -3, 1]] where
    su := ![![110, 0, 0], ![40, -20, 10]]
    hsu := by decide
    w := ![![-120, 170, -30], ![2950, -320, -60]]
    hw := by decide
    g := ![![![53, 9, 3], ![-7, 0, 0]], ![![86, 17, 4], ![-3, 0, 0]]]
    h := ![![![-4, 3, -1], ![8, 0, 0]], ![![21, 0, -2], ![16, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {10} * I11N0 =  Ideal.span {B.equivFun.symm ![-12, 17, -3]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 10 ![![11, 0, 0], ![2, 1, 0]]
  ![-33, 2, 1] ![![10, 0, 0], ![-1, -3, 1]] where
    su := ![![110, 0, 0], ![20, 10, 0]]
    hsu := by decide
    w := ![![-330, 20, 10], ![-80, 210, -40]]
    hw := by decide
    g := ![![![86, 17, 4], ![-3, 0, 0]], ![![53, 9, 3], ![-7, 0, 0]]]
    h := ![![![-513, -265, -5], ![2805, 56, 0]], ![![-112, -57, -2], ![612, 18, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {10} * I11N1 =  Ideal.span {B.equivFun.symm ![-33, 2, 1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E11RS1 


noncomputable def E17RS1 : RelationCertificate Table 10 ![![17, 0, 0], ![5, 1, 0]]
  ![-9326, -1929, -399] ![![10, 0, 0], ![-1, -3, 1]] where
    su := ![![170, 0, 0], ![50, 10, 0]]
    hsu := by decide
    w := ![![-93260, -19290, -3990], ![-73390, -15180, -3140]]
    hw := by decide
    g := ![![![-144, 18, 2], ![13, 0, 0]], ![![-20, -2, 1], ![8, 0, 0]]]
    h := ![![![-15518, -3405, -83], ![50896, 1012, 0]], ![![-12212, -2678, -65], ![40053, 791, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {10} * I17N1 =  Ideal.span {B.equivFun.symm ![-9326, -1929, -399]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E17RS1 


noncomputable def E19RS0 : RelationCertificate Table 2 ![![19, 0, 0], ![1, 1, 0]]
  ![-3284595, -679395, -140528] ![![2, 0, 0], ![1, 1, 1]] where
    su := ![![38, 0, 0], ![2, 2, 0]]
    hsu := by decide
    w := ![![-6569190, -1358790, -281056], ![-95935894, -19843654, -4104518]]
    hw := by decide
    g := ![![![4140, -1771, -420], ![975, 0, 0]], ![![536, 67, -173], ![218, 0, 0]]]
    h := ![![![-171921, -171921, -144512], ![-18096, 2605200, 0]], ![![-2510719, -2510719, -2110441], ![-264286, 38046120, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N0 : Ideal.span {2} * I19N0 =  Ideal.span {B.equivFun.symm ![-3284595, -679395, -140528]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E19RS0 


noncomputable def E19RS1 : RelationCertificate Table 2 ![![19, 0, 0], ![7, 1, 0]]
  ![24, 5, 1] ![![2, 0, 0], ![1, 1, 1]] where
    su := ![![38, 0, 0], ![14, 2, 0]]
    hsu := by decide
    w := ![![48, 10, 2], ![702, 142, 30]]
    hw := by decide
    g := ![![![5, -4, 0], ![1, 0, 0]], ![![4, -2, -1], ![2, 0, 0]]]
    h := ![![![156, 22, 0], ![-420, 1, 0]], ![![2453, 416, 10], ![-6608, -175, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {2} * I19N1 =  Ideal.span {B.equivFun.symm ![24, 5, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E19RS1 


noncomputable def E23RS1 : RelationCertificate Table 10 ![![23, 0, 0], ![-7, 1, 0]]
  ![-7, 1, 0] ![![10, 0, 0], ![-1, -3, 1]] where
    su := ![![230, 0, 0], ![-70, 10, 0]]
    hsu := by decide
    w := ![![-70, 10, 0], ![120, 20, -10]]
    hw := by decide
    g := ![![![-4, 2, -1], ![9, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    h := ![![![-21, 10, -1], ![-68, 23, 0]], ![![62, -9, 0], ![202, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {10} * I23N1 =  Ideal.span {B.equivFun.symm ![-7, 1, 0]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E23RS1 


noncomputable def E29RS1 : RelationCertificate Table 10 ![![29, 0, 0], ![-11, 1, 0]]
  ![117, 24, 5] ![![10, 0, 0], ![-1, -3, 1]] where
    su := ![![290, 0, 0], ![-110, 10, 0]]
    hsu := by decide
    w := ![![1170, 240, 50], ![900, 190, 40]]
    hw := by decide
    g := ![![![13, 2, -1], ![1, 0, 0]], ![![-8, 1, 0], ![4, 0, 0]]]
    h := ![![![529, -45, 0], ![1384, 5, 0]], ![![412, -35, 0], ![1078, 4, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {10} * I29N1 =  Ideal.span {B.equivFun.symm ![117, 24, 5]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E29RS1 
