import IdealArithmetic.Examples.NF3_1_925444_2.PrimesBelow3_1_925444_2F2
import IdealArithmetic.Examples.NF3_1_925444_2.ClassGroupData3_1_925444_2

set_option linter.all false

noncomputable section


noncomputable def E83RS1 : RelationCertificate Table 12 ![![83, 0, 0], ![-12, 1, 0]]
  ![-48006372, -11290916, -3363511] ![![12, 0, 0], ![-3, 1, 0]] where
    su := ![![996, 0, 0], ![-144, 12, 0]]
    hsu := by decide
    w := ![![-576076464, -135490992, -40362132], ![-613733604, -144347808, -43000536]]
    hw := by decide
    g := ![![![-17018, -1159, 573], ![4159, 340, 0]], ![![588811892, 319523782, -1547378288], ![-120575980, 3713707501, 0]]]
    h := ![![![-82960088968, -419894685531, 209905455563], ![6935257677, -3484431235048, 0]], ![![-88383049085, -447342487943, 223626618674], ![7388603645, -3712202586664, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {12} * I83N1 =  Ideal.span {B.equivFun.symm ![-48006372, -11290916, -3363511]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E83RS1 


noncomputable def E107RS1 : RelationCertificate Table 3 ![![107, 0, 0], ![-32, 1, 0]]
  ![55748253, -477682, -1097744] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![321, 0, 0], ![-96, 3, 0]]
    hsu := by decide
    w := ![![167244759, -1433046, -3293232], ![-253721244, 19665081, -1290666]]
    hw := by decide
    g := ![![![35211936083727, 7453541946823, 2467083441924], ![2484513982277, 107744, 0]], ![![-5336280197664, -1129565491554, -373880253436], ![-376521830515, -31746, 0]]]
    h := ![![![2883062415, 45214525410, -7535080412], ![-439658512, 161250501268, 0]], ![![-4403915454, -69065804343, 11509927499], ![671584038, -246312534523, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {3} * I107N1 =  Ideal.span {B.equivFun.symm ![55748253, -477682, -1097744]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E107RS1 


noncomputable def E127RS1 : RelationCertificate Table 2 ![![127, 0, 0], ![5, 1, 0]]
  ![-224638, -52834, -15739] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![254, 0, 0], ![10, 2, 0]]
    hsu := by decide
    w := ![![-449276, -105668, -31478], ![-3770418, -886788, -264170]]
    hw := by decide
    g := ![![![6514, -899, -362], ![2809, 0, 0]], ![![-295, 54, 1], ![-119, 3, 0]]]
    h := ![![![1254749, -4400387, -3142877], ![14819, 79825928, 0]], ![![10530138, -36928962, -26375680], ![123795, 669915855, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N1 : Ideal.span {2} * I127N1 =  Ideal.span {B.equivFun.symm ![-224638, -52834, -15739]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E127RS1 


noncomputable def E131RS1 : RelationCertificate Table 12 ![![131, 0, 0], ![15, 1, 0]]
  ![-324, 40, -7] ![![12, 0, 0], ![-3, 1, 0]] where
    su := ![![1572, 0, 0], ![180, 12, 0]]
    hsu := by decide
    w := ![![-3888, 480, -84], ![-732, -588, 228]]
    hw := by decide
    g := ![![![-31172346, -16915923, 81919234], ![6383431, -196606245, 0]], ![![-3331455, -1807826, 8754726], ![682221, -21011362, 0]]]
    h := ![![![271056, -2317192, -681497], ![13452, 17855220, 0]], ![![49687, -424751, -124921], ![2454, 3272934, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {12} * I131N1 =  Ideal.span {B.equivFun.symm ![-324, 40, -7]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E131RS1 
