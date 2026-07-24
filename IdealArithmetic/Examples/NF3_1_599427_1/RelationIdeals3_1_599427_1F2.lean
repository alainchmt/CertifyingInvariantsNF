import IdealArithmetic.Examples.NF3_1_599427_1.PrimesBelow3_1_599427_1F2
import IdealArithmetic.Examples.NF3_1_599427_1.ClassGroupData3_1_599427_1

set_option linter.all false

noncomputable section


noncomputable def E89RS1 : RelationCertificate Table 5 ![![89, 0, 0], ![24, 1, 0]]
  ![20200011914766, 3810273960761, 718721737260] ![![5, 0, 0], ![1, -1, 1]] where
    su := ![![445, 0, 0], ![120, 5, 0]]
    hsu := by decide
    w := ![![101000059573830, 19051369803805, 3593608686300], ![480841293216415, 90699800897735, 17108459691265]]
    hw := by decide
    g := ![![![-20692471, 1811689, 1118998], ![-4277029, 0, 0]], ![![-5164175, 271912, 306242], ![-1025968, 0, 0]]]
    h := ![![![121174824509166, 5479363771163, 24619592529], ![-448514973725042, -1472421997821, 0]], ![![576889355987803, 26086166412713, 117209007206], ![-2135291017677966, -7009909703081, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {5} * I89N1 =  Ideal.span {B.equivFun.symm ![20200011914766, 3810273960761, 718721737260]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E89RS1 


noncomputable def E101RS1 : RelationCertificate Table 5 ![![101, 0, 0], ![-29, 1, 0]]
  ![1449385086720992, 273393613743930, 51569502626153] ![![5, 0, 0], ![1, -1, 1]] where
    su := ![![505, 0, 0], ![-145, 5, 0]]
    hsu := by decide
    w := ![![7246925433604960, 1366968068719650, 257847513130765], ![34501177643269765, 6507864418319735, 1227560975603215]]
    hw := by decide
    g := ![![![88461087, -32456040, -1085059], ![23966419, 0, 0]], ![![-20078399, 10391602, -206484], ![-6135295, 0, 0]]]
    h := ![![![4360639584708146, -155020120739336, 781449325813], ![15137076309269026, -27356879280960, 0]], ![![20760141984164154, -738020112516723, 3720325572012], ![72064624305928469, -130240687652569, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {5} * I101N1 =  Ideal.span {B.equivFun.symm ![1449385086720992, 273393613743930, 51569502626153]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E101RS1 


noncomputable def E107RS1 : RelationCertificate Table 5 ![![107, 0, 0], ![-37, 1, 0]]
  ![-34766, 3589, 560] ![![5, 0, 0], ![1, -1, 1]] where
    su := ![![535, 0, 0], ![-185, 5, 0]]
    hsu := by decide
    w := ![![-173830, 17945, 2800], ![416555, 121795, -37795]]
    hw := by decide
    g := ![![![-176341313, -39800721, -969570], ![-27502031, 0, 0]], ![![52240769, 11790886, 287233], ![8147424, 0, 0]]]
    h := ![![![-7041418, 208028, -473], ![-20362080, 51171, 0]], ![![16840248, -497208, 1073], ![48697925, -122370, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {5} * I107N1 =  Ideal.span {B.equivFun.symm ![-34766, 3589, 560]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E107RS1 


noncomputable def E113RS1 : RelationCertificate Table 5 ![![113, 0, 0], ![-52, 1, 0]]
  ![88476, 16689, 3148] ![![5, 0, 0], ![1, -1, 1]] where
    su := ![![565, 0, 0], ![-260, 5, 0]]
    hsu := by decide
    w := ![![442380, 83445, 15740], ![2106085, 397265, 74935]]
    hw := by decide
    g := ![![![-1210, -94, 95], ![-202, 0, 0]], ![![625, 36, -48], ![112, 0, 0]]]
    h := ![![![2895692, -62343, 159], ![6290860, -14819, 0]], ![![13785537, -297007, 761], ![29948932, -71006, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {5} * I113N1 =  Ideal.span {B.equivFun.symm ![88476, 16689, 3148]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E113RS1 
