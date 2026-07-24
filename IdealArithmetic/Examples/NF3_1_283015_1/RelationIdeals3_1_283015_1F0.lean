import IdealArithmetic.Examples.NF3_1_283015_1.PrimesBelow3_1_283015_1F0
import IdealArithmetic.Examples.NF3_1_283015_1.ClassGroupData3_1_283015_1

set_option linter.all false

noncomputable section


noncomputable def E3RS0 : RelationCertificate Table 1 ![![3, 0, 0], ![0, 1, 0]]
  ![1, 0, 0] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![3, 0, 0], ![0, 1, 0]]
    hsu := by decide
    w := ![![3, 0, 0], ![0, 1, 0]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {1} * I3N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 3 ![![3, 0, 0], ![-1, 1, 0]]
  ![63, 15, 7] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![9, 0, 0], ![-3, 3, 0]]
    hsu := by decide
    w := ![![189, 45, 21], ![-693, 36, 135]]
    hw := by decide
    g := ![![![-7767, 445, -591], ![149, 0, 0]], ![![22092, -1267, 1681], ![-420, 0, 0]]]
    h := ![![![-191, -28, 0], ![57, 0, -7]], ![![-1427, -221, 0], ![405, 0, -45]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {3} * I3N1 =  Ideal.span {B.equivFun.symm ![63, 15, 7]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E3RS1 


noncomputable def E7RS1 : RelationCertificate Table 3 ![![7, 0, 0], ![-3, 1, 0]]
  ![147, -99, -125] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![21, 0, 0], ![-9, 3, 0]]
    hsu := by decide
    w := ![![441, -297, -375], ![12375, 798, -891]]
    hw := by decide
    g := ![![![-823395, 47196, -62653], ![15734, 0, 0]], ![![1238976, -71018, 94275], ![-23671, 0, 0]]]
    h := ![![![1416, -492, 40], ![3255, -45, 0]], ![![38184, -12833, 1485], ![87721, -1188, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {3} * I7N1 =  Ideal.span {B.equivFun.symm ![147, -99, -125]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E7RS1 


noncomputable def E7RS2 : RelationCertificate Table 3 ![![7, 0, 0], ![-1, 1, 0]]
  ![-709947694, 45215395, -54020674] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![21, 0, 0], ![-3, 3, 0]]
    hsu := by decide
    w := ![![-2129843082, 135646185, -162062022], ![5348046726, -340608255, 406938555]]
    hw := by decide
    g := ![![![-3110, 2371, 3215], ![793, 0, 0]], ![![-45025, -2880, 2929], ![-960, 0, 0]]]
    h := ![![![-99305796, 4344039, -216082696], ![14807122, 162062022, 0]], ![![249357356, -10907905, 542584740], ![-37180750, -406938555, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N2 : Ideal.span {3} * I7N2 =  Ideal.span {B.equivFun.symm ![-709947694, 45215395, -54020674]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E7RS2 


noncomputable def E11RS1 : RelationCertificate Table 3 ![![11, 0, 0], ![3, 1, 0]]
  ![-644, 41, -49] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![33, 0, 0], ![9, 3, 0]]
    hsu := by decide
    w := ![![-1932, 123, -147], ![4851, -309, 369]]
    hw := by decide
    g := ![![![-11, 2, 4], ![1, 0, 0]], ![![-39, -3, 3], ![2, 0, 0]]]
    h := ![![![-628, -205, -47], ![2088, 52, 0]], ![![1557, 501, 102], ![-5170, -111, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {3} * I11N1 =  Ideal.span {B.equivFun.symm ![-644, 41, -49]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E11RS1 


noncomputable def E11RS2 : RelationCertificate Table 3 ![![11, 0, 0], ![-4, 1, 0]]
  ![-23, -4, -1] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![33, 0, 0], ![-12, 3, 0]]
    hsu := by decide
    w := ![![-69, -12, -3], ![99, -21, -36]]
    hw := by decide
    g := ![![![-539, 30, -41], ![13, 0, 0]], ![![565, -33, 43], ![-9, 0, 0]]]
    h := ![![![-33, 9, -5], ![-85, 6, 0]], ![![63, -14, -6], ![165, 6, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N2 : Ideal.span {3} * I11N2 =  Ideal.span {B.equivFun.symm ![-23, -4, -1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E11RS2 


noncomputable def E17RS0 : RelationCertificate Table 3 ![![17, 0, 0], ![4, 1, 0]]
  ![-2549603, 162380, -194002] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![51, 0, 0], ![12, 3, 0]]
    hsu := by decide
    w := ![![-7648809, 487140, -582006], ![19206198, -1223211, 1461420]]
    hw := by decide
    g := ![![![313, 271, 274], ![91, 0, 0]], ![![-1522, 9, 224], ![4, 0, 0]]]
    h := ![![![-26537383, -7032741, -813206], ![112146477, 1514500, 0]], ![![66635482, 17659230, 2041941], ![-281600282, -3802873, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N0 : Ideal.span {3} * I17N0 =  Ideal.span {B.equivFun.symm ![-2549603, 162380, -194002]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E17RS0 


noncomputable def E17RS2 : RelationCertificate Table 3 ![![17, 0, 0], ![-2, 1, 0]]
  ![-148210388287, 9439274620, -11277485844] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![51, 0, 0], ![-6, 3, 0]]
    hsu := by decide
    w := ![![-444631164861, 28317823860, -33832457532], ![1116471098556, -71106198603, 84953471580]]
    hw := by decide
    g := ![![![381217, -18074, -74556], ![-6022, 0, 0]], ![![389330, 44927, -1860], ![14978, 0, 0]]]
    h := ![![![-9074105405, -69568141441, 632048467200], ![-3024701799, -1195122380916, 0]], ![![22785124462, 174685954195, -1587076890429], ![7595041501, 3000958329017, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N2 : Ideal.span {3} * I17N2 =  Ideal.span {B.equivFun.symm ![-148210388287, 9439274620, -11277485844]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E17RS2 


noncomputable def E31RS1 : RelationCertificate Table 3 ![![31, 0, 0], ![-6, 1, 0]]
  ![13, -1, 1] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![93, 0, 0], ![-18, 3, 0]]
    hsu := by decide
    w := ![![39, -3, 3], ![-99, 6, -9]]
    hw := by decide
    g := ![![![-1, 0, 1], ![2, 0, 0]], ![![-3, -1, 0], ![2, 0, 0]]]
    h := ![![![235, -38, -2], ![1212, 7, 0]], ![![-591, 105, -12], ![-3048, 41, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {3} * I31N1 =  Ideal.span {B.equivFun.symm ![13, -1, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E31RS1 
