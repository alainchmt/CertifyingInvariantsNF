import IdealArithmetic.Examples.NF3_1_138580_1.PrimesBelow3_1_138580_1F0
import IdealArithmetic.Examples.NF3_1_138580_1.ClassGroupData3_1_138580_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 2 ![![2, 0, 0], ![0, 1, 0]]
  ![-5040650418302, -495320703465, -401620329225] ![![2, 0, 0], ![3, 0, 1]] where
    su := ![![4, 0, 0], ![0, 2, 0]]
    hsu := by decide
    w := ![![-10081300836604, -990641406930, -803240658450], ![-64440133098036, -6332224893360, -5134350792542]]
    hw := by decide
    g := ![![![-11104, -221991, 110521], ![38605, 3, 0]], ![![1671123, -125198, -1305934], ![1853723, 0, 0]]]
    h := ![![![9932319691047, -1681441616292, -4011373903804], ![3266768164121, 2005686951902, -401620329225]], ![![63487838845102, -10747851225412, -25640884292290], ![20881330565205, 12820442146145, -2567175396271]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {2} * I2N0 =  Ideal.span {B.equivFun.symm ![-5040650418302, -495320703465, -401620329225]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 1 ![![2, 0, 0], ![3, 0, 1]]
  ![1, 0, 0] ![![2, 0, 0], ![3, 0, 1]] where
    su := ![![2, 0, 0], ![3, 0, 1]]
    hsu := by decide
    w := ![![2, 0, 0], ![3, 0, 1]]
    hw := by decide
    g := ![![![-2, 0, -1], ![2, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![-2, 0, -1], ![2, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {1} * I2N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS1 


noncomputable def E3RS0 : RelationCertificate Table 2 ![![3, 0, 0], ![4, 1, 1]]
  ![-1098440, 312337, -77138] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![6, 0, 0], ![8, 2, 2]]
    hsu := by decide
    w := ![![-2196880, 624674, -154276], ![-6027702, -789888, 1095072]]
    hw := by decide
    g := ![![![-480375421198, 49850596178, -46850187120], ![-215262412509, 0, 0]], ![![-3157237722279, 327639957806, -307919954985], ![-1414798882236, 0, 0]]]
    h := ![![![-160788, 155452, 25627], ![-154019, 0, 0]], ![![-416825, 15300, 329460], ![-440844, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {2} * I3N0 =  Ideal.span {B.equivFun.symm ![-1098440, 312337, -77138]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 2 ![![3, 0, 0], ![1, 1, 0]]
  ![-8, 3, -1] ![![2, 0, 0], ![3, 0, 1]] where
    su := ![![6, 0, 0], ![2, 2, 0]]
    hsu := by decide
    w := ![![-16, 6, -2], ![158, -20, -4]]
    hw := by decide
    g := ![![![-253, 19, 148], ![-305, 22, 0]], ![![-77, 24, 53], ![-87, 11, 0]]]
    h := ![![![30, -3, 73], ![12, -55, 0]], ![![-246, 21, -594], ![-73, 445, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {2} * I3N1 =  Ideal.span {B.equivFun.symm ![-8, 3, -1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E3RS1 


noncomputable def E7RS0 : RelationCertificate Table 2 ![![7, 0, 0], ![3, 2, 1]]
  ![-1088693512, -106980725, -86743061] ![![2, 0, 0], ![3, 0, 1]] where
    su := ![![14, 0, 0], ![6, 4, 2]]
    hsu := by decide
    w := ![![-2177387024, -213961450, -173486122], ![-13917956810, -1367651312, -1108931176]]
    hw := by decide
    g := ![![![-6160, 1333, 4255], ![-7107, 54, 0]], ![![9131, -3860, -5764], ![10817, 27, 0]]]
    h := ![![![-131263801, 892935, -4303918], ![-56615635, 0, 0]], ![![-839044180, 5707682, -27510839], ![-361889715, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {2} * I7N0 =  Ideal.span {B.equivFun.symm ![-1088693512, -106980725, -86743061]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 2 ![![7, 0, 0], ![-2, 1, 0]]
  ![13718, 1348, 1093] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![14, 0, 0], ![-4, 2, 0]]
    hsu := by decide
    w := ![![27436, 2696, 2186], ![95110, 9346, 7578]]
    hw := by decide
    g := ![![![-28, 31, -17], ![3, 0, 0]], ![![-131, 19, 21], ![-54, 0, 0]]]
    h := ![![![31520, -48707, 68395], ![-15957, -119418, 0]], ![![109263, -168846, 237099], ![-55333, -413976, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {2} * I7N1 =  Ideal.span {B.equivFun.symm ![13718, 1348, 1093]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E7RS1 


noncomputable def E11RS0 : RelationCertificate Table 2 ![![11, 0, 0], ![0, 1, 0]]
  ![-75744, -7443, -6035] ![![2, 0, 0], ![3, 0, 1]] where
    su := ![![22, 0, 0], ![0, 2, 0]]
    hsu := by decide
    w := ![![-151488, -14886, -12070], ![-968318, -95152, -77152]]
    hw := by decide
    g := ![![![-1232, 47, 729], ![-1477, 86, 0]], ![![-473, -23, 268], ![-570, 43, 0]]]
    h := ![![![227232, -116771, 467687], ![-10610, -1287648, 0]], ![![1452477, -746403, 2989476], ![-67846, -8230703, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {2} * I11N0 =  Ideal.span {B.equivFun.symm ![-75744, -7443, -6035]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 2 ![![11, 0, 0], ![3, 1, 0]]
  ![-4, -1, 1] ![![2, 0, 0], ![3, 0, 1]] where
    su := ![![22, 0, 0], ![6, 2, 0]]
    hsu := by decide
    w := ![![-8, -2, 2], ![-50, 18, -6]]
    hw := by decide
    g := ![![![-5496, 212, 3121], ![-6677, 430, 0]], ![![-1656, 62, 938], ![-2009, 129, 0]]]
    h := ![![![4, 5, 11], ![4, -30, 0]], ![![33, 39, 79], ![16, -218, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {2} * I11N1 =  Ideal.span {B.equivFun.symm ![-4, -1, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E11RS1 


noncomputable def E11RS2 : RelationCertificate Table 2 ![![11, 0, 0], ![-3, 1, 0]]
  ![-4155280964, -408319665, -331077375] ![![2, 0, 0], ![3, 0, 1]] where
    su := ![![22, 0, 0], ![-6, 2, 0]]
    hsu := by decide
    w := ![![-8310561928, -816639330, -662154750], ![-53121489522, -5219995710, -4232523254]]
    hw := by decide
    g := ![![![17657, -17749, -6795], ![23093, 172, 0]], ![![6579, 10022, -9823], ![4959, -43, 0]]]
    h := ![![![-14204377240, 30643252187, -31315894761], ![6659671274, 86035941249, 0]], ![![-90795024858, 195873060584, -200172622481], ![42568921385, 549945646416, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N2 : Ideal.span {2} * I11N2 =  Ideal.span {B.equivFun.symm ![-4155280964, -408319665, -331077375]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E11RS2 


noncomputable def E13RS0 : RelationCertificate Table 2 ![![13, 0, 0], ![0, 1, 0]]
  ![-440, 89, -9] ![![2, 0, 0], ![3, 0, 1]] where
    su := ![![26, 0, 0], ![0, 2, 0]]
    hsu := by decide
    w := ![![-880, 178, -18], ![4782, -242, -342]]
    hw := by decide
    g := ![![![29518, 8103, -12382], ![38089, -102, 0]], ![![13527, 3696, -5684], ![17454, -51, 0]]]
    h := ![![![1320, -667, 2707], ![-40, -8800, 0]], ![![-7173, 3647, -14727], ![288, 47820, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {2} * I13N0 =  Ideal.span {B.equivFun.symm ![-440, 89, -9]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E13RS0 


noncomputable def E17RS0 : RelationCertificate Table 2 ![![17, 0, 0], ![5, 1, 0]]
  ![722, -186, 39] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![34, 0, 0], ![10, 2, 0]]
    hsu := by decide
    w := ![![1444, -372, 78], ![3158, 566, -666]]
    hw := by decide
    g := ![![![-521911, 54160, -50901], ![-233873, 0, 0]], ![![-335657, 34832, -32736], ![-150411, 0, 0]]]
    h := ![![![-15854, -35370, -35753], ![-6736, 151960, 0]], ![![-32578, -72658, -73509], ![-13851, 312330, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N0 : Ideal.span {2} * I17N0 =  Ideal.span {B.equivFun.symm ![722, -186, 39]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E17RS0 


noncomputable def E17RS1 : RelationCertificate Table 2 ![![17, 0, 0], ![-4, 1, 0]]
  ![517996, 50901, 41272] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![34, 0, 0], ![-8, 2, 0]]
    hsu := by decide
    w := ![![1035992, 101802, 82544], ![3591382, 352908, 286148]]
    hw := by decide
    g := ![![![-318, -124, 186], ![-221, 0, 0]], ![![717, -144, -88], ![288, 0, 0]]]
    h := ![![![-841368, 2360924, -1899768], ![336853, 8084332, 0]], ![![-2916697, 8184407, -6585758], ![1167735, 28025240, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {2} * I17N1 =  Ideal.span {B.equivFun.symm ![517996, 50901, 41272]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E17RS1 


noncomputable def E17RS2 : RelationCertificate Table 2 ![![17, 0, 0], ![-1, 1, 0]]
  ![-2, 2, -1] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![34, 0, 0], ![-2, 2, 0]]
    hsu := by decide
    w := ![![-4, 4, -2], ![-70, 2, 6]]
    hw := by decide
    g := ![![![71, -8, 7], ![33, 0, 0]], ![![20, -3, 2], ![11, 0, 0]]]
    h := ![![![4, -4, 7], ![10, -30, 0]], ![![-12, 10, -21], ![11, 90, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N2 : Ideal.span {2} * I17N2 =  Ideal.span {B.equivFun.symm ![-2, 2, -1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E17RS2 


noncomputable def E29RS1 : RelationCertificate Table 2 ![![29, 0, 0], ![6, 1, 0]]
  ![3892, -1027, 225] ![![2, 0, 0], ![3, 0, 1]] where
    su := ![![58, 0, 0], ![12, 2, 0]]
    hsu := by decide
    w := ![![7784, -2054, 450], ![-54618, 4852, 2640]]
    hw := by decide
    g := ![![![-3284407, -950975, 1354114], ![-4249551, -460, 0]], ![![-1352451, -391280, 557743], ![-1749800, -115, 0]]]
    h := ![![![-7858, -21148, -16947], ![-2345, 122922, 0]], ![![53259, 143296, 115056], ![15972, -833826, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {2} * I29N1 =  Ideal.span {B.equivFun.symm ![3892, -1027, 225]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E29RS1 
