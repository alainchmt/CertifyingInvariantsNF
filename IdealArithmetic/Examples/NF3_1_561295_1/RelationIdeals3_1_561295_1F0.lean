import IdealArithmetic.Examples.NF3_1_561295_1.PrimesBelow3_1_561295_1F0
import IdealArithmetic.Examples.NF3_1_561295_1.ClassGroupData3_1_561295_1

set_option linter.all false

noncomputable section


noncomputable def E3RS0 : RelationCertificate Table 1 ![![3, 0, 0], ![1, 1, 0]]
  ![1, 0, 0] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![3, 0, 0], ![1, 1, 0]]
    hsu := by decide
    w := ![![3, 0, 0], ![1, 1, 0]]
    hw := by decide
    g := ![![![70, 13, -5], ![30, 0, 3]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![70, 13, -5], ![30, 0, 3]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {1} * I3N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 177147 ![![3, 0, 0], ![-1, 1, 0]]
  ![402052, -14140, 17217] ![![177147, 0, 0], ![-40124, 1, 0]] where
    su := ![![531441, 0, 0], ![-177147, 177147, 0]]
    hsu := by decide
    w := ![![71222305644, -2504858580, 3049939899], ![-16133308731, 567401841, -690873300]]
    hw := by decide
    g := ![![![108202, -3654061948, 819565], ![75671, -16131435488, 14]], ![![-56030, 2609823228, -585354], ![39775, 11521478192, -10]]]
    h := ![![![121406, 7898, 5739], ![-37834, 0, 0]], ![![-27500, -1790, -1300], ![8573, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {177147} * I3N1 =  Ideal.span {B.equivFun.symm ![402052, -14140, 17217]} * (J0 ^ 11) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_11 E3RS1 


noncomputable def E5RS0 : RelationCertificate Table 9 ![![5, 0, 0], ![0, 1, 0]]
  ![-5, -1, 0] ![![9, 0, 0], ![-2, 1, 0]] where
    su := ![![45, 0, 0], ![0, 9, 0]]
    hsu := by decide
    w := ![![-45, -9, 0], ![9, 0, -9]]
    hw := by decide
    g := ![![![-1485, -481, 39], ![282, 0, -176]], ![![-32, -11, 1], ![6, 0, -4]]]
    h := ![![![0, -4, 9], ![4, -5, 0]], ![![0, 0, -2], ![3, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {9} * I5N0 =  Ideal.span {B.equivFun.symm ![-5, -1, 0]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 243 ![![5, 0, 0], ![2, 1, 0]]
  ![1066, -37, 45] ![![243, 0, 0], ![-29, 1, 0]] where
    su := ![![1215, 0, 0], ![486, 243, 0]]
    hsu := by decide
    w := ![![259038, -8991, 10935], ![-34506, 1215, -1458]]
    hw := by decide
    g := ![![![1413731932, -46614493788, 13110747924], ![-360546017, -353990102840, 32799]], ![![4241208734, -139843909022, 39332364055], ![-1081641628, -1061973556160, 98397]]]
    h := ![![![-732910, 811618, -7069113], ![-130837, 3927290, 0]], ![![97644, -108133, 941820], ![17436, -523234, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {243} * I5N1 =  Ideal.span {B.equivFun.symm ![1066, -37, 45]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E5RS1 


noncomputable def E7RS0 : RelationCertificate Table 6561 ![![7, 0, 0], ![2, 1, 0]]
  ![-451, 25, 9] ![![6561, 0, 0], ![-758, 1, 0]] where
    su := ![![45927, 0, 0], ![13122, 6561, 0]]
    hsu := by decide
    w := ![![-2959011, 164025, 59049], ![341172, -19683, -6561]]
    hw := by decide
    g := ![![![87772706653559397, -68605908209342849593, 811370830665743418], ![-20597107125855926, -591489335556642839392, -15706882]], ![![27717696852338897, -21665023656289443689, 256222367711512935], ![-6504349622059531, -186786106062108473090, -4960068]]]
    h := ![![![694, -793, 7056], ![89, -5487, 0]], ![![-81, 91, -814], ![-7, 633, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {6561} * I7N0 =  Ideal.span {B.equivFun.symm ![-451, 25, 9]} * (J0 ^ 8) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8 E7RS0 


noncomputable def E11RS0 : RelationCertificate Table 3 ![![11, 0, 0], ![0, 1, 0]]
  ![-140, 5, -6] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![33, 0, 0], ![0, 3, 0]]
    hsu := by decide
    w := ![![-420, 15, -18], ![339, -12, 15]]
    hw := by decide
    g := ![![![45553, 8968, -3267], ![18174, 0, 1960]], ![![2279, 448, -164], ![912, 0, 98]]]
    h := ![![![0, -38, 114], ![3, -140, 0]], ![![0, 30, -92], ![5, 113, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {3} * I11N0 =  Ideal.span {B.equivFun.symm ![-140, 5, -6]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 177147 ![![11, 0, 0], ![18, 2, 1]]
  ![26990, -1307, 1629] ![![177147, 0, 0], ![-40124, 1, 0]] where
    su := ![![1948617, 0, 0], ![3188646, 354294, 177147]]
    hsu := by decide
    w := ![![4781197530, -231531129, 288572463], ![-1083076758, 52435512, -65367243]]
    hw := by decide
    g := ![![![258085655753928, -11476315893898332841, 2573998630631388], ![-123240838073891, -50664015046717890843, -63]], ![![421953425288693, -18763037359155730046, 4208321983767474], ![-201490832840184, -82832401606495649894, -103]]]
    h := ![![![688, -315, 50], ![1079, 0, 0]], ![![-168, 70, -12], ![-237, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {177147} * I11N1 =  Ideal.span {B.equivFun.symm ![26990, -1307, 1629]} * (J0 ^ 11) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_11 E11RS1 


noncomputable def E13RS0 : RelationCertificate Table 19683 ![![13, 0, 0], ![0, 1, 0]]
  ![5665, -154, 207] ![![19683, 0, 0], ![-758, 1, 0]] where
    su := ![![255879, 0, 0], ![0, 19683, 0]]
    hsu := by decide
    w := ![![111504195, -3031182, 4074381], ![-4310577, 118098, -157464]]
    hw := by decide
    g := ![![![1242694626308086023, -948505360630589325838, 11217540459365812271], ![-96045719014989248, -24532760984674897794539, -499731062]], ![![-45813626893934033, 34967939652177385932, -413549879747840092], ![3540856009644765, 904433587010069741405, 18423265]]]
    h := ![![![0, 1287, -3906], ![110, 5665, 0]], ![![0, -50, 151], ![-1, -219, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {19683} * I13N0 =  Ideal.span {B.equivFun.symm ![5665, -154, 207]} * (J0 ^ 9) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_9 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 27 ![![13, 0, 0], ![13, 1, 1]]
  ![-845, 29, -36] ![![27, 0, 0], ![-2, 1, 0]] where
    su := ![![351, 0, 0], ![351, 27, 27]]
    hsu := by decide
    w := ![![-22815, 783, -972], ![4563, -162, 189]]
    hw := by decide
    g := ![![![-68819, 3717, -39288], ![5240, 122775, -22099]], ![![-68818, 3716, -39288], ![5262, 122775, -22099]]]
    h := ![![![-42, 4, -1], ![-23, 0, 0]], ![![6, -1, 0], ![7, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {27} * I13N1 =  Ideal.span {B.equivFun.symm ![-845, 29, -36]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E13RS1 


noncomputable def E17RS1 : RelationCertificate Table 3 ![![17, 0, 0], ![-5, 1, 0]]
  ![-7, -2, 0] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![51, 0, 0], ![-15, 3, 0]]
    hsu := by decide
    w := ![![-21, -6, 0], ![-9, -3, -18]]
    hw := by decide
    g := ![![![-992, -167, 61], ![-386, 0, -39]], ![![251, 35, -13], ![97, 0, 9]]]
    h := ![![![-156, 1591, -1800], ![151, 3400, 0]], ![![-64, 678, -768], ![73, 1450, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {3} * I17N1 =  Ideal.span {B.equivFun.symm ![-7, -2, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E17RS1 


noncomputable def E19RS1 : RelationCertificate Table 9 ![![19, 0, 0], ![-4, 1, 0]]
  ![-4, 1, 0] ![![9, 0, 0], ![-2, 1, 0]] where
    su := ![![171, 0, 0], ![-36, 9, 0]]
    hsu := by decide
    w := ![![-36, 9, 0], ![9, -9, 9]]
    hw := by decide
    g := ![![![-19691, -6378, 519], ![3674, 0, -2336]], ![![4630, 1498, -122], ![-855, 0, 549]]]
    h := ![![![-23, 188, -243], ![20, 513, 0]], ![![8, -50, 64], ![4, -135, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {9} * I19N1 =  Ideal.span {B.equivFun.symm ![-4, 1, 0]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E19RS1 


noncomputable def E23RS1 : RelationCertificate Table 243 ![![23, 0, 0], ![7, 1, 0]]
  ![143, -2, 9] ![![243, 0, 0], ![-29, 1, 0]] where
    su := ![![5589, 0, 0], ![1701, 243, 0]]
    hsu := by decide
    w := ![![34749, -486, 2187], ![-4860, 0, -243]]
    hw := by decide
    g := ![![![65951880032891, -2174624960059318, 611632736317490], ![-16819874407347, -16514083905162852, -8852624]], ![![20984689196536, -691926126793077, 194610416983565], ![-5351778244811, -5254481266380544, -2816744]]]
    h := ![![![-213, -992, -2241], ![-98, 5728, 0]], ![![26, 138, 313], ![26, -800, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {243} * I23N1 =  Ideal.span {B.equivFun.symm ![143, -2, 9]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E23RS1 


noncomputable def E29RS1 : RelationCertificate Table 729 ![![29, 0, 0], ![-6, 1, 0]]
  ![-14681, 518, -630] ![![729, 0, 0], ![-29, 1, 0]] where
    su := ![![21141, 0, 0], ![-4374, 729, 0]]
    hsu := by decide
    w := ![![-10702449, 377622, -459270], ![476037, -16767, 20412]]
    hw := by decide
    g := ![![![-1022450044517599, 32827381885697216, -9232734239369604], ![85704297910908, 747851472160665028, -442178242]], ![![229215349817115, -7359322700268740, 2069816926306429], ![-19213398963656, -167655170755463528, 99128599]]]
    h := ![![![-76925, 765121, -766584], ![42315, 2470034, 0]], ![![3422, -34032, 34097], ![-1880, -109865, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {729} * I29N1 =  Ideal.span {B.equivFun.symm ![-14681, 518, -630]} * (J0 ^ 6) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6 E29RS1 


noncomputable def E31RS1 : RelationCertificate Table 2187 ![![31, 0, 0], ![10, 1, 0]]
  ![383, 100, 36] ![![2187, 0, 0], ![-758, 1, 0]] where
    su := ![![67797, 0, 0], ![21870, 2187, 0]]
    hsu := by decide
    w := ![![837621, 218700, 78732], ![-293058, -76545, -26244]]
    hw := by decide
    g := ![![![256507537165, -248637518740302, 2940523656204], ![-202592697466, -714547248459576, -24]], ![![128264095022, -124328768508383, 1470380201660], ![-101304502890, -357302389004384, -12]]]
    h := ![![![-859, -7178, -9252], ![-486, 31872, 0]], ![![297, 2511, 3237], ![181, -11151, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {2187} * I31N1 =  Ideal.span {B.equivFun.symm ![383, 100, 36]} * (J0 ^ 7) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7 E31RS1 
