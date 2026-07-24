import IdealArithmetic.Examples.NF3_1_892863_2.PrimesBelow3_1_892863_2F4
import IdealArithmetic.Examples.NF3_1_892863_2.ClassGroupData3_1_892863_2

set_option linter.all false

noncomputable section


noncomputable def E197RS0 : RelationCertificate Table 32 ![![197, 0, 0], ![24, 1, 0]]
  ![-7261, -321, -225] ![![32, 0, 0], ![175, 13, 10]] where
    su := ![![6304, 0, 0], ![768, 32, 0]]
    hsu := by decide
    w := ![![-232352, -10272, -7200], ![-1995136, -88096, -61792]]
    hw := by decide
    g := ![![![-17639, 51054, 10998], ![-71361, 8610, 0]], ![![-2308, 6379, 1370], ![-8908, 1077, 0]]]
    h := ![![![-69950915, -894209601, -143084145], ![-13061049, 7046894085, 0]], ![![-600647438, -7678308675, -1228620483], ![-112151403, 60509558305, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R197N0 : Ideal.span {32} * I197N0 =  Ideal.span {B.equivFun.symm ![-7261, -321, -225]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E197RS0 


noncomputable def E197RS2 : RelationCertificate Table 2 ![![197, 0, 0], ![-72, 1, 0]]
  ![24189750062, 1068537107, 749331126] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![394, 0, 0], ![-144, 2, 0]]
    hsu := by decide
    w := ![![48379500124, 2137074214, 1498662252], ![137977162050, 6094883874, 4274148428]]
    hw := by decide
    g := ![![![-509055, 183954, 27836], ![-162549, 0, 0]], ![![205512, -76157, -8230], ![64678, 0, 0]]]
    h := ![![![176121254890, -7581937765491, 427184947494], ![-102856183324, -21038671331298, 0]], ![![502293551277, -21623502786115, 1218321118958], ![-293343342496, -60001780840128, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R197N2 : Ideal.span {2} * I197N2 =  Ideal.span {B.equivFun.symm ![24189750062, 1068537107, 749331126]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E197RS2 


noncomputable def E211RS1 : RelationCertificate Table 8 ![![211, 0, 0], ![-96, 1, 0]]
  ![13, -3, 1] ![![8, 0, 0], ![-33, 1, -2]] where
    su := ![![1688, 0, 0], ![-768, 8, 0]]
    hsu := by decide
    w := ![![104, -24, 8], ![784, -168, -24]]
    hw := by decide
    g := ![![![10572404, -8259445, -13944990], ![-41157301, 4874222, 0]], ![![-4788311, 3740773, 6315807], ![18640500, -2207577, 0]]]
    h := ![![![531, -30470, 1283], ![-243, -67678, 0]], ![![3618, -229674, 9671], ![-2677, -510146, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R211N1 : Ideal.span {8} * I211N1 =  Ideal.span {B.equivFun.symm ![13, -3, 1]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E211RS1 


noncomputable def E229RS1 : RelationCertificate Table 16 ![![229, 0, 0], ![-58, 1, 0]]
  ![24406459, -5799881, 745863] ![![16, 0, 0], ![12, 1, 1]] where
    su := ![![3664, 0, 0], ![-928, 16, 0]]
    hsu := by decide
    w := ![![390503344, -92798096, 11933808], ![-537406880, 118284464, -4926992]]
    hw := by decide
    g := ![![![-11292495268383, -249587503859, -16589099907], ![-8486007489001, 1641444, 0]], ![![2628145914985, 58087424476, 3860842236], ![1974981202922, -410361, 0]]]
    h := ![![![-758873255, 23766134922, -1667888165], ![295985965, 95486783912, 0]], ![![1044110528, -32699102206, 2294799555], ![-407238003, -131377351508, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R229N1 : Ideal.span {16} * I229N1 =  Ideal.span {B.equivFun.symm ![24406459, -5799881, 745863]} * (J0 ^ 4*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_0 E229RS1 


noncomputable def E239RS1 : RelationCertificate Table 8 ![![239, 0, 0], ![-12, 1, 0]]
  ![-271209, 333995, -337125] ![![8, 0, 0], ![20, 1, 1]] where
    su := ![![1912, 0, 0], ![-96, 8, 0]]
    hsu := by decide
    w := ![![-2169672, 2671960, -2697000], ![24444440, -8006304, 3427776]]
    hw := by decide
    g := ![![![254717674508, 2012279584, -22273108340], ![634261582701, -5052, 0]], ![![-7775868399, -61429543, 679940108], ![-19362357172, 231, 0]]]
    h := ![![![-16434771, 90714105, -32989683], ![1204958, 1971049278, 0]], ![![184401227, -1017816843, 370136052], ![-13517190, -22115521989, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R239N1 : Ideal.span {8} * I239N1 =  Ideal.span {B.equivFun.symm ![-271209, 333995, -337125]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E239RS1 


noncomputable def E241RS1 : RelationCertificate Table 16 ![![241, 0, 0], ![49, 1, 0]]
  ![-7941, 1407, 343] ![![16, 0, 0], ![103, 1, 6]] where
    su := ![![3856, 0, 0], ![784, 16, 0]]
    hsu := by decide
    w := ![![-127056, 22512, 5488], ![312752, -8256, -71040]]
    hw := by decide
    g := ![![![3544921, -9849632, -7645273], ![19338203, -2344220, 0]], ![![793006, -2203112, -1710198], ![4326067, -524365, 0]]]
    h := ![![![-372478, -9904090, -792365], ![-116753, 47740077, 0]], ![![916026, 24359035, 1948800], ![287549, -117416310, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R241N1 : Ideal.span {16} * I241N1 =  Ideal.span {B.equivFun.symm ![-7941, 1407, 343]} * (J0 ^ 4*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_1 E241RS1 


noncomputable def E257RS1 : RelationCertificate Table 32 ![![257, 0, 0], ![11, 1, 0]]
  ![-13872984885, -612813241, -429746457] ![![32, 0, 0], ![175, 13, 10]] where
    su := ![![8224, 0, 0], ![352, 32, 0]]
    hsu := by decide
    w := ![![-443935516320, -19610023712, -13751886624], ![-3811039233280, -168345552416, -118055387616]]
    hw := by decide
    g := ![![![-25231, 71426, 13422], ![-104197, 13174, 0]], ![![-1464, 3930, 672], ![-5347, 651, 0]]]
    h := ![![![-1871854906264, -11262154610662, -3754213166385], ![-123939916571, 241208088503622, 0]], ![![-16069253809441, -96681863682110, -32228675429691], ![-1063983095415, 2070691474049931, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R257N1 : Ideal.span {32} * I257N1 =  Ideal.span {B.equivFun.symm ![-13872984885, -612813241, -429746457]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E257RS1 
