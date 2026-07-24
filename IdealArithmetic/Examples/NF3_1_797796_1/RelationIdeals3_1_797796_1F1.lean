import IdealArithmetic.Examples.NF3_1_797796_1.PrimesBelow3_1_797796_1F1
import IdealArithmetic.Examples.NF3_1_797796_1.ClassGroupData3_1_797796_1

set_option linter.all false

noncomputable section


noncomputable def E47RS1 : RelationCertificate Table 8 ![![47, 0, 0], ![-2, 1, 0]]
  ![882, 195, 22] ![![8, 0, 0], ![-75, -5, 1]] where
    su := ![![376, 0, 0], ![-16, 8, 0]]
    hsu := by decide
    w := ![![7056, 1560, 176], ![-5800, -1280, -144]]
    hw := by decide
    g := ![![![264596, -26180, 31520], ![-2460091, 0, 52570]], ![![-7546, 751, -901], ![70288, 0, -1502]]]
    h := ![![![13814, -6905, 12], ![324188, -271, 0]], ![![-11353, 5677, -12], ![-266433, 273, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {8} * I47N1 =  Ideal.span {B.equivFun.symm ![882, 195, 22]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E47RS1 


noncomputable def E59RS1 : RelationCertificate Table 8 ![![59, 0, 0], ![11, 1, 0]]
  ![-88021244, -19471287, -2197237] ![![8, 0, 0], ![-75, -1, 1]] where
    su := ![![472, 0, 0], ![88, 8, 0]]
    hsu := by decide
    w := ![![-704169952, -155770296, -17577896], ![-5662982200, -1252715216, -141362624]]
    hw := by decide
    g := ![![![-3296, -9590, -548], ![32247, 0, 0]], ![![-94, -613, -12], ![1597, 0, 0]]]
    h := ![![![-5529988176, -525736880, -4185657], ![29652843740, 122378263, 0]], ![![-44472537355, -4228011389, -33661334], ![238470166470, 984174189, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {8} * I59N1 =  Ideal.span {B.equivFun.symm ![-88021244, -19471287, -2197237]} * (J0 ^ 6) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6 E59RS1 


noncomputable def E61RS1 : RelationCertificate Table 16 ![![61, 0, 0], ![-14, 1, 0]]
  ![-14, 1, 0] ![![16, 0, 0], ![-383, -13, 5]] where
    su := ![![976, 0, 0], ![-224, 16, 0]]
    hsu := by decide
    w := ![![-224, 16, 0], ![8912, 384, -96]]
    hw := by decide
    g := ![![![-116601, 1932912, 279797], ![1311621, 0, -54628]], ![![25026, -414194, -59957], ![-281060, 0, 11706]]]
    h := ![![![-3374, 255, -2], ![-14700, 61, 0]], ![![134531, -10043, 62], ![586131, -1894, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {16} * I61N1 =  Ideal.span {B.equivFun.symm ![-14, 1, 0]} * (J0 ^ 7) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7 E61RS1 


noncomputable def E71RS0 : RelationCertificate Table 8 ![![71, 0, 0], ![0, 1, 0]]
  ![-12354, 59, 72] ![![8, 0, 0], ![-75, -5, 1]] where
    su := ![![568, 0, 0], ![0, 8, 0]]
    hsu := by decide
    w := ![![-98832, 472, 576], ![712840, 47688, -9920]]
    hw := by decide
    g := ![![![1176, 112261, 27783], ![-77303, 0, 0]], ![![320, 28025, 6935], ![-19294, 0, 0]]]
    h := ![![![-174, 0, 0], ![59, 36, 0]], ![![1255, 166, -18], ![-5825, 19, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N0 : Ideal.span {8} * I71N0 =  Ideal.span {B.equivFun.symm ![-12354, 59, 72]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E71RS0 


noncomputable def E73RS1 : RelationCertificate Table 8 ![![73, 0, 0], ![21, 1, 0]]
  ![59306, 4780, -917] ![![8, 0, 0], ![-75, -1, 1]] where
    su := ![![584, 0, 0], ![168, 8, 0]]
    hsu := by decide
    w := ![![474448, 38240, -7336], ![-403080, -76792, 11232]]
    hw := by decide
    g := ![![![76558, 1766873, 324290], ![-897931, 0, 0]], ![![40626, 937252, 172022], ![-476313, 0, 0]]]
    h := ![![![114068, 5874, 27], ![-393698, -1444, 0]], ![![-97050, -5090, -16], ![334965, 1286, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {8} * I73N1 =  Ideal.span {B.equivFun.symm ![59306, 4780, -917]} * (J0 ^ 6) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6 E73RS1 


noncomputable def E79RS0 : RelationCertificate Table 2 ![![79, 0, 0], ![20, 1, 0]]
  ![4169802, 922407, 104089] ![![2, 0, 0], ![-77, -3, 1]] where
    su := ![![158, 0, 0], ![40, 2, 0]]
    hsu := by decide
    w := ![![8339604, 1844814, 208178], ![112124646, 24803230, 2798920]]
    hw := by decide
    g := ![![![-7, 3932, -139], ![-3559, 0, 0]], ![![43, 562, -25], ![-452, 0, 0]]]
    h := ![![![4172838, 229673, 2517], ![-16274220, -47377, 0]], ![![56103237, 3087975, 33846], ![-218804670, -637187, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N0 : Ideal.span {2} * I79N0 =  Ideal.span {B.equivFun.symm ![4169802, 922407, 104089]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E79RS0 


noncomputable def E79RS1 : RelationCertificate Table 4 ![![79, 0, 0], ![21, 1, 0]]
  ![-74, -17, -2] ![![4, 0, 0], ![-79, -3, 1]] where
    su := ![![316, 0, 0], ![84, 4, 0]]
    hsu := by decide
    w := ![![-296, -68, -8], ![-1964, -432, -48]]
    hw := by decide
    g := ![![![32238, -320160, -42198], ![-406661, 0, 15144]], ![![10749, -106719, -14066], ![-135557, 0, 5048]]]
    h := ![![![-3572, -191, -2], ![13434, 78, 0]], ![![-23552, -1247, -12], ![88577, 468, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {4} * I79N1 =  Ideal.span {B.equivFun.symm ![-74, -17, -2]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E79RS1 


noncomputable def E79RS2 : RelationCertificate Table 4 ![![79, 0, 0], ![38, 1, 0]]
  ![124, 27, 3] ![![4, 0, 0], ![-79, -5, 1]] where
    su := ![![316, 0, 0], ![152, 4, 0]]
    hsu := by decide
    w := ![![496, 108, 12], ![-1276, -284, -32]]
    hw := by decide
    g := ![![![34, 3, 0], ![33, 0, 0]], ![![14, 1, 0], ![12, 0, 0]]]
    h := ![![![8376, 277, 3], ![-17410, -117, 0]], ![![-21703, -798, -12], ![45111, 470, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N2 : Ideal.span {4} * I79N2 =  Ideal.span {B.equivFun.symm ![124, 27, 3]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E79RS2 
