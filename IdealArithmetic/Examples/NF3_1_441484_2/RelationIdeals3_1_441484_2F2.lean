import IdealArithmetic.Examples.NF3_1_441484_2.PrimesBelow3_1_441484_2F2
import IdealArithmetic.Examples.NF3_1_441484_2.ClassGroupData3_1_441484_2

set_option linter.all false

noncomputable section


noncomputable def E101RS0 : RelationCertificate Table 3 ![![101, 0, 0], ![9, 1, 0]]
  ![-20717, 1085, -1727] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![303, 0, 0], ![27, 3, 0]]
    hsu := by decide
    w := ![![-62151, 3255, -5181], ![226038, -11838, 18843]]
    hw := by decide
    g := ![![![-1375, -2466, -5973], ![-819, 1616, 0]], ![![-55, -207, -506], ![-68, 136, 0]]]
    h := ![![![-137170, -646682, -508277], ![-18533, 4666750, 0]], ![![498845, 2351925, 1848561], ![67749, -16972580, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N0 : Ideal.span {3} * I101N0 =  Ideal.span {B.equivFun.symm ![-20717, 1085, -1727]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E101RS0 


noncomputable def E101RS2 : RelationCertificate Table 9 ![![101, 0, 0], ![-26, 1, 0]]
  ![-5, -1, 1] ![![9, 0, 0], ![-3, 1, 0]] where
    su := ![![909, 0, 0], ![-234, 9, 0]]
    hsu := by decide
    w := ![![-45, -9, 9], ![-117, -9, -18]]
    hw := by decide
    g := ![![![286825, 215117, 1139329], ![-71698, -932178, 0]], ![![-65416, -49062, -259847], ![16354, 212602, 0]]]
    h := ![![![-8108, 61743, -32356], ![2783, 297087, 0]], ![![-21170, 160834, -84283], ![7056, 773871, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N2 : Ideal.span {9} * I101N2 =  Ideal.span {B.equivFun.symm ![-5, -1, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E101RS2 


noncomputable def E103RS1 : RelationCertificate Table 9 ![![103, 0, 0], ![-29, 1, 0]]
  ![-35, 2, -2] ![![9, 0, 0], ![-3, 1, 0]] where
    su := ![![927, 0, 0], ![-261, 9, 0]]
    hsu := by decide
    w := ![![-315, 18, -18], ![369, -27, 36]]
    hw := by decide
    g := ![![![-2068572, -1551427, -8216812], ![517145, 6722846, 0]], ![![577457, 433090, 2293775], ![-144359, -1876725, 0]]]
    h := ![![![-60188, 531182, -243557], ![22152, 2280579, 0]], ![![70547, -622383, 285374], ![-25866, -2672138, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {9} * I103N1 =  Ideal.span {B.equivFun.symm ![-35, 2, -2]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E103RS1 


noncomputable def E131RS0 : RelationCertificate Table 3 ![![131, 0, 0], ![23, 1, 0]]
  ![-4832, -160, 199] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![393, 0, 0], ![69, 3, 0]]
    hsu := by decide
    w := ![![-14496, -480, 597], ![-26151, -6030, -2556]]
    hw := by decide
    g := ![![![2398962, 280590, 1111746], ![93533, -254448, 0]], ![![245025, 61351, 189271], ![20453, -47120, 0]]]
    h := ![![![-2306857, -22470591, -8829459], ![-576483, 105150848, 0]], ![![-4147161, -40396774, -15873270], ![-1036480, 189036138, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N0 : Ideal.span {3} * I131N0 =  Ideal.span {B.equivFun.symm ![-4832, -160, 199]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E131RS0 


noncomputable def E131RS1 : RelationCertificate Table 3 ![![131, 0, 0], ![24, 1, 0]]
  ![-193, 10, -16] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![393, 0, 0], ![72, 3, 0]]
    hsu := by decide
    w := ![![-579, 30, -48], ![2094, -111, 174]]
    hw := by decide
    g := ![![![-265, -315, -766], ![-103, 210, 0]], ![![-54, -61, -146], ![-18, 40, 0]]]
    h := ![![![-12605, -127475, -48362], ![-3199, 575946, 0]], ![![45532, 461029, 174908], ![11874, -2082990, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {3} * I131N1 =  Ideal.span {B.equivFun.symm ![-193, 10, -16]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E131RS1 


noncomputable def E131RS2 : RelationCertificate Table 3 ![![131, 0, 0], ![-48, 1, 0]]
  ![383, -20, 32] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![393, 0, 0], ![-144, 3, 0]]
    hsu := by decide
    w := ![![1149, -60, 96], ![-4188, 219, -348]]
    hw := by decide
    g := ![![![2077, 3135, 7680], ![1047, -2096, 0]], ![![-764, -1162, -2844], ![-385, 776, 0]]]
    h := ![![![14539, -245522, 62822], ![-7088, -748150, 0]], ![![-52829, 894904, -228981], ![26284, 2726945, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N2 : Ideal.span {3} * I131N2 =  Ideal.span {B.equivFun.symm ![383, -20, 32]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E131RS2 


noncomputable def E137RS1 : RelationCertificate Table 3 ![![137, 0, 0], ![-63, 1, 0]]
  ![59861, 5485, -1] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![411, 0, 0], ![-189, 3, 0]]
    hsu := by decide
    w := ![![179583, 16455, -3], ![16584, 87288, 60339]]
    hw := by decide
    g := ![![![-441246586, 20797488, -36784276], ![6932498, 357, 0]], ![![238050105, -11220175, 19844812], ![-3740058, -164, 0]]]
    h := ![![![1363825, -34143394, 6476692], ![-876327, -80664255, 0]], ![![112942, -2826106, 536273], ![-72446, -6677208, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {3} * I137N1 =  Ideal.span {B.equivFun.symm ![59861, 5485, -1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E137RS1 
