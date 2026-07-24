import IdealArithmetic.Examples.NF3_1_977075_1.PrimesBelow3_1_977075_1F1
import IdealArithmetic.Examples.NF3_1_977075_1.ClassGroupData3_1_977075_1

set_option linter.all false

noncomputable section


noncomputable def E37RS1 : RelationCertificate Table 256 ![![37, 0, 0], ![-6, 1, 0]]
  ![-679, 41, 11] ![![256, 0, 0], ![-28, 1, 0]] where
    su := ![![9472, 0, 0], ![-1536, 256, 0]]
    hsu := by decide
    w := ![![-173824, 10496, 2816], ![15360, -1024, -256]]
    hw := by decide
    g := ![![![-9051, -21468733, 766752], ![-82750, -196288515, 0]], ![![1486, 3488579, -124594], ![13585, 31896065, 0]]]
    h := ![![![-1096207, 187153, -742], ![-6759830, 27465, 0]], ![![96876, -16536, 65], ![597392, -2406, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {256} * I37N1 =  Ideal.span {B.equivFun.symm ![-679, 41, 11]} * (J0 ^ 8) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8 E37RS1 


noncomputable def E37RS2 : RelationCertificate Table 2 ![![37, 0, 0], ![-1, 1, 0]]
  ![13323, -4283, 395] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![74, 0, 0], ![-2, 2, 0]]
    hsu := by decide
    w := ![![26646, -8566, 790], ![-131140, 42158, -3888]]
    hw := by decide
    g := ![![![1657, -74, 5339], ![-37, -10731, 0]], ![![193, -4, -76], ![-2, 147, 0]]]
    h := ![![![740, -495, 10], ![14057, 25, 0]], ![![-3634, 2433, -54], ![-68888, 54, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N2 : Ideal.span {2} * I37N2 =  Ideal.span {B.equivFun.symm ![13323, -4283, 395]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E37RS2 


noncomputable def E41RS0 : RelationCertificate Table 8 ![![41, 0, 0], ![7, 1, 0]]
  ![-69, 3, 1] ![![8, 0, 0], ![4, 1, 0]] where
    su := ![![328, 0, 0], ![56, 8, 0]]
    hsu := by decide
    w := ![![-552, 24, 8], ![-608, 16, 8]]
    hw := by decide
    g := ![![![18020207, -360404238, -91227323], ![-36040420, 729818583, 0]], ![![2637085, -52741737, -13350252], ![-5274169, 106802016, 0]]]
    h := ![![![-71, -17, -1], ![406, 42, 0]], ![![-78, -18, -1], ![446, 42, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N0 : Ideal.span {8} * I41N0 =  Ideal.span {B.equivFun.symm ![-69, 3, 1]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E41RS0 


noncomputable def E41RS1 : RelationCertificate Table 2 ![![41, 0, 0], ![15, 1, 0]]
  ![87, -1, -1] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![82, 0, 0], ![30, 2, 0]]
    hsu := by decide
    w := ![![174, -2, -2], ![332, 14, -2]]
    hw := by decide
    g := ![![![-135, 34, 159], ![19, -326, 0]], ![![-17, 4, 81], ![3, -163, 0]]]
    h := ![![![282, 19, 0], ![-765, -1, 0]], ![![536, 36, 0], ![-1454, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {2} * I41N1 =  Ideal.span {B.equivFun.symm ![87, -1, -1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E41RS1 


noncomputable def E41RS2 : RelationCertificate Table 32 ![![41, 0, 0], ![18, 1, 0]]
  ![183, -57, 5] ![![32, 0, 0], ![4, 1, 0]] where
    su := ![![1312, 0, 0], ![576, 32, 0]]
    hsu := by decide
    w := ![![5856, -1824, 160], ![-928, 320, -32]]
    hw := by decide
    g := ![![![-22128, 5749471, 1438750], ![176931, -46039993, 0]], ![![-10251, 2662471, 666258], ![81953, -21320252, 0]]]
    h := ![![![879, 45, 0], ![-1992, 5, 0]], ![![-157, -26, -1], ![356, 40, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N2 : Ideal.span {32} * I41N2 =  Ideal.span {B.equivFun.symm ![183, -57, 5]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E41RS2 


noncomputable def E53RS1 : RelationCertificate Table 256 ![![53, 0, 0], ![15, 1, 0]]
  ![-85, 27, 1] ![![256, 0, 0], ![-28, 1, 0]] where
    su := ![![13568, 0, 0], ![3840, 256, 0]]
    hsu := by decide
    w := ![![-21760, 6912, 256], ![2048, -768, 0]]
    hw := by decide
    g := ![![![-502161, -1189448134, 42480931], ![-4591193, -10875118339, 0]], ![![-181079, -428900333, 15318100], ![-1655582, -3921433601, 0]]]
    h := ![![![-176900, -13413, -108], ![625041, 5725, 0]], ![![16606, 1257, 10], ![-58674, -530, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {256} * I53N1 =  Ideal.span {B.equivFun.symm ![-85, 27, 1]} * (J0 ^ 8) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8 E53RS1 


noncomputable def E59RS1 : RelationCertificate Table 64 ![![59, 0, 0], ![20, 1, 0]]
  ![-1659, 533, -49] ![![64, 0, 0], ![-28, 1, 0]] where
    su := ![![3776, 0, 0], ![1280, 64, 0]]
    hsu := by decide
    w := ![![-106176, 34112, -3136], ![62720, -20160, 1856]]
    hw := by decide
    g := ![![![1747931, 304631800, -10881937], ![3995219, 696443946, 0]], ![![618016, 107709856, -3847569], ![1412586, 246244407, 0]]]
    h := ![![![-1661, -96, -2], ![4817, 69, 0]], ![![940, 31, 0], ![-2724, 29, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {64} * I59N1 =  Ideal.span {B.equivFun.symm ![-1659, 533, -49]} * (J0 ^ 6) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6 E59RS1 


noncomputable def E73RS1 : RelationCertificate Table 16 ![![73, 0, 0], ![-18, 1, 0]]
  ![97, -31, 3] ![![16, 0, 0], ![4, 1, 0]] where
    su := ![![1168, 0, 0], ![-288, 16, 0]]
    hsu := by decide
    w := ![![1552, -496, 48], ![-608, 192, -16]]
    hw := by decide
    g := ![![![-33539, 2281994, 572596], ![134248, -9161541, 0]], ![![8728, -593941, -149031], ![-34929, 2384497, 0]]]
    h := ![![![28609, -1661, 4], ![116020, -289, 0]], ![![-11198, 658, -2], ![-45412, 145, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {16} * I73N1 =  Ideal.span {B.equivFun.symm ![97, -31, 3]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E73RS1 
