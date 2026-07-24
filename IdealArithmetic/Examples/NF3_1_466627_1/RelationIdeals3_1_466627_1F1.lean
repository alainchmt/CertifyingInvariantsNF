import IdealArithmetic.Examples.NF3_1_466627_1.PrimesBelow3_1_466627_1F1
import IdealArithmetic.Examples.NF3_1_466627_1.ClassGroupData3_1_466627_1

set_option linter.all false

noncomputable section


noncomputable def E37RS1 : RelationCertificate Table 16 ![![37, 0, 0], ![9, 1, 0]]
  ![91, 33, 3] ![![16, 0, 0], ![4, 1, 0]] where
    su := ![![592, 0, 0], ![144, 16, 0]]
    hsu := by decide
    w := ![![1456, 528, 48], ![1600, 544, 48]]
    hw := by decide
    g := ![![![-74785, 5085585, 1276070], ![299162, -20417123, 0]], ![![-16173, 1099589, 275908], ![64689, -4414528, 0]]]
    h := ![![![7741, 941, 9], ![-31814, -330, 0]], ![![8506, 1026, 9], ![-34958, -330, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {16} * I37N1 =  Ideal.span {B.equivFun.symm ![91, 33, 3]} * (J0 ^ 4*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_0 E37RS1 


noncomputable def E41RS1 : RelationCertificate Table 6 ![![41, 0, 0], ![-8, 1, 0]]
  ![167, 57, 5] ![![6, 0, 0], ![2, 1, 0]] where
    su := ![![246, 0, 0], ![-48, 6, 0]]
    hsu := by decide
    w := ![![1002, 342, 30], ![2394, 816, 72]]
    hw := by decide
    g := ![![![-452, 7676, 3934], ![1131, -23600, 0]], ![![42, -481, -246], ![-62, 1475, 0]]]
    h := ![![![8199, -1054, 4], ![41999, -159, 0]], ![![19583, -2529, 11], ![100313, -439, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {6} * I41N1 =  Ideal.span {B.equivFun.symm ![167, 57, 5]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E41RS1 


noncomputable def E61RS1 : RelationCertificate Table 72 ![![61, 0, 0], ![-21, 1, 0]]
  ![1139, 393, 35] ![![72, 0, 0], ![-4, 1, 0]] where
    su := ![![4392, 0, 0], ![-1512, 72, 0]]
    hsu := by decide
    w := ![![82008, 28296, 2520], ![9864, 3312, 288]]
    hw := by decide
    g := ![![![-57008, -74156190, 18542613], ![-1026739, -1335068174, 0]], ![![19134, 24888516, -6223326], ![344681, 448079489, 0]]]
    h := ![![![2205428, -113632, 411], ![6406189, -25036, 0]], ![![265298, -13660, 49], ![770621, -2985, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {72} * I61N1 =  Ideal.span {B.equivFun.symm ![1139, 393, 35]} * (J0 ^ 3*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_2 E61RS1 


noncomputable def E67RS1 : RelationCertificate Table 24 ![![67, 0, 0], ![-29, 1, 0]]
  ![-191, 3, 1] ![![24, 0, 0], ![-4, 1, 0]] where
    su := ![![1608, 0, 0], ![-696, 24, 0]]
    hsu := by decide
    w := ![![-4584, 72, 24], ![1176, -96, 0]]
    hw := by decide
    g := ![![![-4, -203, 50], ![11, -1204, 0]], ![![4, 64, -16], ![15, 385, 0]]]
    h := ![![![-173003, 6691, -25], ![-399690, 1676, 0]], ![![44427, -1706, 6], ![102640, -402, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {24} * I67N1 =  Ideal.span {B.equivFun.symm ![-191, 3, 1]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E67RS1 


noncomputable def E71RS1 : RelationCertificate Table 48 ![![71, 0, 0], ![25, 1, 0]]
  ![-121, -27, -1] ![![48, 0, 0], ![20, 1, 0]] where
    su := ![![3408, 0, 0], ![1200, 48, 0]]
    hsu := by decide
    w := ![![-5808, -1296, -48], ![-2832, -768, -48]]
    hw := by decide
    g := ![![![34, -4953, -248], ![-43, 11893, 0]], ![![11, -1758, -88], ![-16, 4221, 0]]]
    h := ![![![-75976, -3689, -26], ![215767, 1845, 0]], ![![-37054, -1807, -13], ![105231, 922, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {48} * I71N1 =  Ideal.span {B.equivFun.symm ![-121, -27, -1]} * (J0 ^ 4*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_1 E71RS1 


noncomputable def E73RS1 : RelationCertificate Table 32 ![![73, 0, 0], ![13, 1, 0]]
  ![-123, 47, -3] ![![32, 0, 0], ![4, 1, 0]] where
    su := ![![2336, 0, 0], ![416, 32, 0]]
    hsu := by decide
    w := ![![-3936, 1504, -96], ![-1728, -256, 32]]
    hw := by decide
    g := ![![![-401664163, 104432675532, 26133272893], ![3213313110, -836264732599, 0]], ![![-66027237, 17167079347, 4295896539], ![528217829, -137468689256, 0]]]
    h := ![![![-39719, -3184, -10], ![223028, 727, 0]], ![![-17508, -1412, -5], ![98310, 366, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {32} * I73N1 =  Ideal.span {B.equivFun.symm ![-123, 47, -3]} * (J0 ^ 5*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_0 E73RS1 
