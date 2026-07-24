import IdealArithmetic.Examples.NF3_1_903756_2.PrimesBelow3_1_903756_2F1
import IdealArithmetic.Examples.NF3_1_903756_2.ClassGroupData3_1_903756_2

set_option linter.all false

noncomputable section


noncomputable def E37RS1 : RelationCertificate Table 9 ![![37, 0, 0], ![11, 1, 0]]
  ![8093, 675, 635] ![![9, 0, 0], ![-3, 1, 0]] where
    su := ![![333, 0, 0], ![99, 9, 0]]
    hsu := by decide
    w := ![![72837, 6075, 5715], ![94626, 7893, 7425]]
    hw := by decide
    g := ![![![312, -323, 736], ![-138, -604, 0]], ![![88, -101, 233], ![-38, -192, 0]]]
    h := ![![![7011963, 17416709, 21371495], ![2555362, -71885880, 0]], ![![9109567, 22626866, 27764715], ![3319805, -93390330, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {9} * I37N1 =  Ideal.span {B.equivFun.symm ![8093, 675, 635]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E37RS1 


noncomputable def E47RS0 : RelationCertificate Table 9 ![![47, 0, 0], ![22, 1, 0]]
  ![-14, 0, 1] ![![9, 0, 0], ![-3, 1, 0]] where
    su := ![![423, 0, 0], ![198, 9, 0]]
    hsu := by decide
    w := ![![-126, 0, 9], ![225, -9, 0]]
    hw := by decide
    g := ![![![219580, -307271, 702234], ![-107334, -574555, 0]], ![![114881, -160758, 367394], ![-56152, -300595, 0]]]
    h := ![![![264, 1783, 983], ![199, -4200, 0]], ![![-507, -3194, -1760], ![-283, 7520, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N0 : Ideal.span {9} * I47N0 =  Ideal.span {B.equivFun.symm ![-14, 0, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E47RS0 


noncomputable def E47RS1 : RelationCertificate Table 9 ![![47, 0, 0], ![-16, 1, 0]]
  ![-12094270, 400086, 283397] ![![9, 0, 0], ![-3, 1, 0]] where
    su := ![![423, 0, 0], ![-144, 9, 0]]
    hsu := by decide
    w := ![![-108848430, 3600774, 2550573], ![89744805, -12677715, 4400946]]
    hw := by decide
    g := ![![![-761332285106, -97253717576, -66093620731], ![242971459756, 0, 0]], ![![21173215723, 2704698042, 1838112632], ![-6757216562, -1, 0]]]
    h := ![![![-16307587930, 84484779538, -51725131519], ![7349067820, 221007405890, 0]], ![![13478530751, -69828298856, 42751819627], ![-6074144453, -182666821225, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {9} * I47N1 =  Ideal.span {B.equivFun.symm ![-12094270, 400086, 283397]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E47RS1 


noncomputable def E47RS2 : RelationCertificate Table 9 ![![47, 0, 0], ![-7, 1, 0]]
  ![433, 36, 34] ![![9, 0, 0], ![-3, 1, 0]] where
    su := ![![423, 0, 0], ![-63, 9, 0]]
    hsu := by decide
    w := ![![3897, 324, 306], ![5067, 423, 396]]
    hw := by decide
    g := ![![![53, -51, 117], ![-14, -97, 0]], ![![-10, 5, -13], ![9, 11, 0]]]
    h := ![![![13556, -31319, 38350], ![-2675, -163856, 0]], ![![17624, -40721, 49863], ![-3489, -213047, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N2 : Ideal.span {9} * I47N2 =  Ideal.span {B.equivFun.symm ![433, 36, 34]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E47RS2 


noncomputable def E53RS0 : RelationCertificate Table 3 ![![53, 0, 0], ![9, 1, 0]]
  ![-89, 18, -8] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![159, 0, 0], ![27, 3, 0]]
    hsu := by decide
    w := ![![-267, 54, -24], ![-1392, -165, 174]]
    hw := by decide
    g := ![![![2575, 188, 227], ![64, -7, 0]], ![![1151, 84, 101], ![29, -3, 0]]]
    h := ![![![1004, 1819, 2864], ![211, -13800, 0]], ![![4962, 8990, 14161], ![1050, -68225, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N0 : Ideal.span {3} * I53N0 =  Ideal.span {B.equivFun.symm ![-89, 18, -8]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E53RS0 


noncomputable def E53RS1 : RelationCertificate Table 3 ![![53, 0, 0], ![-5, 1, 0]]
  ![-340229, -135675, 106399] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![159, 0, 0], ![-15, 3, 0]]
    hsu := by decide
    w := ![![-1020687, -407025, 319197], ![18928317, 463116, -1173228]]
    hw := by decide
    g := ![![![155626865960, 11682544829, 12211402803], ![3894181610, 133, 0]], ![![28461790440, 2136560014, 2233280253], ![712186673, -10, 0]]]
    h := ![![![-79455812, 140517656, -221116333], ![10147133, 1065388368, 0]], ![![1500252750, -2653247251, 4175066436], ![-191594533, -20116264744, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {3} * I53N1 =  Ideal.span {B.equivFun.symm ![-340229, -135675, 106399]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E53RS1 


noncomputable def E59RS1 : RelationCertificate Table 3 ![![59, 0, 0], ![-23, 1, 0]]
  ![-2230, -186, -175] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![177, 0, 0], ![-69, 3, 0]]
    hsu := by decide
    w := ![![-6690, -558, -525], ![-32769, -2733, -2571]]
    hw := by decide
    g := ![![![30, -6, -40], ![0, 13, 0]], ![![11, 3, 13], ![4, -5, 0]]]
    h := ![![![-885549, 6642223, -2925997], ![457857, 15693968, 0]], ![![-4337689, 32534987, -14332139], ![2242456, 76872304, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {3} * I59N1 =  Ideal.span {B.equivFun.symm ![-2230, -186, -175]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E59RS1 


noncomputable def E67RS1 : RelationCertificate Table 3 ![![67, 0, 0], ![-6, 1, 0]]
  ![3442922, 287169, 270152] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![201, 0, 0], ![-18, 3, 0]]
    hsu := by decide
    w := ![![10328766, 861507, 810456], ![50586492, 4219344, 3969315]]
    hw := by decide
    g := ![![![-5079, 468, -117], ![157, 0, 0]], ![![177, -137, 120], ![-45, -8, 0]]]
    h := ![![![-426204712, 860892372, -1184764072], ![51016773, 7216314816, 0]], ![![-2087393732, 4216333792, -5802538101], ![249861200, 35342852352, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {3} * I67N1 =  Ideal.span {B.equivFun.symm ![3442922, 287169, 270152]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E67RS1 
