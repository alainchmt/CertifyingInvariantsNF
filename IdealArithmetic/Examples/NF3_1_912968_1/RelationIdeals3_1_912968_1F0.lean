import IdealArithmetic.Examples.NF3_1_912968_1.PrimesBelow3_1_912968_1F0
import IdealArithmetic.Examples.NF3_1_912968_1.ClassGroupData3_1_912968_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 2 ![![2, 0, 0], ![-16, -2, 1]]
  ![193158203, 44386435, 9926722] ![![2, 0, 0], ![-15, -2, 1]] where
    su := ![![4, 0, 0], ![-32, -4, 2]]
    hsu := by decide
    w := ![![386316406, 88772870, 19853444], ![2712748638, 623371098, 139412674]]
    hw := by decide
    g := ![![![-840, 2969, -984], ![2919, 0, -3]], ![![-659, 19452, -1854], ![-15411, 0, 18]]]
    h := ![![![1473639979, -3970647925, 2435989889], ![-6600476883, -579474609, 0]], ![![10348032759, -27882247779, 17105740663], ![-46349143860, -4069122957, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {2} * I2N0 =  Ideal.span {B.equivFun.symm ![193158203, 44386435, 9926722]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 1 ![![2, 0, 0], ![-15, -2, 1]]
  ![1, 0, 0] ![![2, 0, 0], ![-15, -2, 1]] where
    su := ![![2, 0, 0], ![-15, -2, 1]]
    hsu := by decide
    w := ![![2, 0, 0], ![-15, -2, 1]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![31, -89, 8], ![-31, 0, 2]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![31, -89, 8], ![-31, 0, 2]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {1} * I2N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS1 


noncomputable def E5RS0 : RelationCertificate Table 2 ![![5, 0, 0], ![-14, -2, 1]]
  ![4266898, 980504, 219283] ![![2, 0, 0], ![-16, -1, 1]] where
    su := ![![10, 0, 0], ![-28, -4, 2]]
    hsu := by decide
    w := ![![8533796, 1961008, 438566], ![98083178, 22538844, 5040658]]
    hw := by decide
    g := ![![![63, -403, 125], ![-189, 0, 0]], ![![-305, 120, -526], ![2162, 0, 0]]]
    h := ![![![91704, 87290, 98262], ![-272027, 0, 0]], ![![1053975, 1003264, 1129376], ![-3126551, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {2} * I5N0 =  Ideal.span {B.equivFun.symm ![4266898, 980504, 219283]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 2 ![![5, 0, 0], ![-2, 1, 0]]
  ![-39, -9, -2] ![![2, 0, 0], ![-15, -2, 1]] where
    su := ![![10, 0, 0], ![-4, 2, 0]]
    hsu := by decide
    w := ![![-78, -18, -4], ![-556, -126, -28]]
    hw := by decide
    g := ![![![994, -5177, 508], ![-1929, 0, 114]], ![![-321, 1730, -171], ![647, 0, -38]]]
    h := ![![![86, -235, 248], ![-76, -621, 0]], ![![603, -1673, 1772], ![-572, -4437, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {2} * I5N1 =  Ideal.span {B.equivFun.symm ![-39, -9, -2]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E5RS1 


noncomputable def E11RS0 : RelationCertificate Table 2 ![![11, 0, 0], ![-15, 3, 1]]
  ![-163423049571, -37553499953, -8398582904] ![![2, 0, 0], ![-15, -2, 1]] where
    su := ![![22, 0, 0], ![-30, 6, 2]]
    hsu := by decide
    w := ![![-326846099142, -75106999906, -16797165808], ![-2295142780662, -527408125916, -117951212944]]
    hw := by decide
    g := ![![![14016, -38804, 13710], ![-59415, 0, 344]], ![![-24200, 40934, -23027], ![129082, 0, -473]]]
    h := ![![![-5930619441, -5199158827, -1358575632], ![6545749048, 0, 0]], ![![-41645344491, -36508962104, -9540040594], ![45964840062, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {2} * I11N0 =  Ideal.span {B.equivFun.symm ![-163423049571, -37553499953, -8398582904]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 2 ![![11, 0, 0], ![4, 1, 0]]
  ![-39, -1, 1] ![![2, 0, 0], ![-16, -1, 1]] where
    su := ![![22, 0, 0], ![8, 2, 0]]
    hsu := by decide
    w := ![![-78, -2, 2], ![354, 112, -30]]
    hw := by decide
    g := ![![![6, -24, -17], ![19, 0, 0]], ![![-1, -31, -21], ![23, 0, 0]]]
    h := ![![![-13, -42, -21], ![-3, 116, 0]], ![![44, 174, 85], ![42, -475, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {2} * I11N1 =  Ideal.span {B.equivFun.symm ![-39, -1, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E11RS1 


noncomputable def E17RS0 : RelationCertificate Table 2 ![![17, 0, 0], ![5, 1, 0]]
  ![-12032, -5458, 1355] ![![2, 0, 0], ![-16, -1, 1]] where
    su := ![![34, 0, 0], ![10, 2, 0]]
    hsu := by decide
    w := ![![-24064, -10916, 2710], ![-944702, 74020, 4266]]
    hw := by decide
    g := ![![![2638337, 36927627, 24862837], ![-27139001, 0, 0]], ![![2319067, 32458989, 21854168], ![-23854892, 0, 0]]]
    h := ![![![100697, 598195, 241011], ![64807, -2047916, 0]], ![![4276248, 25407965, 10227201], ![2752315, -86930142, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N0 : Ideal.span {2} * I17N0 =  Ideal.span {B.equivFun.symm ![-12032, -5458, 1355]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E17RS0 


noncomputable def E17RS1 : RelationCertificate Table 2 ![![17, 0, 0], ![6, 1, 0]]
  ![166576, -5174, -2353] ![![2, 0, 0], ![-16, -1, 1]] where
    su := ![![34, 0, 0], ![12, 2, 0]]
    hsu := by decide
    w := ![![333152, -10348, -4706], ![-3444982, -406088, 152926]]
    hw := by decide
    g := ![![![-37291621, -521956391, -351425703], ![383598329, 0, 0]], ![![-34972554, -489497402, -329571535], ![359743437, 0, 0]]]
    h := ![![![147560, 1062160, 356263], ![114578, -3029412, 0]], ![![-1455091, -10458455, -3499805], ![-1128753, 29786574, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {2} * I17N1 =  Ideal.span {B.equivFun.symm ![166576, -5174, -2353]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E17RS1 


noncomputable def E19RS0 : RelationCertificate Table 2 ![![19, 0, 0], ![6, 1, 0]]
  ![-3263044720710814195, -749825377065998565, -167693306900646688] ![![2, 0, 0], ![-15, -2, 1]] where
    su := ![![38, 0, 0], ![12, 2, 0]]
    hsu := by decide
    w := ![![-6526089441421628390, -1499650754131997130, -335386613801293376], ![-45826788530604266282, -10530682822575218476, -2355115044717992004]]
    hw := by decide
    g := ![![![-239981903, 1280361108, -307757795], ![365624285, 0, 1950]], ![![-74779490, 242377844, -87178413], ![274879229, 0, 750]]]
    h := ![![![4281205123508762743, 32300257022863800998, 10824624595280393028], ![3051973040206125133, -102917780308614057110, 0]], ![![30063008423684301129, 226815317405226619916, 76011489990096162530], ![21431229891964864574, -722697933667093042036, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N0 : Ideal.span {2} * I19N0 =  Ideal.span {B.equivFun.symm ![-3263044720710814195, -749825377065998565, -167693306900646688]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E19RS0 


noncomputable def E19RS1 : RelationCertificate Table 2 ![![19, 0, 0], ![-5, 1, 0]]
  ![-85985149, -7827723, 3347954] ![![2, 0, 0], ![-15, -2, 1]] where
    su := ![![38, 0, 0], ![-10, 2, 0]]
    hsu := by decide
    w := ![![-171970298, -15655446, 6695908], ![-1081302500, 284526446, -35718348]]
    hw := by decide
    g := ![![![-6220022178926, -49627373184969, -59309828220188], ![66622625416895, 0, -2250]], ![![-1618128345034, -12910478076348, -15429352488127], ![17331764420126, 0, 450]]]
    h := ![![![-2178130587, 12417163411, -4992679786], ![1226727188, 47432131944, 0]], ![![-14020072229, 79940593992, -32140432904], ![7896892380, 305325183001, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {2} * I19N1 =  Ideal.span {B.equivFun.symm ![-85985149, -7827723, 3347954]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E19RS1 


noncomputable def E19RS2 : RelationCertificate Table 2 ![![19, 0, 0], ![-2, 1, 0]]
  ![59893, 13763, 3078] ![![2, 0, 0], ![-15, -2, 1]] where
    su := ![![38, 0, 0], ![-4, 2, 0]]
    hsu := by decide
    w := ![![119786, 27526, 6156], ![841148, 193290, 43228]]
    hw := by decide
    g := ![![![-7709, 40728, -3982], ![15213, 0, -900]], ![![4, 25, -1], ![-29, 0, 0]]]
    h := ![![![-186169, 385668, -386882], ![39907, 3676918, 0]], ![![-1307303, 2708199, -2716720], ![280158, 25819647, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N2 : Ideal.span {2} * I19N2 =  Ideal.span {B.equivFun.symm ![59893, 13763, 3078]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E19RS2 


noncomputable def E23RS1 : RelationCertificate Table 2 ![![23, 0, 0], ![4, 1, 0]]
  ![-207143442463, -47600147453, -10645446766] ![![2, 0, 0], ![-15, -2, 1]] where
    su := ![![46, 0, 0], ![8, 2, 0]]
    hsu := by decide
    w := ![![-414286884926, -95200294906, -21290893532], ![-2909159863180, -668505055266, -149506574232]]
    hw := by decide
    g := ![![![72687, -383350, 89378], ![-117053, 0, 546]], ![![12630, -31445, 12987], ![-56673, 0, 182]]]
    h := ![![![1703546815004, 7246848760254, 3637286524608], ![611349392205, -41834117756375, 0]], ![![11962459347829, 50888025460025, 25541353958538], ![4292950558772, -293762947166745, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {2} * I23N1 =  Ideal.span {B.equivFun.symm ![-207143442463, -47600147453, -10645446766]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E23RS1 


noncomputable def E31RS1 : RelationCertificate Table 2 ![![31, 0, 0], ![-14, 1, 0]]
  ![365, -81, 9] ![![2, 0, 0], ![-16, -1, 1]] where
    su := ![![62, 0, 0], ![-28, 2, 0]]
    hsu := by decide
    w := ![![730, -162, 18], ![-21806, -356, 518]]
    hw := by decide
    g := ![![![840, 11581, 7796], ![-8509, 0, 0]], ![![-99, -1515, -1021], ![1115, 0, 0]]]
    h := ![![![-419, 9230, -1321], ![509, 20480, 0]], ![![12492, -269958, 38639], ![-14330, -598775, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {2} * I31N1 =  Ideal.span {B.equivFun.symm ![365, -81, 9]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E31RS1 
