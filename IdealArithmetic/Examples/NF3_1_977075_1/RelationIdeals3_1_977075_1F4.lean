import IdealArithmetic.Examples.NF3_1_977075_1.PrimesBelow3_1_977075_1F4
import IdealArithmetic.Examples.NF3_1_977075_1.ClassGroupData3_1_977075_1

set_option linter.all false

noncomputable section


noncomputable def E197RS1 : RelationCertificate Table 64 ![![197, 0, 0], ![83, 1, 0]]
  ![2525, -147, -41] ![![64, 0, 0], ![-28, 1, 0]] where
    su := ![![12608, 0, 0], ![5312, 64, 0]]
    hsu := by decide
    w := ![![161600, -9408, -2624], ![-57088, 3648, 960]]
    hw := by decide
    g := ![![![-23, 2707, -98], ![107, 6140, 0]], ![![-1, 1162, -42], ![57, 2639, 0]]]
    h := ![![![18810, 243, 0], ![-44615, -41, 0]], ![![-6808, -171, -1], ![16148, 212, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R197N1 : Ideal.span {64} * I197N1 =  Ideal.span {B.equivFun.symm ![2525, -147, -41]} * (J0 ^ 6) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6 E197RS1 


noncomputable def E199RS1 : RelationCertificate Table 4 ![![199, 0, 0], ![27, 1, 0]]
  ![23, -9, 1] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![796, 0, 0], ![108, 4, 0]]
    hsu := by decide
    w := ![![92, -36, 4], ![-332, 96, -8]]
    hw := by decide
    g := ![![![70, -8, 173], ![1, -698, 0]], ![![12, -2, 24], ![3, -97, 0]]]
    h := ![![![140, 5, 0], ![-1031, 1, 0]], ![![-632, -50, -1], ![4655, 197, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R199N1 : Ideal.span {4} * I199N1 =  Ideal.span {B.equivFun.symm ![23, -9, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E199RS1 


noncomputable def E223RS1 : RelationCertificate Table 32 ![![223, 0, 0], ![75, 1, 0]]
  ![-157751, 50713, -4677] ![![32, 0, 0], ![4, 1, 0]] where
    su := ![![7136, 0, 0], ![2400, 32, 0]]
    hsu := by decide
    w := ![![-5048032, 1622816, -149664], ![921760, -296320, 27328]]
    hw := by decide
    g := ![![![287234, -74653418, -18681308], ![-2297007, 597801974, 0]], ![![99284, -25806471, -6457824], ![-794025, 206650415, 0]]]
    h := ![![![-258299237, -3948880, -6756], ![768007628, 1501911, 0]], ![![47164835, 721009, 1233], ![-140236392, -274105, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R223N1 : Ideal.span {32} * I223N1 =  Ideal.span {B.equivFun.symm ![-157751, 50713, -4677]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E223RS1 


noncomputable def E233RS1 : RelationCertificate Table 256 ![![233, 0, 0], ![2, 1, 0]]
  ![5, 149, 15] ![![256, 0, 0], ![-28, 1, 0]] where
    su := ![![59648, 0, 0], ![512, 256, 0]]
    hsu := by decide
    w := ![![1280, 38144, 3840], ![-5120, -3072, -256]]
    hw := by decide
    g := ![![![-628426529283, -1488473122243897, 53160555930304], ![-5745613981982, -13609102318157855, 0]], ![![-2697114306, -6388307937009, 228157295090], ![-24659330799, -58408267543039, 0]]]
    h := ![![![2537, 1269, 0], ![-295558, 15, 0]], ![![-10136, -5070, -1], ![1180834, 232, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R233N1 : Ideal.span {256} * I233N1 =  Ideal.span {B.equivFun.symm ![5, 149, 15]} * (J0 ^ 8) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8 E233RS1 


noncomputable def E251RS0 : RelationCertificate Table 64 ![![251, 0, 0], ![32, 1, 0]]
  ![-193, 47, -3] ![![64, 0, 0], ![-28, 1, 0]] where
    su := ![![16064, 0, 0], ![2048, 64, 0]]
    hsu := by decide
    w := ![![-12352, 3008, -192], ![6400, -1728, 128]]
    hw := by decide
    g := ![![![16547117, 2883922321, -103018332], ![37821963, 6593173235, 0]], ![![2151940, 375049308, -13397363], ![4918717, 857431230, 0]]]
    h := ![![![-2291, -103, -1], ![17964, 248, 0]], ![![1132, 35, 0], ![-8876, 2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R251N0 : Ideal.span {64} * I251N0 =  Ideal.span {B.equivFun.symm ![-193, 47, -3]} * (J0 ^ 6) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6 E251RS0 


noncomputable def E251RS1 : RelationCertificate Table 16 ![![251, 0, 0], ![-23, 1, 0]]
  ![1829, -139, -33] ![![16, 0, 0], ![4, 1, 0]] where
    su := ![![4016, 0, 0], ![-368, 16, 0]]
    hsu := by decide
    w := ![![29264, -2224, -528], ![18272, -1136, -304]]
    hw := by decide
    g := ![![![-603, 499, 54], ![-103, -1162, 0]], ![![75, -54, -4], ![29, 103, 0]]]
    h := ![![![709751, -31092, 10], ![7745464, -2543, 0]], ![![443168, -19408, 6], ![4836262, -1525, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R251N1 : Ideal.span {16} * I251N1 =  Ideal.span {B.equivFun.symm ![1829, -139, -33]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E251RS1 


noncomputable def E251RS2 : RelationCertificate Table 256 ![![251, 0, 0], ![-10, 1, 0]]
  ![-1021, -13, 9] ![![256, 0, 0], ![-28, 1, 0]] where
    su := ![![64256, 0, 0], ![-2560, 256, 0]]
    hsu := by decide
    w := ![![-261376, -3328, 2304], ![25600, 0, -256]]
    hw := by decide
    g := ![![![-2512778395007, -5951695112765685, 212563744816115], ![-22973973897190, -54416318672925453, 0]], ![![110121723910, 260831168868381, -9315539349539], ![1006827190033, 2384778073481985, 0]]]
    h := ![![![-2633421, 263762, -42], ![-66098765, 10551, 0]], ![![257940, -25834, 4], ![6474284, -1005, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R251N2 : Ideal.span {256} * I251N2 =  Ideal.span {B.equivFun.symm ![-1021, -13, 9]} * (J0 ^ 8) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8 E251RS2 


noncomputable def E257RS1 : RelationCertificate Table 4 ![![257, 0, 0], ![109, 1, 0]]
  ![123, -17, -3] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![1028, 0, 0], ![436, 4, 0]]
    hsu := by decide
    w := ![![492, -68, -12], ![996, -96, -20]]
    hw := by decide
    g := ![![![-116, 34, 993831], ![9, -3975337, 0]], ![![-45, 13, 422404], ![4, -1689621, 0]]]
    h := ![![![19162, 177, 0], ![-45179, -3, 0]], ![![39020, 469, 1], ![-91999, -262, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R257N1 : Ideal.span {4} * I257N1 =  Ideal.span {B.equivFun.symm ![123, -17, -3]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E257RS1 
