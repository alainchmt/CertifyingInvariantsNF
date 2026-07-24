import IdealArithmetic.Examples.NF3_1_767839_1.PrimesBelow3_1_767839_1F0
import IdealArithmetic.Examples.NF3_1_767839_1.ClassGroupData3_1_767839_1

set_option linter.all false

noncomputable section


noncomputable def E3RS0 : RelationCertificate Table 243 ![![3, 0, 0], ![20, 1, 1]]
  ![6047, -938, -215] ![![243, 0, 0], ![-88, 1, 0]] where
    su := ![![729, 0, 0], ![4860, 243, 243]]
    hsu := by decide
    w := ![![1469421, -227934, -52245], ![-565461, 95256, 17982]]
    hw := by decide
    g := ![![![-24786, -19425073, 220764], ![-70900, -53640696, 0]], ![![-154873, -124755993, 1417959], ![-457288, -344504272, 0]]]
    h := ![![![69, -410, -169], ![292, 0, 0]], ![![-29, 168, 62], ![-112, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {243} * I3N0 =  Ideal.span {B.equivFun.symm ![6047, -938, -215]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 1 ![![3, 0, 0], ![-1, 1, 0]]
  ![1, 0, 0] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![3, 0, 0], ![-1, 1, 0]]
    hsu := by decide
    w := ![![3, 0, 0], ![-1, 1, 0]]
    hw := by decide
    g := ![![![2, 1, -2], ![3, 6, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![2, 1, -2], ![3, 6, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {1} * I3N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E3RS1 


noncomputable def E5RS0 : RelationCertificate Table 9 ![![5, 0, 0], ![0, 1, 0]]
  ![2050, 167, 47] ![![9, 0, 0], ![2, 1, 0]] where
    su := ![![45, 0, 0], ![0, 9, 0]]
    hsu := by decide
    w := ![![18450, 1503, 423], ![11385, 927, 261]]
    hw := by decide
    g := ![![![-255, 10605, 5365], ![1126, -48283, 0]], ![![254, -10591, -5356], ![-1112, 48205, 0]]]
    h := ![![![410, 32, 0], ![7, 47, 0]], ![![253, 19, 0], ![8, 29, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {9} * I5N0 =  Ideal.span {B.equivFun.symm ![2050, 167, 47]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 9 ![![5, 0, 0], ![2, 1, 0]]
  ![11, 4, -2] ![![9, 0, 0], ![2, 1, 0]] where
    su := ![![45, 0, 0], ![18, 9, 0]]
    hsu := by decide
    w := ![![99, 36, -18], ![-288, 81, 0]]
    hw := by decide
    g := ![![![-83, -21, -10], ![-19, 72, 0]], ![![-94, -14, -6], ![-13, 34, 0]]]
    h := ![![![121, 71, 5], ![-297, -27, 0]], ![![-316, -191, -19], ![774, 95, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {9} * I5N1 =  Ideal.span {B.equivFun.symm ![11, 4, -2]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E5RS1 


noncomputable def E5RS2 : RelationCertificate Table 9 ![![5, 0, 0], ![-2, 1, 0]]
  ![934, -238, -7] ![![9, 0, 0], ![2, 1, 0]] where
    su := ![![45, 0, 0], ![-18, 9, 0]]
    hsu := by decide
    w := ![![8406, -2142, -63], ![783, 675, -252]]
    hw := by decide
    g := ![![![33163, 1821, 711], ![7574, 790, 0]], ![![10297, 706, 292], ![2370, -395, 0]]]
    h := ![![![21026, -11530, 530], ![52098, -2657, 0]], ![![131, 1661, -857], ![284, 4257, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N2 : Ideal.span {9} * I5N2 =  Ideal.span {B.equivFun.symm ![934, -238, -7]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E5RS2 


noncomputable def E7RS0 : RelationCertificate Table 9 ![![7, 0, 0], ![19, 3, 1]]
  ![26, -11, 1] ![![9, 0, 0], ![2, 1, 0]] where
    su := ![![63, 0, 0], ![171, 27, 9]]
    hsu := by decide
    w := ![![234, -99, 9], ![207, -27, -9]]
    hw := by decide
    g := ![![![-11, -1, 0], ![6, -2, 0]], ![![-56, -1, 0], ![-10, -12, 0]]]
    h := ![![![-18, -5, -1], ![8, 0, 0]], ![![-13, -3, -1], ![6, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {9} * I7N0 =  Ideal.span {B.equivFun.symm ![26, -11, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 81 ![![7, 0, 0], ![-3, 1, 0]]
  ![-226, 124, -17] ![![81, 0, 0], ![-7, 1, 0]] where
    su := ![![567, 0, 0], ![-243, 81, 0]]
    hsu := by decide
    w := ![![-18306, 10044, -1377], ![-1053, -567, 243]]
    hw := by decide
    g := ![![![-2026, -1788396, 255519], ![-21867, -20697292, 0]], ![![629, 598770, -85552], ![7403, 6929692, 0]]]
    h := ![![![-68926, 25765, -930], ![-160752, 6493, 0]], ![![-3616, 1364, -53], ![-8433, 374, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {81} * I7N1 =  Ideal.span {B.equivFun.symm ![-226, 124, -17]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E7RS1 


noncomputable def E11RS0 : RelationCertificate Table 243 ![![11, 0, 0], ![1, 1, 0]]
  ![646861, 52685, 14828] ![![243, 0, 0], ![-88, 1, 0]] where
    su := ![![2673, 0, 0], ![243, 243, 0]]
    hsu := by decide
    w := ![![157187223, 12802455, 3603204], ![-54625428, -4449087, -1252179]]
    hw := by decide
    g := ![![![2519354956, 1912219032526, -21730087063], ![6956855155, 5280411156356, 0]], ![![114516201, 86919047085, -987731232], ![316220865, 240018689348, 0]]]
    h := ![![![57849, 57849, 55364], ![10522, -594176, 0]], ![![-20104, -20104, -19240], ![-3652, 206487, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {243} * I11N0 =  Ideal.span {B.equivFun.symm ![646861, 52685, 14828]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 9 ![![11, 0, 0], ![3, 1, 0]]
  ![-1073201, -87409, -24601] ![![9, 0, 0], ![2, 1, 0]] where
    su := ![![99, 0, 0], ![27, 9, 0]]
    hsu := by decide
    w := ![![-9658809, -786681, -221409], ![-5959557, -485388, -136611]]
    hw := by decide
    g := ![![![104, -46, -31], ![20, 200, 0]], ![![-91, 23, -9], ![-14, 60, 0]]]
    h := ![![![-1044439, -349787, -10975], ![3471876, 96124, 0]], ![![-644429, -215823, -6772], ![2142182, 59313, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {9} * I11N1 =  Ideal.span {B.equivFun.symm ![-1073201, -87409, -24601]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E11RS1 


noncomputable def E11RS2 : RelationCertificate Table 243 ![![11, 0, 0], ![-4, 1, 0]]
  ![19171, -5488, 26] ![![243, 0, 0], ![-88, 1, 0]] where
    su := ![![2673, 0, 0], ![-972, 243, 0]]
    hsu := by decide
    w := ![![4658553, -1333584, 6318], ![-1683018, 501309, -7776]]
    hw := by decide
    g := ![![![37001, 13326921, -150922], ![41705, 36796024, 0]], ![![-7950, -5451187, 61925], ![-19496, -15052731, 0]]]
    h := ![![![32277, -8679, 139], ![83969, -1503, 0]], ![![-11658, 3145, -53], ![-30328, 551, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N2 : Ideal.span {243} * I11N2 =  Ideal.span {B.equivFun.symm ![19171, -5488, 26]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E11RS2 


noncomputable def E13RS0 : RelationCertificate Table 3 ![![13, 0, 0], ![15, 6, 1]]
  ![197, -59, 1] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![39, 0, 0], ![45, 18, 3]]
    hsu := by decide
    w := ![![591, -177, 3], ![-42, 225, -60]]
    hw := by decide
    g := ![![![-1129, -169, -67], ![321, 116, 0]], ![![-4257, -698, -184], ![1189, 232, 0]]]
    h := ![![![-1, -11, -1], ![14, 0, 0]], ![![-8, 3, -2], ![6, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {3} * I13N0 =  Ideal.span {B.equivFun.symm ![197, -59, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 243 ![![13, 0, 0], ![-6, 1, 0]]
  ![8, 25, -8] ![![243, 0, 0], ![-88, 1, 0]] where
    su := ![![3159, 0, 0], ![-1458, 243, 0]]
    hsu := by decide
    w := ![![1944, 6075, -1944], ![-1944, -1944, 729]]
    hw := by decide
    g := ![![![-15, -47700, 542], ![-36, -131717, 0]], ![![67, 19800, -225], ![184, 54677, 0]]]
    h := ![![![10904, -2155, 56], ![23624, -736, 0]], ![![-338, -11601, 1943], ![-731, -25256, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {243} * I13N1 =  Ideal.span {B.equivFun.symm ![8, 25, -8]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E13RS1 


noncomputable def E17RS0 : RelationCertificate Table 3 ![![17, 0, 0], ![1, 1, 0]]
  ![-66178, -5390, -1517] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![51, 0, 0], ![3, 3, 0]]
    hsu := by decide
    w := ![![-198534, -16170, -4551], ![-168957, -13761, -3873]]
    hw := by decide
    g := ![![![174, -10, -15], ![-61, 34, 0]], ![![-18, 12, -3], ![12, 1, 0]]]
    h := ![![![-3867, -3867, -3665], ![-439, 60788, 0]], ![![-3291, -3291, -3119], ![-372, 51732, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N0 : Ideal.span {3} * I17N0 =  Ideal.span {B.equivFun.symm ![-66178, -5390, -1517]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E17RS0 


noncomputable def E17RS1 : RelationCertificate Table 81 ![![17, 0, 0], ![-2, 1, 0]]
  ![-1, 7, 1] ![![81, 0, 0], ![-7, 1, 0]] where
    su := ![![1377, 0, 0], ![-162, 81, 0]]
    hsu := by decide
    w := ![![-81, 567, 81], ![162, -81, 0]]
    hw := by decide
    g := ![![![1, 119, -17], ![9, 1378, 0]], ![![7, -1, 0], ![80, 0, 0]]]
    h := ![![![-191, 98, -1], ![-1623, 18, 0]], ![![362, -183, 1], ![3076, -17, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {81} * I17N1 =  Ideal.span {B.equivFun.symm ![-1, 7, 1]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E17RS1 


noncomputable def E19RS1 : RelationCertificate Table 3 ![![19, 0, 0], ![-6, 1, 0]]
  ![-79, 40, -5] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![57, 0, 0], ![-18, 3, 0]]
    hsu := by decide
    w := ![![-237, 120, -15], ![-696, 36, 45]]
    hw := by decide
    g := ![![![8795, 1568, 236], ![-2407, -48, 0]], ![![-1132, -200, -33], ![312, 14, 0]]]
    h := ![![![-1489, 272, -4], ![-4702, 71, 0]], ![![-4324, 784, -10], ![-13654, 205, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {3} * I19N1 =  Ideal.span {B.equivFun.symm ![-79, 40, -5]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E19RS1 


noncomputable def E29RS0 : RelationCertificate Table 27 ![![29, 0, 0], ![5, 1, 0]]
  ![-13074896, -1064911, -299716] ![![27, 0, 0], ![-7, 1, 0]] where
    su := ![![783, 0, 0], ![135, 27, 0]]
    hsu := by decide
    w := ![![-353022192, -28752597, -8092332], ![45068292, 3670677, 1033101]]
    hw := by decide
    g := ![![![-190, -707, 103], ![49, -3104, 0]], ![![-88, -130, 23], ![42, -584, 0]]]
    h := ![![![-13026864, -2628807, -25712], ![72940832, 445932, 0]], ![![1663054, 335600, 3282], ![-9311874, -56915, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N0 : Ideal.span {27} * I29N0 =  Ideal.span {B.equivFun.symm ![-13074896, -1064911, -299716]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E29RS0 


noncomputable def E29RS2 : RelationCertificate Table 27 ![![29, 0, 0], ![13, 1, 0]]
  ![196484, 16003, 4504] ![![27, 0, 0], ![-7, 1, 0]] where
    su := ![![783, 0, 0], ![351, 27, 0]]
    hsu := by decide
    w := ![![5305068, 432081, 121608], ![-677268, -55161, -15525]]
    hw := by decide
    g := ![![![1751, 191497, -27394], ![6640, 739585, 0]], ![![794, 87544, -12523], ![3052, 338096, 0]]]
    h := ![![![615386, 57465, 932], ![-1357670, -22524, 0]], ![![-78570, -7350, -120], ![173342, 2905, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N2 : Ideal.span {27} * I29N2 =  Ideal.span {B.equivFun.symm ![196484, 16003, 4504]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E29RS2 


noncomputable def E31RS0 : RelationCertificate Table 81 ![![31, 0, 0], ![0, 1, 0]]
  ![16294499, 1327138, 373519] ![![81, 0, 0], ![-7, 1, 0]] where
    su := ![![2511, 0, 0], ![0, 81, 0]]
    hsu := by decide
    w := ![![1319854419, 107498178, 30255039], ![-56166048, -4574556, -1287495]]
    hw := by decide
    g := ![![![-12, 18614, -2655], ![242, 215589, 0]], ![![41, 5637, -807], ![93, 65330, 0]]]
    h := ![![![525629, 42766, 0], ![1392, 373519, 0]], ![![-22368, -1820, 0], ![-56, -15895, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N0 : Ideal.span {81} * I31N0 =  Ideal.span {B.equivFun.symm ![16294499, 1327138, 373519]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E31RS0 
