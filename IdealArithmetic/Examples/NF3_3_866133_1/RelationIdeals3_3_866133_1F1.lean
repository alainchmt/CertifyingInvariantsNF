import IdealArithmetic.Examples.NF3_3_866133_1.PrimesBelow3_3_866133_1F1
import IdealArithmetic.Examples.NF3_3_866133_1.ClassGroupData3_3_866133_1

set_option linter.all false

noncomputable section


noncomputable def E41RS0 : RelationCertificate Table 32 ![![41, 0, 0], ![0, 1, 0]]
  ![-363, -37, 12] ![![32, 0, 0], ![-10, 1, 0]] where
    su := ![![1312, 0, 0], ![0, 32, 0]]
    hsu := by decide
    w := ![![-11616, -1184, 384], ![7744, 800, -256]]
    hw := by decide
    g := ![![![-17729676429649, 112811949365802, -41125548410784], ![9065897301949, 329004386294590, -440748]], ![![2, 0, 0], ![3, 0, 0]]]
    h := ![![![22869, -11434, 45756], ![-239, -468996, 0]], ![![-15246, 7622, -30504], ![187, 312664, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N0 : Ideal.span {32} * I41N0 =  Ideal.span {B.equivFun.symm ![-363, -37, 12]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E41RS0 


noncomputable def E41RS1 : RelationCertificate Table 4 ![![41, 0, 0], ![3, 1, 0]]
  ![3, 1, 0] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![164, 0, 0], ![12, 4, 0]]
    hsu := by decide
    w := ![![12, 4, 0], ![8, 4, 4]]
    hw := by decide
    g := ![![![7380752, 714309, 80074], ![3868958, 0, -106765]], ![![543370, 52587, 5895], ![284832, 0, -7860]]]
    h := ![![![-306, -306, -612], ![1, 6273, 0]], ![![-203, -202, -403], ![21, 4131, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {4} * I41N1 =  Ideal.span {B.equivFun.symm ![3, 1, 0]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E41RS1 


noncomputable def E41RS2 : RelationCertificate Table 32 ![![41, 0, 0], ![-3, 1, 0]]
  ![-129, -15, 4] ![![32, 0, 0], ![-10, 1, 0]] where
    su := ![![1312, 0, 0], ![-96, 32, 0]]
    hsu := by decide
    w := ![![-4128, -480, 128], ![2656, 288, -96]]
    hw := by decide
    g := ![![![-234742776, 1493649804, -544509349], ![120033680, 4356074513, -123]], ![![19083482, -121426666, 44266035], ![-9758149, -354128257, 10]]]
    h := ![![![-2013, 4053, -4060], ![276, 41616, 0]], ![![1297, -2609, 2613], ![-158, -26784, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N2 : Ideal.span {32} * I41N2 =  Ideal.span {B.equivFun.symm ![-129, -15, 4]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E41RS2 


noncomputable def E43RS1 : RelationCertificate Table 2 ![![43, 0, 0], ![9, 1, 0]]
  ![9, 1, 0] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![86, 0, 0], ![18, 2, 0]]
    hsu := by decide
    w := ![![18, 2, 0], ![2, 8, 4]]
    hw := by decide
    g := ![![![1611376, 232698, 4616], ![116351, 0, -9234]], ![![358075, 51710, 1026], ![25856, 0, -2052]]]
    h := ![![![-140, -560, -280], ![1, 3010, 0]], ![![-13, -52, -26], ![0, 280, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {2} * I43N1 =  Ideal.span {B.equivFun.symm ![9, 1, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E43RS1 


noncomputable def E47RS0 : RelationCertificate Table 2 ![![47, 0, 0], ![16, 1, 0]]
  ![523, 19, -10] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![94, 0, 0], ![32, 2, 0]]
    hsu := by decide
    w := ![![1046, 38, -20], ![-3452, -126, 66]]
    hw := by decide
    g := ![![![-2512609, -362855, -7201], ![-181426, 0, 14399]], ![![-881056, -127236, -2525], ![-63618, 0, 5049]]]
    h := ![![![1177, 10375, 2770], ![644, -32550, 0]], ![![-3908, -34239, -9141], ![-2055, 107415, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N0 : Ideal.span {2} * I47N0 =  Ideal.span {B.equivFun.symm ![523, 19, -10]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E47RS0 


noncomputable def E47RS1 : RelationCertificate Table 16 ![![47, 0, 0], ![-12, 1, 0]]
  ![-347, -37, 12] ![![16, 0, 0], ![6, 1, 0]] where
    su := ![![752, 0, 0], ![-192, 16, 0]]
    hsu := by decide
    w := ![![-5552, -592, 192], ![2032, 224, -64]]
    hw := by decide
    g := ![![![-1838947916086, -5501657419197, -4452999475489], ![-1033459057222, 17811998280833, -216504]], ![![408655091898, 1222590535947, 989555437661], ![229657567967, -3958221834838, 48112]]]
    h := ![![![-420473, 3014002, -928508], ![171505, 10909972, 0]], ![![153883, -1103015, 339800], ![-62744, -3992651, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {16} * I47N1 =  Ideal.span {B.equivFun.symm ![-347, -37, 12]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E47RS1 


noncomputable def E47RS2 : RelationCertificate Table 2 ![![47, 0, 0], ![-4, 1, 0]]
  ![83, 5, -2] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![94, 0, 0], ![-8, 2, 0]]
    hsu := by decide
    w := ![![166, 10, -4], ![-688, -48, 18]]
    hw := by decide
    g := ![![![-24570, -3548, -69], ![-1773, 0, 141]], ![![2626, 379, 8], ![191, 0, -15]]]
    h := ![![![613, -1541, 1234], ![-68, -14500, 0]], ![![-2532, 6383, -5113], ![375, 60080, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N2 : Ideal.span {2} * I47N2 =  Ideal.span {B.equivFun.symm ![83, 5, -2]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E47RS2 


noncomputable def E53RS0 : RelationCertificate Table 8 ![![53, 0, 0], ![21, 1, 0]]
  ![-183, -9, 4] ![![8, 0, 0], ![-2, 1, 0]] where
    su := ![![424, 0, 0], ![168, 8, 0]]
    hsu := by decide
    w := ![![-1464, -72, 32], ![1744, 96, -40]]
    hw := by decide
    g := ![![![-9793510980962516, 15796370962483153, -21798929117814754], ![4422924115551026, 43597856962101285, -5094112895]], ![![-3695669129714688, 5960902136225824, -8226021245919816], ![1669030049456901, 16452042011262345, -1922309150]]]
    h := ![![![-6096, -76088, -15232], ![-3845, 201825, 0]], ![![7255, 90629, 18143], ![4595, -240396, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N0 : Ideal.span {8} * I53N0 =  Ideal.span {B.equivFun.symm ![-183, -9, 4]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E53RS0 


noncomputable def E53RS1 : RelationCertificate Table 8 ![![53, 0, 0], ![-16, 1, 0]]
  ![-115, -13, 4] ![![8, 0, 0], ![-2, 1, 0]] where
    su := ![![424, 0, 0], ![-128, 8, 0]]
    hsu := by decide
    w := ![![-920, -104, 32], ![1600, 176, -56]]
    hw := by decide
    g := ![![![-13814831958109576, 22282735158753169, -30750052627538171], ![6239049884371545, 61500102783633900, -9885769765]], ![![4431167914313685, -7147284988917659, 9863214187460159], ![-2001202602193123, -19726427582194320, 3170903991]]]
    h := ![![![-2919, 28448, -6700], ![1435, 88776, 0]], ![![5088, -49479, 11653], ![-2459, -154404, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {8} * I53N1 =  Ideal.span {B.equivFun.symm ![-115, -13, 4]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E53RS1 


noncomputable def E59RS1 : RelationCertificate Table 4 ![![59, 0, 0], ![15, 1, 0]]
  ![15, 1, 0] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![236, 0, 0], ![60, 4, 0]]
    hsu := by decide
    w := ![![60, 4, 0], ![32, 16, 4]]
    hw := by decide
    g := ![![![12234, 1183, 133], ![6415, 0, -177]], ![![3042, 294, 33], ![1596, 0, -44]]]
    h := ![![![5, 139, 40], ![60, -590, 0]], ![![2, 66, 19], ![30, -280, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {4} * I59N1 =  Ideal.span {B.equivFun.symm ![15, 1, 0]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E59RS1 


noncomputable def E61RS1 : RelationCertificate Table 2 ![![61, 0, 0], ![5, 1, 0]]
  ![5, 1, 0] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![122, 0, 0], ![10, 2, 0]]
    hsu := by decide
    w := ![![10, 2, 0], ![2, 4, 4]]
    hw := by decide
    g := ![![![2289732, 330673, 6562], ![165337, 0, -13122]], ![![254422, 36741, 729], ![18372, 0, -1458]]]
    h := ![![![187, 383, 384], ![62, -5856, 0]], ![![32, 73, 74], ![61, -1128, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {2} * I61N1 =  Ideal.span {B.equivFun.symm ![5, 1, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E61RS1 


noncomputable def E67RS0 : RelationCertificate Table 32 ![![67, 0, 0], ![8, 1, 0]]
  ![-113, 1, 4] ![![32, 0, 0], ![-10, 1, 0]] where
    su := ![![2144, 0, 0], ![256, 32, 0]]
    hsu := by decide
    w := ![![-3616, 32, 128], ![2528, 128, -32]]
    hw := by decide
    g := ![![![-544728914, 3498015317, -1274969719], ![279540780, 10198658004, -488775]], ![![-66896536, 429580832, -156575230], ![34329572, 1252466784, -60025]]]
    h := ![![![-2779, -9912, -5668], ![-475, 94940, 0]], ![![1933, 6919, 3957], ![391, -66280, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N0 : Ideal.span {32} * I67N0 =  Ideal.span {B.equivFun.symm ![-113, 1, 4]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E67RS0 


noncomputable def E67RS1 : RelationCertificate Table 32 ![![67, 0, 0], ![22, 1, 0]]
  ![537, 119, 28] ![![32, 0, 0], ![-10, 1, 0]] where
    su := ![![2144, 0, 0], ![704, 32, 0]]
    hsu := by decide
    w := ![![17184, 3808, 896], ![4640, 992, 224]]
    hw := by decide
    g := ![![![62583838, -396544608, 144572197], ![-31949460, -1156635003, -25527]], ![![20238565, -128235819, 46752203], ![-10331899, -374036196, -8255]]]
    h := ![![![4381, 53642, 10224], ![2250, -171245, 0]], ![![1181, 14486, 2761], ![614, -46245, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {32} * I67N1 =  Ideal.span {B.equivFun.symm ![537, 119, 28]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E67RS1 


noncomputable def E67RS2 : RelationCertificate Table 4 ![![67, 0, 0], ![-30, 1, 0]]
  ![315, 69, 16] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![268, 0, 0], ![-120, 4, 0]]
    hsu := by decide
    w := ![![1260, 276, 64], ![6352, 1392, 324]]
    hw := by decide
    g := ![![![13643, 1366, 156], ![7167, 0, -201]], ![![-6157, -621, -71], ![-3233, 0, 91]]]
    h := ![![![633, -12577, 1624], ![-410, -27198, 0]], ![![3106, -63401, 8187], ![-2257, -137112, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N2 : Ideal.span {4} * I67N2 =  Ideal.span {B.equivFun.symm ![315, 69, 16]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E67RS2 


noncomputable def E71RS0 : RelationCertificate Table 8 ![![71, 0, 0], ![14, 1, 0]]
  ![293, 3, -4] ![![8, 0, 0], ![-2, 1, 0]] where
    su := ![![568, 0, 0], ![112, 8, 0]]
    hsu := by decide
    w := ![![2344, 24, -32], ![-1976, 32, 16]]
    hw := by decide
    g := ![![![1004279343, -1619786265, 2235308156], ![-453543116, -4470616381, -254]], ![![213507078, -344362211, 475220507], ![-96422043, -950441030, -54]]]
    h := ![![![17497, 120294, 37036], ![5199, -657390, 0]], ![![-14773, -101450, -31234], ![-4298, 554404, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N0 : Ideal.span {8} * I71N0 =  Ideal.span {B.equivFun.symm ![293, 3, -4]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E71RS0 


noncomputable def E71RS2 : RelationCertificate Table 8 ![![71, 0, 0], ![-33, 1, 0]]
  ![-123, -13, 4] ![![8, 0, 0], ![-2, 1, 0]] where
    su := ![![568, 0, 0], ![-264, 8, 0]]
    hsu := by decide
    w := ![![-984, -104, 32], ![1616, 168, -56]]
    hw := by decide
    g := ![![![-2636367930, 4252223745, -5868065924], ![1190619954, 11736131792, -231]], ![![1186937272, -1914422783, 2641902160], ![-536037165, -5283804295, 104]]]
    h := ![![![-58516, 1361148, -160212], ![46455, 2843764, 0]], ![![96187, -2235474, 263123], ![-76115, -4670435, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N2 : Ideal.span {8} * I71N2 =  Ideal.span {B.equivFun.symm ![-123, -13, 4]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E71RS2 


noncomputable def E73RS0 : RelationCertificate Table 8 ![![73, 0, 0], ![4, 1, 0]]
  ![633, 23, -12] ![![8, 0, 0], ![-2, 1, 0]] where
    su := ![![584, 0, 0], ![32, 8, 0]]
    hsu := by decide
    w := ![![5064, 184, -96], ![-5408, -192, 104]]
    hw := by decide
    g := ![![![476248626, -768656781, 1060662643], ![-215144249, -2121323586, 6789]], ![![23921194, -38608368, 53275343], ![-10806338, -106550601, 341]]]
    h := ![![![14245, 21432, 28596], ![1127, -521880, 0]], ![![-15216, -22889, -30539], ![-1147, 557340, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N0 : Ideal.span {8} * I73N0 =  Ideal.span {B.equivFun.symm ![633, 23, -12]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E73RS0 


noncomputable def E73RS1 : RelationCertificate Table 8 ![![73, 0, 0], ![28, 1, 0]]
  ![361, 39, -12] ![![8, 0, 0], ![-2, 1, 0]] where
    su := ![![584, 0, 0], ![224, 8, 0]]
    hsu := by decide
    w := ![![2888, 312, -96], ![-4832, -512, 168]]
    hw := by decide
    g := ![![![29814572146, -48088533891, 66362093037], ![-13464709767, -132724184364, 6789]], ![![11299586850, -18225334952, 25150930501], ![-5103063576, -50301860355, 2573]]]
    h := ![![![274895, 4579867, 678840], ![168239, -12388833, 0]], ![![-460008, -7662981, -1135827], ![-281347, 20728848, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {8} * I73N1 =  Ideal.span {B.equivFun.symm ![361, 39, -12]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E73RS1 


noncomputable def E79RS1 : RelationCertificate Table 2 ![![79, 0, 0], ![-2, 1, 0]]
  ![-525, -19, 10] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![158, 0, 0], ![-4, 2, 0]]
    hsu := by decide
    w := ![![-1050, -38, 20], ![3452, 124, -66]]
    hw := by decide
    g := ![![![41446, 5979, 115], ![2991, 0, -237]], ![![-1588, -229, -4], ![-113, 0, 9]]]
    h := ![![![-20181, 30284, -40394], ![897, 797784, 0]], ![![66350, -99564, 132801], ![-2866, -2622828, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {2} * I79N1 =  Ideal.span {B.equivFun.symm ![-525, -19, 10]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E79RS1 
