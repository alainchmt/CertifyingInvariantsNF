import IdealArithmetic.Examples.NF3_1_387059_1.PrimesBelow3_1_387059_1F2
import IdealArithmetic.Examples.NF3_1_387059_1.ClassGroupData3_1_387059_1

set_option linter.all false

noncomputable section


noncomputable def E83RS1 : RelationCertificate Table 4 ![![83, 0, 0], ![27, 1, 0]]
  ![2, -3, 0] ![![4, 0, 0], ![-1, 1, 0]] where
    su := ![![332, 0, 0], ![108, 4, 0]]
    hsu := by decide
    w := ![![8, -12, 0], ![-8, 8, -12]]
    hw := by decide
    g := ![![![50, 65, 0], ![7, 0, 9]], ![![17, 21, 0], ![5, 0, 3]]]
    h := ![![![-39, -520, -80], ![-3, 1660, 0]], ![![19, 513, 79], ![63, -1640, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {4} * I83N1 =  Ideal.span {B.equivFun.symm ![2, -3, 0]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E83RS1 


noncomputable def E97RS1 : RelationCertificate Table 128 ![![97, 0, 0], ![-31, 1, 0]]
  ![378, -11, 12] ![![128, 0, 0], ![-9, 1, 0]] where
    su := ![![12416, 0, 0], ![-3968, 128, 0]]
    hsu := by decide
    w := ![![48384, -1408, 1536], ![-3328, 128, -128]]
    hw := by decide
    g := ![![![6653472271, -33492987213, 13351718008], ![-729486169, -427818000510, -321728145]], ![![-2126377965, 10703997465, -4267065067], ![233136055, 136726018623, 102820845]]]
    h := ![![![-2079565, 38700716, -4838960], ![1063593, 117344783, 0]], ![![143105, -2662950, 332963], ![-73145, -8074353, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {128} * I97N1 =  Ideal.span {B.equivFun.symm ![378, -11, 12]} * (J0 ^ 7) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7 E97RS1 


noncomputable def E101RS1 : RelationCertificate Table 512 ![![101, 0, 0], ![-43, 1, 0]]
  ![-54, -35, -20] ![![512, 0, 0], ![119, 1, 0]] where
    su := ![![51712, 0, 0], ![-22016, 512, 0]]
    hsu := by decide
    w := ![![-27648, -17920, -10240], ![-6656, -3584, -2560]]
    hw := by decide
    g := ![![![597726162085, 38193418799740, 1294706299511], ![213521156882, -165722406327404, -331]], ![![-251005953508, -16038741667870, -543692094769], ![-89664941656, 69592588126231, 139]]]
    h := ![![![-2265794, 64884745, -5900060], ![1607160, 148976510, 0]], ![![-546559, 15652515, -1423305], ![387778, 35938450, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {512} * I101N1 =  Ideal.span {B.equivFun.symm ![-54, -35, -20]} * (J0 ^ 9) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_9 E101RS1 


noncomputable def E103RS0 : RelationCertificate Table 512 ![![103, 0, 0], ![3, 1, 0]]
  ![6986, -99, 236] ![![512, 0, 0], ![119, 1, 0]] where
    su := ![![52736, 0, 0], ![1536, 512, 0]]
    hsu := by decide
    w := ![![3576832, -50688, 120832], ![833024, -11776, 28160]]
    hw := by decide
    g := ![![![407667, 26052138, 883035], ![145824, -113040917, 411]], ![![12829, 824135, 27934], ![4902, -3575946, 13]]]
    h := ![![![492912566, 493284263, 986940296], ![19145938, -25413712563, 0]], ![![114796499, 114883065, 229852713], ![4458974, -5918707346, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N0 : Ideal.span {512} * I103N0 =  Ideal.span {B.equivFun.symm ![6986, -99, 236]} * (J0 ^ 9) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_9 E103RS0 


noncomputable def E103RS2 : RelationCertificate Table 4 ![![103, 0, 0], ![-46, 1, 0]]
  ![-2, 9, 0] ![![4, 0, 0], ![-1, 1, 0]] where
    su := ![![412, 0, 0], ![-184, 4, 0]]
    hsu := by decide
    w := ![![-8, 36, 0], ![20, -20, 36]]
    hw := by decide
    g := ![![![-918417, 4352176, -156033], ![1317650, 0, 624213]], ![![407108, -1929197, 69165], ![-584076, 0, -276696]]]
    h := ![![![-552, 18466, -1572], ![524, 40479, 0]], ![![1405, -43030, 3663], ![-955, -94320, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N2 : Ideal.span {4} * I103N2 =  Ideal.span {B.equivFun.symm ![-2, 9, 0]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E103RS2 


noncomputable def E107RS1 : RelationCertificate Table 8 ![![107, 0, 0], ![52, 1, 0]]
  ![350, -5, 12] ![![8, 0, 0], ![-1, 1, 0]] where
    su := ![![856, 0, 0], ![416, 8, 0]]
    hsu := by decide
    w := ![![2800, -40, 96], ![-264, 0, -8]]
    hw := by decide
    g := ![![![-1569729310, 1569606937, -3237646316], ![392417036, 6475303758, -44499]], ![![-1207433778, 1207339645, -2490393408], ![301846680, 4980795374, -34230]]]
    h := ![![![-132912, -4736171, -371544], ![-108763, 9938805, 0]], ![![12523, 446371, 35017], ![10258, -936705, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {8} * I107N1 =  Ideal.span {B.equivFun.symm ![350, -5, 12]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E107RS1 


noncomputable def E109RS0 : RelationCertificate Table 4 ![![109, 0, 0], ![-47, 1, 0]]
  ![2, -7, 0] ![![4, 0, 0], ![-1, 1, 0]] where
    su := ![![436, 0, 0], ![-188, 4, 0]]
    hsu := by decide
    w := ![![8, -28, 0], ![-16, 16, -28]]
    hw := by decide
    g := ![![![1205648, -5708137, 204687], ![-1728443, 0, -818699]], ![![-519886, 2461404, -88263], ![745323, 0, 353031]]]
    h := ![![![665, -20540, 1712], ![-443, -46652, 0]], ![![-1245, 39195, -3267], ![901, 89024, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N0 : Ideal.span {4} * I109N0 =  Ideal.span {B.equivFun.symm ![2, -7, 0]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E109RS0 


noncomputable def E109RS1 : RelationCertificate Table 128 ![![109, 0, 0], ![-16, 1, 0]]
  ![-1258, 19, -44] ![![128, 0, 0], ![-9, 1, 0]] where
    su := ![![13952, 0, 0], ![-2048, 128, 0]]
    hsu := by decide
    w := ![![-161024, 2432, -5632], ![11008, -128, 384]]
    hw := by decide
    g := ![![![58944465429235282, -296944468569598010, 118797988731314740], ![-6464411386193081, -3801535639191114582, 120546915]], ![![-8652648029996058, 43589435450416515, -17438739594602857], ![948931779065502, 558039666996324352, -17695470]]]
    h := ![![![10562722, -92757493, 21830476], ![-2401438, -594880482, 0]], ![![-722014, 6340484, -1492233], ![164193, 40663350, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {128} * I109N1 =  Ideal.span {B.equivFun.symm ![-1258, 19, -44]} * (J0 ^ 7) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7 E109RS1 


noncomputable def E113RS1 : RelationCertificate Table 128 ![![113, 0, 0], ![-26, 1, 0]]
  ![-6, -11, 12] ![![128, 0, 0], ![-9, 1, 0]] where
    su := ![![14464, 0, 0], ![-3328, 128, 0]]
    hsu := by decide
    w := ![![-768, -1408, 1536], ![128, -256, -128]]
    hw := by decide
    g := ![![![53426, -269155, 107651], ![-5814, -3445182, -195]], ![![-12051, 60721, -24286], ![1338, 777231, 44]]]
    h := ![![![54, -513, 76], ![70, -2144, 0]], ![![9, 114, -17], ![76, 480, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {128} * I113N1 =  Ideal.span {B.equivFun.symm ![-6, -11, 12]} * (J0 ^ 7) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7 E113RS1 


noncomputable def E127RS0 : RelationCertificate Table 16 ![![127, 0, 0], ![58, 1, 0]]
  ![6, -13, 4] ![![16, 0, 0], ![7, 1, 0]] where
    su := ![![2032, 0, 0], ![928, 16, 0]]
    hsu := by decide
    w := ![![96, -208, 64], ![48, -192, -16]]
    hw := by decide
    g := ![![![796793139694, 3065624123057, 2066259527746], ![540198506312, -8265035825250, -1015875]], ![![382460707048, 1471499579067, 991804573318], ![259295283036, -3967217196120, -487620]]]
    h := ![![![-6822, -259767, -18232], ![-5023, 578867, 0]], ![![-3529, -134827, -9463], ![-2633, 300450, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N0 : Ideal.span {16} * I127N0 =  Ideal.span {B.equivFun.symm ![6, -13, 4]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E127RS0 


noncomputable def E127RS1 : RelationCertificate Table 32 ![![127, 0, 0], ![-49, 1, 0]]
  ![14, -1, 4] ![![32, 0, 0], ![-9, 1, 0]] where
    su := ![![4064, 0, 0], ![-1568, 32, 0]]
    hsu := by decide
    w := ![![448, -32, 128], ![-96, -96, -32]]
    hw := by decide
    g := ![![![688007397, -3869860746, 1547077990], ![-314435214, -12390761703, -8078735]], ![![-261636606, 1471637182, -588325432], ![119573988, 4711979796, 3072195]]]
    h := ![![![272, -7549, 604], ![-78, -19176, 0]], ![![-45, 1587, -127], ![48, 4032, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N1 : Ideal.span {32} * I127N1 =  Ideal.span {B.equivFun.symm ![14, -1, 4]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E127RS1 


noncomputable def E127RS2 : RelationCertificate Table 4 ![![127, 0, 0], ![-10, 1, 0]]
  ![-10, 1, 0] ![![4, 0, 0], ![-1, 1, 0]] where
    su := ![![508, 0, 0], ![-40, 4, 0]]
    hsu := by decide
    w := ![![-40, 4, 0], ![12, -12, 4]]
    hw := by decide
    g := ![![![431, -2100, 75], ![-632, 0, -301]], ![![-28, 139, -5], ![44, 0, 20]]]
    h := ![![![2704, -14980, 5448], ![-253, -172974, 0]], ![![-819, 4599, -1673], ![222, 53118, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N2 : Ideal.span {4} * I127N2 =  Ideal.span {B.equivFun.symm ![-10, 1, 0]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E127RS2 
