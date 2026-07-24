import IdealArithmetic.Examples.NF3_1_116424_1.PrimesBelow3_1_116424_1F1
import IdealArithmetic.Examples.NF3_1_116424_1.ClassGroupData3_1_116424_1

set_option linter.all false

noncomputable section


noncomputable def E37RS1 : RelationCertificate Table 6400 ![![37, 0, 0], ![-7, 1, 0]]
  ![155, -112, -121] ![![6400, 0, 0], ![21878, 4814, 2739]] where
    su := ![![236800, 0, 0], ![-44800, 6400, 0]]
    hsu := by decide
    w := ![![992000, -716800, -774400], ![-30956800, 3475200, 505600]]
    hw := by decide
    g := ![![![5335065624851, -9815904154560, 1075457153619], ![11314450085514, -2037069953065, 0]], ![![-1018312636512, 1873577519235, -205274251222], ![-2159607406639, 388818841147, 0]]]
    h := ![![![-89, -249, 242], ![26, -1815, 0]], ![![-61, 174, -158], ![30, 1185, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {6400} * I37N1 =  Ideal.span {B.equivFun.symm ![155, -112, -121]} * (J0 ^ 8*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8J1_2 E37RS1 


noncomputable def E41RS0 : RelationCertificate Table 1280 ![![41, 0, 0], ![-19, 1, 0]]
  ![-485, 144, 7] ![![1280, 0, 0], ![-3430, -345, -494]] where
    su := ![![52480, 0, 0], ![-24320, 1280, 0]]
    hsu := by decide
    w := ![![-620800, 184320, 8960], ![-2077440, 474880, 152320]]
    hw := by decide
    g := ![![![-7765653, 9048172, 4891376], ![16492412, -2559417, 0]], ![![3353100, -3904956, -2110855], ![-7117409, 1104621, 0]]]
    h := ![![![12091, 113880, -33473], ![-2776, 274480, 0]], ![![40313, 380167, -111741], ![-9376, 916300, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N0 : Ideal.span {1280} * I41N0 =  Ideal.span {B.equivFun.symm ![-485, 144, 7]} * (J0 ^ 8*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8J1_1 E41RS0 


noncomputable def E41RS1 : RelationCertificate Table 400 ![![41, 0, 0], ![-16, 1, 0]]
  ![-55, 32, -19] ![![400, 0, 0], ![1202, 191, 158]] where
    su := ![![16400, 0, 0], ![-6400, 400, 0]]
    hsu := by decide
    w := ![![-22000, 12800, -7600], ![112800, -26400, 29200]]
    hw := by decide
    g := ![![![2107701, -3125913, -570578], ![4616457, -784302, 0]], ![![-149749083164, 222064058286, 40531995969], ![-327950264838, 55717282405, 0]]]
    h := ![![![531, 3989, -1424], ![-95, 11673, 0]], ![![-2646, -20151, 7193], ![573, -58968, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {400} * I41N1 =  Ideal.span {B.equivFun.symm ![-55, 32, -19]} * (J0 ^ 4*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_2 E41RS1 


noncomputable def E41RS2 : RelationCertificate Table 64 ![![41, 0, 0], ![-6, 1, 0]]
  ![195, 16, 15] ![![64, 0, 0], ![18, 1, 0]] where
    su := ![![2624, 0, 0], ![-384, 64, 0]]
    hsu := by decide
    w := ![![12480, 1024, 960], ![4288, 320, 320]]
    hw := by decide
    g := ![![![-1503, 15422, 3855], ![-140, -49343, 0]], ![![173, -1901, -475], ![61, 6080, 0]]]
    h := ![![![5099, 10336, -12905], ![-464, 105824, 0]], ![![1753, 3552, -4435], ![-155, 36368, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N2 : Ideal.span {64} * I41N2 =  Ideal.span {B.equivFun.symm ![195, 16, 15]} * (J0 ^ 6*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6J1_0 E41RS2 


noncomputable def E43RS1 : RelationCertificate Table 8 ![![43, 0, 0], ![6, 1, 0]]
  ![-107, -8, -7] ![![8, 0, 0], ![2, 1, 0]] where
    su := ![![344, 0, 0], ![48, 8, 0]]
    hsu := by decide
    w := ![![-856, -64, -56], ![-576, -48, -40]]
    hw := by decide
    g := ![![![31, -73, -91], ![7, 146, 0]], ![![3334, -6671, -8338], ![4, 13341, 0]]]
    h := ![![![-59875, 241073, 150631], ![-2723, -1295428, 0]], ![![-40278, 162179, 101335], ![-1847, -871482, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {8} * I43N1 =  Ideal.span {B.equivFun.symm ![-107, -8, -7]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E43RS1 


noncomputable def E59RS1 : RelationCertificate Table 80 ![![59, 0, 0], ![-16, 1, 0]]
  ![-435, -32, -31] ![![80, 0, 0], ![-330, -60, -39]] where
    su := ![![4720, 0, 0], ![-1280, 80, 0]]
    hsu := by decide
    w := ![![-34800, -2560, -2480], ![261600, 19440, 17280]]
    hw := by decide
    g := ![![![-21511733681, 47291553358, -985838239], ![53747832804, -9797443867, 0]], ![![5833690632, -12824827836, 267345985], ![-14575683245, 2656933898, 0]]]
    h := ![![![727779, 5300369, -1892339], ![-107487, 22329594, 0]], ![![-5470434, -39841428, 14224194], ![808251, -167845446, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {80} * I59N1 =  Ideal.span {B.equivFun.symm ![-435, -32, -31]} * (J0 ^ 4*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_1 E59RS1 


noncomputable def E67RS0 : RelationCertificate Table 1600 ![![67, 0, 0], ![-28, 1, 0]]
  ![-1985, -176, -133] ![![1600, 0, 0], ![-6386, -1148, -787]] where
    su := ![![107200, 0, 0], ![-44800, 1600, 0]]
    hsu := by decide
    w := ![![-3176000, -281600, -212800], ![24019200, 1696000, 1688000]]
    hw := by decide
    g := ![![![-8732475, 18711065, 745831], ![21089091, -3697500, 0]], ![![-46147768194618, 98804262760886, 3934555998042], ![111359911571456, -19525914740727, 0]]]
    h := ![![![-321008071, -4535181201, 871959461], ![66463387, -11684256804, 0]], ![![2428492620, 34309584652, -6596553835], ![-502809024, 88393821600, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N0 : Ideal.span {1600} * I67N0 =  Ideal.span {B.equivFun.symm ![-1985, -176, -133]} * (J0 ^ 6*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6J1_2 E67RS0 


noncomputable def E67RS1 : RelationCertificate Table 10 ![![67, 0, 0], ![-21, 1, 0]]
  ![-15, 2, 1] ![![10, 0, 0], ![8, 4, 1]] where
    su := ![![670, 0, 0], ![-210, 10, 0]]
    hsu := by decide
    w := ![![-150, 20, 10], ![150, -90, 10]]
    hw := by decide
    g := ![![![7551203, -1540493, 4200011], ![5844768, -2658049, 0]], ![![-2377588, 485039, -1322422], ![-1840285, 836917, 0]]]
    h := ![![![-14131, -141197, 37148], ![2324, -497783, 0]], ![![14271, 142485, -37487], ![-2310, 502326, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {10} * I67N1 =  Ideal.span {B.equivFun.symm ![-15, 2, 1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E67RS1 


noncomputable def E67RS2 : RelationCertificate Table 4 ![![67, 0, 0], ![-18, 1, 0]]
  ![9, 0, 1] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![268, 0, 0], ![-72, 4, 0]]
    hsu := by decide
    w := ![![36, 0, 4], ![72, -4, 0]]
    hw := by decide
    g := ![![![-79789, 159579, 199474], ![4, -159579, 0]], ![![21418, -42841, -53550], ![3, 42840, 0]]]
    h := ![![![-1701, -14254, 4453], ![298, -59670, 0]], ![![-3426, -28568, 8925], ![535, -119595, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N2 : Ideal.span {4} * I67N2 =  Ideal.span {B.equivFun.symm ![9, 0, 1]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E67RS2 


noncomputable def E71RS0 : RelationCertificate Table 50 ![![71, 0, 0], ![9, 1, 0]]
  ![-65, -4, -7] ![![50, 0, 0], ![-14, -7, -2]] where
    su := ![![3550, 0, 0], ![450, 50, 0]]
    hsu := by decide
    w := ![![-3250, -200, -350], ![3400, 50, 100]]
    hw := by decide
    g := ![![![-6545, 123, -2261], ![1958, -3773, 0]], ![![-1237, 25, -428], ![383, -715, 0]]]
    h := ![![![50972, -282157, -128237], ![2539, 1820964, 0]], ![![-53648, 296920, 134947], ![-2602, -1916247, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N0 : Ideal.span {50} * I71N0 =  Ideal.span {B.equivFun.symm ![-65, -4, -7]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E71RS0 


noncomputable def E71RS1 : RelationCertificate Table 3200 ![![71, 0, 0], ![25, 1, 0]]
  ![-2255, -208, -139] ![![3200, 0, 0], ![10950, 2505, 1454]] where
    su := ![![227200, 0, 0], ![80000, 3200, 0]]
    hsu := by decide
    w := ![![-7216000, -665600, -444800], ![-51104000, -3744000, -3881600]]
    hw := by decide
    g := ![![![-105608942999253754977, 198718799659283343271, -12404306883653162746], ![-211457248407548571419, 36097808174302354542, 0]], ![![-37186540224811424431, 69971959069871568538, -4367748069338531200], ![-74457363651398446379, 12710595879278011945, 0]]]
    h := ![![![-738494765, 10504073232, 1944906391], ![-112088620, -27617670780, 0]], ![![-5231890420, 74416453408, 13778753497], ![-794095838, -195658299900, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {3200} * I71N1 =  Ideal.span {B.equivFun.symm ![-2255, -208, -139]} * (J0 ^ 7*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7J1_2 E71RS1 


noncomputable def E71RS2 : RelationCertificate Table 50 ![![71, 0, 0], ![-34, 1, 0]]
  ![-635, -46, -43] ![![50, 0, 0], ![-14, -7, -2]] where
    su := ![![3550, 0, 0], ![-1700, 50, 0]]
    hsu := by decide
    w := ![![-31750, -2300, -2150], ![26200, 2000, 1750]]
    hw := by decide
    g := ![![![-26224167, 466054, -9048249], ![7639479, -15086820, 0]], ![![-117109761466, 2081249837, -40406931194], ![34115635524, -67373478411, 0]]]
    h := ![![![7737, 137191, -21433], ![-1727, 304340, 0]], ![![-6362, -113201, 17685], ![1471, -251120, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N2 : Ideal.span {50} * I71N2 =  Ideal.span {B.equivFun.symm ![-635, -46, -43]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E71RS2 


noncomputable def E73RS1 : RelationCertificate Table 25 ![![73, 0, 0], ![19, 1, 0]]
  ![-165, -14, -12] ![![25, 0, 0], ![2, 1, 1]] where
    su := ![![1825, 0, 0], ![475, 25, 0]]
    hsu := by decide
    w := ![![-4125, -350, -300], ![-1250, -75, -75]]
    hw := by decide
    g := ![![![-29665181, 5254346, -1632604], ![-2228344, 14347812, 0]], ![![-7721167, 1367585, -424930], ![-579970, 3734406, 0]]]
    h := ![![![-392461, 4241578, 1009756], ![-43968, -14742440, 0]], ![![-118997, 1285966, 306139], ![-13291, -4469630, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {25} * I73N1 =  Ideal.span {B.equivFun.symm ![-165, -14, -12]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E73RS1 


noncomputable def E79RS0 : RelationCertificate Table 40 ![![79, 0, 0], ![10, 1, 0]]
  ![15, -8, 11] ![![40, 0, 0], ![110, 25, 14]] where
    su := ![![3160, 0, 0], ![400, 40, 0]]
    hsu := by decide
    w := ![![600, -320, 440], ![5000, -560, -1600]]
    hw := by decide
    g := ![![![-4307994787452056, 6064898487936267, -824153461167135], ![-8344877821941321, 1544272453132618, 0]], ![![-545271604611700, 767646455830545, -104314768793552], ![-1056228046865784, 195461684617145, 0]]]
    h := ![![![-10081, 60843, 25349], ![-461, -400512, 0]], ![![-79823, 481995, 200810], ![-3947, -3172806, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N0 : Ideal.span {40} * I79N0 =  Ideal.span {B.equivFun.symm ![15, -8, 11]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E79RS0 


noncomputable def E79RS1 : RelationCertificate Table 16 ![![79, 0, 0], ![34, 1, 0]]
  ![-7, 0, -3] ![![16, 0, 0], ![2, 1, 0]] where
    su := ![![1264, 0, 0], ![544, 16, 0]]
    hsu := by decide
    w := ![![-112, 0, -48], ![-176, 32, 0]]
    hw := by decide
    g := ![![![457426, -914866, -1143581], ![15, 3659458, 0]], ![![1256044, -2512095, -3140118], ![8, 10048377, 0]]]
    h := ![![![1399, -27558, -3827], ![306, 60466, 0]], ![![2263, -44430, -6170], ![476, 97486, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {16} * I79N1 =  Ideal.span {B.equivFun.symm ![-7, 0, -3]} * (J0 ^ 4*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_0 E79RS1 


noncomputable def E79RS2 : RelationCertificate Table 100 ![![79, 0, 0], ![35, 1, 0]]
  ![5, 8, -11] ![![100, 0, 0], ![-206, -33, -22]] where
    su := ![![7900, 0, 0], ![3500, 100, 0]]
    hsu := by decide
    w := ![![500, 800, -1100], ![400, -900, -2200]]
    hw := by decide
    g := ![![![2062106273, -1391457725, 230665293], ![-3839504084, 888724125, 0]], ![![965982377, -651820617, 108053891], ![-1798594285, 416317879, 0]]]
    h := ![![![62880, -1261547, -170459], ![11971, 2693250, 0]], ![![53146, -1066044, -144043], ![10092, 2275875, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N2 : Ideal.span {100} * I79N2 =  Ideal.span {B.equivFun.symm ![5, 8, -11]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E79RS2 
