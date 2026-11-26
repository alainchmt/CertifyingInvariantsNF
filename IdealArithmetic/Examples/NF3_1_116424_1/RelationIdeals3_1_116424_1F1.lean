import IdealArithmetic.Examples.NF3_1_116424_1.PrimesBelow3_1_116424_1F1
import IdealArithmetic.Examples.NF3_1_116424_1.ClassGroupData3_1_116424_1

set_option linter.all false

noncomputable section


noncomputable def E37RS1 : RelationCertificate Table 6400 ![![37, 0, 0], ![-7, 1, 0]]
  ![155, -112, -121] ![![6400, 0, 0], ![-4250, 2170, -889]] where
    su := ![![236800, 0, 0], ![-44800, 6400, 0]]
    hsu := by decide
    w := ![![992000, -716800, -774400], ![-13062400, 4166400, -1696000]]
    hw := by decide
    g := ![![![24855247, -2497859, -10737240], ![-15851058, 4325843, 0]], ![![-4688122, 470334, 2026484], ![2993985, -816269, 0]]]
    h := ![![![-89, -249, 242], ![26, -1815, 0]], ![![-260, -521, 530], ![53, -3975, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {6400} * I37N1 =  Ideal.span {B.equivFun.symm ![155, -112, -121]} * (J0 ^ 8*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8J1_2 E37RS1 


noncomputable def E41RS0 : RelationCertificate Table 1280 ![![41, 0, 0], ![-19, 1, 0]]
  ![-485, 144, 7] ![![1280, 0, 0], ![3430, 705, 406]] where
    su := ![![52480, 0, 0], ![-24320, 1280, 0]]
    hsu := by decide
    w := ![![-620800, 184320, 8960], ![1448960, -423680, 176640]]
    hw := by decide
    g := ![![![1800732552851, -2280862214090, 375365839951], ![3688205726892, -729037891727, 0]], ![![-738179225683, 935000091099, -153874746427], ![-1511916269759, 298856498691, 0]]]
    h := ![![![12091, 113880, -33473], ![-2776, 274480, 0]], ![![-28156, -265759, 78118], ![6608, -640540, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N0 : Ideal.span {1280} * I41N0 =  Ideal.span {B.equivFun.symm ![-485, 144, 7]} * (J0 ^ 8*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8J1_1 E41RS0 


noncomputable def E41RS1 : RelationCertificate Table 400 ![![41, 0, 0], ![-16, 1, 0]]
  ![-55, 32, -19] ![![400, 0, 0], ![722, 221, 84]] where
    su := ![![16400, 0, 0], ![-6400, 400, 0]]
    hsu := by decide
    w := ![![-22000, 12800, -7600], ![-74800, 19200, 37600]]
    hw := by decide
    g := ![![![3538013642, -2694314125, 1884896305], ![5293335527, -1279187520, 0]], ![![-2696773212642842, 2053681388236727, -1436720667640218], ![-4034728022022512, 975032466281727, 0]]]
    h := ![![![531, 3989, -1424], ![-95, 11673, 0]], ![![1767, 13375, -4771], ![-353, 39141, 0]]]
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
  ![-435, -32, -31] ![![80, 0, 0], ![-234, 3, -32]] where
    su := ![![4720, 0, 0], ![-1280, 80, 0]]
    hsu := by decide
    w := ![![-34800, -2560, -2480], ![114560, 9760, 7920]]
    hw := by decide
    g := ![![![-74717, 58807, 100103], ![181335, -27918, 0]], ![![-1039437726, 816088256, 1388752476], ![2515458094, -387411887, 0]]]
    h := ![![![727779, 5300369, -1892339], ![-107487, 22329594, 0]], ![![-2393216, -17429998, 6222861], ![353644, -73429740, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {80} * I59N1 =  Ideal.span {B.equivFun.symm ![-435, -32, -31]} * (J0 ^ 4*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_1 E59RS1 


noncomputable def E67RS0 : RelationCertificate Table 1600 ![![67, 0, 0], ![-28, 1, 0]]
  ![-1985, -176, -133] ![![1600, 0, 0], ![-1302, -201, -166]] where
    su := ![![107200, 0, 0], ![-44800, 1600, 0]]
    hsu := by decide
    w := ![![-3176000, -281600, -212800], ![4696000, 324800, 324800]]
    hw := by decide
    g := ![![![-200610412901004386553, 37557860944516377045, -9422384990880028601], ![159506089659841253086, -61744170681934166083, 0]], ![![83837187358249615721, -15695822461291293702, 3937713124750829274], ![-66659261252768804501, 25803533978545242772, 0]]]
    h := ![![![-321008071, -4535181201, 871959461], ![66463387, -11684256804, 0]], ![![474807717, 6708052215, -1289727871], ![-98306890, 17282353512, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N0 : Ideal.span {1600} * I67N0 =  Ideal.span {B.equivFun.symm ![-1985, -176, -133]} * (J0 ^ 6*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6J1_2 E67RS0 


noncomputable def E67RS1 : RelationCertificate Table 10 ![![67, 0, 0], ![-21, 1, 0]]
  ![-15, 2, 1] ![![10, 0, 0], ![-20, 0, -3]] where
    su := ![![670, 0, 0], ![-210, 10, 0]]
    hsu := by decide
    w := ![![-150, 20, 10], ![90, -10, 70]]
    hw := by decide
    g := ![![![29, -10, -10], ![-22, 5, 0]], ![![8, 2, 4], ![11, -1, 0]]]
    h := ![![![-14131, -141197, 37148], ![2324, -497783, 0]], ![![8483, 84681, -22279], ![-1368, 298540, 0]]]
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
  ![-65, -4, -7] ![![50, 0, 0], ![22, 21, 4]] where
    su := ![![3550, 0, 0], ![450, 50, 0]]
    hsu := by decide
    w := ![![-3250, -200, -350], ![-9000, 50, -200]]
    hw := by decide
    g := ![![![-7266662788507, 762854531932, -4587131888867], ![-3243903274606, 2498270180843, 0]], ![![-921128086755, 96700061056, -581468570016], ![-411199818065, 316682760547, 0]]]
    h := ![![![50972, -282157, -128237], ![2539, 1820964, 0]], ![![142360, -787960, -358119], ![6982, 5085289, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N0 : Ideal.span {50} * I71N0 =  Ideal.span {B.equivFun.symm ![-65, -4, -7]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E71RS0 


noncomputable def E71RS1 : RelationCertificate Table 3200 ![![71, 0, 0], ![25, 1, 0]]
  ![-2255, -208, -139] ![![3200, 0, 0], ![-11742, -2896, -1521]] where
    su := ![![227200, 0, 0], ![80000, 3200, 0]]
    hsu := by decide
    w := ![![-7216000, -665600, -444800], ![56060800, 4214400, 4310400]]
    hw := by decide
    g := ![![![-62575361, 126949729, -18574666], ![123555530, -21626761, 0]], ![![-23292110, 47256141, -6914122], ![45992707, -8050367, 0]]]
    h := ![![![-738494765, 10504073232, 1944906391], ![-112088620, -27617670780, 0]], ![![5739150659, -81631533869, -15114678693], ![871087846, 214628437710, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {3200} * I71N1 =  Ideal.span {B.equivFun.symm ![-2255, -208, -139]} * (J0 ^ 7*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7J1_2 E71RS1 


noncomputable def E71RS2 : RelationCertificate Table 50 ![![71, 0, 0], ![-34, 1, 0]]
  ![-635, -46, -43] ![![50, 0, 0], ![22, 21, 4]] where
    su := ![![3550, 0, 0], ![-1700, 50, 0]]
    hsu := by decide
    w := ![![-31750, -2300, -2150], ![-64200, -4900, -4250]]
    hw := by decide
    g := ![![![-190504699, 19999168, -120257419], ![-85042945, 65495286, 0]], ![![-1333706217450, 140012528690, -841911410845], ![-595378386452, 458526640083, 0]]]
    h := ![![![7737, 137191, -21433], ![-1727, 304340, 0]], ![![15614, 277385, -43335], ![-3553, 615340, 0]]]
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
  ![15, -8, 11] ![![40, 0, 0], ![106, 18, 13]] where
    su := ![![3160, 0, 0], ![400, 40, 0]]
    hsu := by decide
    w := ![![600, -320, 440], ![1520, 200, -1120]]
    hw := by decide
    g := ![![![-678555189, 818327942, 34591118], ![-1418681260, 266550183, 0]], ![![-87514072, 105540622, 4461244], ![-182968819, 34377264, 0]]]
    h := ![![![-10081, 60843, 25349], ![-461, -400512, 0]], ![![-23536, 142127, 59213], ![-1176, -935571, 0]]]
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
  ![5, 8, -11] ![![100, 0, 0], ![114, 37, 16]] where
    su := ![![7900, 0, 0], ![3500, 100, 0]]
    hsu := by decide
    w := ![![500, 800, -1100], ![-8400, 2500, 2800]]
    hw := by decide
    g := ![![![706819, -305770, 180761], ![721746, -193621, 0]], ![![321035, -138899, 82104], ![327863, -87949, 0]]]
    h := ![![![62880, -1261547, -170459], ![11971, 2693250, 0]], ![![-1086246, 21781960, 2943157], ![-205440, -46501875, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N2 : Ideal.span {100} * I79N2 =  Ideal.span {B.equivFun.symm ![5, 8, -11]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E79RS2 
