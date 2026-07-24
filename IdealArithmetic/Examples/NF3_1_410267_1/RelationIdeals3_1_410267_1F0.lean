import IdealArithmetic.Examples.NF3_1_410267_1.PrimesBelow3_1_410267_1F0
import IdealArithmetic.Examples.NF3_1_410267_1.ClassGroupData3_1_410267_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 16777216 ![![2, 0, 0], ![9, 2, 1]]
  ![137897, 990, 5797] ![![16777216, 0, 0], ![-7863325, 1, 0]] where
    su := ![![33554432, 0, 0], ![150994944, 33554432, 16777216]]
    hsu := by decide
    w := ![![2313527754752, 16609443840, 97257521152], ![-1084328247296, -7784628224, -45583695872]]
    hw := by decide
    g := ![![![-358520, 25180283671719, -16011221], ![12899698, 53724742628145, 0]], ![![-21198740, 126558293710279, -80473788], ![23449954, 270025224722880, 0]]]
    h := ![![![6502, -13382, -4040], ![13877, 0, 0]], ![![-3052, 6271, 1893], ![-6503, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {16777216} * I2N0 =  Ideal.span {B.equivFun.symm ![137897, 990, 5797]} * (J0 ^ 24) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_24 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 1 ![![2, 0, 0], ![1, 1, 0]]
  ![1, 0, 0] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![2, 0, 0], ![1, 1, 0]]
    hsu := by decide
    w := ![![2, 0, 0], ![1, 1, 0]]
    hw := by decide
    g := ![![![0, -1, 0], ![2, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![0, -1, 0], ![2, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {1} * I2N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS1 


noncomputable def E5RS0 : RelationCertificate Table 32768 ![![5, 0, 0], ![1, 1, 0]]
  ![-3241, 34, -165] ![![32768, 0, 0], ![995, 1, 0]] where
    su := ![![163840, 0, 0], ![32768, 32768, 0]]
    hsu := by decide
    w := ![![-106201088, 1114112, -5406720], ![-3244032, 32768, -163840]]
    hw := by decide
    g := ![![![-409, -8566, -43], ![12903, 281805, 0]], ![![-34, -1992, -10], ![988, 65535, 0]]]
    h := ![![![-625, 30, -33], ![-116, 0, 0]], ![![-20, 0, -1], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {32768} * I5N0 =  Ideal.span {B.equivFun.symm ![-3241, 34, -165]} * (J0 ^ 15) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_15 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 1024 ![![5, 0, 0], ![-2, 1, 0]]
  ![181, 6, 1] ![![1024, 0, 0], ![-29, 1, 0]] where
    su := ![![5120, 0, 0], ![-2048, 1024, 0]]
    hsu := by decide
    w := ![![185344, 6144, 1024], ![-5120, 0, 0]]
    hw := by decide
    g := ![![![-5236639, 73400021, -13107185], ![220159, 2684351488, 0]], ![![-7148366796, 100195903176, -17892177934], ![300292506, 3664318040883, 0]]]
    h := ![![![14349, -676, -427], ![-5870, 0, -712]], ![![-403, 19, 12], ![165, 0, 20]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {1024} * I5N1 =  Ideal.span {B.equivFun.symm ![181, 6, 1]} * (J0 ^ 10) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_10 E5RS1 


noncomputable def E7RS0 : RelationCertificate Table 131072 ![![7, 0, 0], ![8, 2, 1]]
  ![-23981, -1174, -1049] ![![131072, 0, 0], ![995, 1, 0]] where
    su := ![![917504, 0, 0], ![1048576, 262144, 131072]]
    hsu := by decide
    w := ![![-3143237632, -153878528, -137494528], ![-23986176, -1179648, -1048576]]
    hw := by decide
    g := ![![![-646042, -321635093, -1614634], ![24818, 42326661531, 0]], ![![-740428, -368323988, -1849016], ![108230, 48470845027, 0]]]
    h := ![![![-1539, 304, 86], ![-1651, 0, 0]], ![![-17, 1, 0], ![-8, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {131072} * I7N0 =  Ideal.span {B.equivFun.symm ![-23981, -1174, -1049]} * (J0 ^ 17) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_17 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 256 ![![7, 0, 0], ![-2, 1, 0]]
  ![75, -6, -1] ![![256, 0, 0], ![-29, 1, 0]] where
    su := ![![1792, 0, 0], ![-512, 256, 0]]
    hsu := by decide
    w := ![![19200, -1536, -256], ![-2304, 256, 0]]
    hw := by decide
    g := ![![![85774, -1223745, 218536], ![-14482, -11189043, 0]], ![![-42627, 608294, -108629], ![7279, 5561805, 0]]]
    h := ![![![11, -1, 2], ![-2, -3, 0]], ![![-1, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {256} * I7N1 =  Ideal.span {B.equivFun.symm ![75, -6, -1]} * (J0 ^ 8) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8 E7RS1 


noncomputable def E11RS0 : RelationCertificate Table 1024 ![![11, 0, 0], ![-4, 1, 0]]
  ![119, -30, -5] ![![1024, 0, 0], ![-29, 1, 0]] where
    su := ![![11264, 0, 0], ![-4096, 1024, 0]]
    hsu := by decide
    w := ![![121856, -30720, -5120], ![-4096, 1024, 0]]
    hw := by decide
    g := ![![![30, -29, 5], ![991, -1025, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![613, -1046, 1785], ![-308, -3928, 0]], ![![-20, 35, -60], ![12, 132, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {1024} * I11N0 =  Ideal.span {B.equivFun.symm ![119, -30, -5]} * (J0 ^ 10) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_10 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 32 ![![11, 0, 0], ![-3, 1, 0]]
  ![147, 10, 7] ![![32, 0, 0], ![3, 1, 0]] where
    su := ![![352, 0, 0], ![-96, 32, 0]]
    hsu := by decide
    w := ![![4704, 320, 224], ![1280, 96, 64]]
    hw := by decide
    g := ![![![172583, 349402, 437812], ![27121, -2801997, 0]], ![![-27033, -54726, -68573], ![-4232, 438867, 0]]]
    h := ![![![352, -359, 927], ![-117, -2038, 0]], ![![97, -98, 252], ![-27, -554, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {32} * I11N1 =  Ideal.span {B.equivFun.symm ![147, 10, 7]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E11RS1 


noncomputable def E13RS0 : RelationCertificate Table 512 ![![13, 0, 0], ![1, 1, 0]]
  ![-31, -18, -3] ![![512, 0, 0], ![-29, 1, 0]] where
    su := ![![6656, 0, 0], ![512, 512, 0]]
    hsu := by decide
    w := ![![-15872, -9216, -1536], ![512, 512, 0]]
    hw := by decide
    g := ![![![-397, 5706, -1019], ![188, 104345, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![3031, 3032, 7674], ![472, -19953, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {512} * I13N0 =  Ideal.span {B.equivFun.symm ![-31, -18, -3]} * (J0 ^ 9) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_9 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 128 ![![13, 0, 0], ![-2, 1, 0]]
  ![-53, -6, -1] ![![128, 0, 0], ![-29, 1, 0]] where
    su := ![![1664, 0, 0], ![-256, 128, 0]]
    hsu := by decide
    w := ![![-6784, -768, -128], ![1408, 128, 0]]
    hw := by decide
    g := ![![![260, -3573, 638], ![22, -16333, 0]], ![![-231, 3572, -638], ![107, 16333, 0]]]
    h := ![![![245, -125, 638], ![-40, -1659, 0]], ![![1, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {128} * I13N1 =  Ideal.span {B.equivFun.symm ![-53, -6, -1]} * (J0 ^ 7) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7 E13RS1 


noncomputable def E17RS1 : RelationCertificate Table 524288 ![![17, 0, 0], ![-3, 1, 0]]
  ![-105807, -7858, -5235] ![![524288, 0, 0], ![995, 1, 0]] where
    su := ![![8912896, 0, 0], ![-1572864, 524288, 0]]
    hsu := by decide
    w := ![![-55473340416, -4119855104, -2744647680], ![-105906176, -7864320, -5242880]]
    hw := by decide
    g := ![![![-3919217, -1951759608, -9797990], ![11065, 1027393716213, 0]], ![![384582, 192008879, 963900], ![515330, -101072240631, 0]]]
    h := ![![![-1163524017391, 1195956735882, -3030432747640], ![275678164006, 10303471340929, 0]], ![![-2221328115, 2283246656, -5785514835], ![526307707, 19670750437, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {524288} * I17N1 =  Ideal.span {B.equivFun.symm ![-105807, -7858, -5235]} * (J0 ^ 19) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_19 E17RS1 


noncomputable def E19RS0 : RelationCertificate Table 16384 ![![19, 0, 0], ![-7, 1, 0]]
  ![-345, 130, -149] ![![16384, 0, 0], ![995, 1, 0]] where
    su := ![![311296, 0, 0], ![-114688, 16384, 0]]
    hsu := by decide
    w := ![![-5652480, 2129920, -2441216], ![-360448, 131072, -147456]]
    hw := by decide
    g := ![![![-7140036030, -3575451438929, -17949053608], ![-651826543, 58815458862690, 0]], ![![2818434408, 1411362409306, 7085152736], ![257314201, -23216628485325, 0]]]
    h := ![![![-1524, 5437, -4571], ![867, 17340, 0]], ![![-96, 346, -291], ![58, 1104, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N0 : Ideal.span {16384} * I19N0 =  Ideal.span {B.equivFun.symm ![-345, 130, -149]} * (J0 ^ 14) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_14 E19RS0 


noncomputable def E19RS1 : RelationCertificate Table 4194304 ![![19, 0, 0], ![-5, 1, 0]]
  ![1157, -7322, 3729] ![![4194304, 0, 0], ![525283, 1, 0]] where
    su := ![![79691776, 0, 0], ![-20971520, 4194304, 0]]
    hsu := by decide
    w := ![![4852809728, -30710693888, 15640559616], ![608174080, -3846176768, 1958739968]]
    hw := by decide
    g := ![![![7950339992221174, 2137607142764745709171, 20347156421717629], ![1505323790339943, -17068431913647187637067, 0]], ![![-1536087565603298, -413007714768818372934, -3931280171953531], ![-290844058113394, 3297796830069076577487, 0]]]
    h := ![![![11868, -26125, 32666], ![-4487, -123385, 0]], ![![1490, -3274, 4093], ![-551, -15460, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {4194304} * I19N1 =  Ideal.span {B.equivFun.symm ![1157, -7322, 3729]} * (J0 ^ 22) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_22 E19RS1 


noncomputable def E23RS1 : RelationCertificate Table 8 ![![23, 0, 0], ![-11, 1, 0]]
  ![-5, 2, -1] ![![8, 0, 0], ![3, 1, 0]] where
    su := ![![184, 0, 0], ![-88, 8, 0]]
    hsu := by decide
    w := ![![-40, 16, -8], ![-128, 16, 8]]
    hw := by decide
    g := ![![![14657, 35508, 45938], ![9941, -73500, 0]], ![![-993298, -2407480, -3114572], ![-673421, 4983315, 0]]]
    h := ![![![5, -26, 13], ![0, -60, 0]], ![![16, -74, 37], ![4, -170, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {8} * I23N1 =  Ideal.span {B.equivFun.symm ![-5, 2, -1]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E23RS1 


noncomputable def E29RS0 : RelationCertificate Table 512 ![![29, 0, 0], ![4, 1, 0]]
  ![269, -42, -7] ![![512, 0, 0], ![-29, 1, 0]] where
    su := ![![14848, 0, 0], ![2048, 512, 0]]
    hsu := by decide
    w := ![![137728, -21504, -3584], ![-8704, 1536, 0]]
    hw := by decide
    g := ![![![339731524, -4778845403, 853375217], ![-28575992, -87385622225, 0]], ![![47671772, -670576567, 119747214], ![-4009725, -12262114715, 0]]]
    h := ![![![5916909, 15208289, 15254517], ![1340577, -88476200, 0]], ![![-374275, -962001, -964925], ![-84793, 5596565, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N0 : Ideal.span {512} * I29N0 =  Ideal.span {B.equivFun.symm ![269, -42, -7]} * (J0 ^ 9) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_9 E29RS0 


noncomputable def E29RS1 : RelationCertificate Table 1024 ![![29, 0, 0], ![8, 1, 0]]
  ![-419, 54, 9] ![![1024, 0, 0], ![-29, 1, 0]] where
    su := ![![29696, 0, 0], ![8192, 1024, 0]]
    hsu := by decide
    w := ![![-429056, 55296, 9216], ![13312, -2048, 0]]
    hw := by decide
    g := ![![![-57639964, 807917346, -144271377], ![2421837, 29546778006, 0]], ![![-15569404, 218230666, -38969876], ![654886, 7981030603, 0]]]
    h := ![![![2559, 12986, 7236], ![1163, -41967, 0]], ![![-81, -404, -225], ![-31, 1305, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {1024} * I29N1 =  Ideal.span {B.equivFun.symm ![-419, 54, 9]} * (J0 ^ 10) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_10 E29RS1 


noncomputable def E29RS2 : RelationCertificate Table 64 ![![29, 0, 0], ![-12, 1, 0]]
  ![-11, 6, 1] ![![64, 0, 0], ![-29, 1, 0]] where
    su := ![![1856, 0, 0], ![-768, 64, 0]]
    hsu := by decide
    w := ![![-704, 384, 64], ![448, -192, 0]]
    hw := by decide
    g := ![![![-1717309, 32145206, -5743788], ![1280454, 73520487, 0]], ![![690819, -12930786, 2310506], ![-515053, -29574477, 0]]]
    h := ![![![-13855, 96577, -44041], ![9091, 255438, 0]], ![![8741, -60886, 27765], ![-5716, -161037, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N2 : Ideal.span {64} * I29N2 =  Ideal.span {B.equivFun.symm ![-11, 6, 1]} * (J0 ^ 6) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6 E29RS2 


noncomputable def E31RS0 : RelationCertificate Table 65536 ![![31, 0, 0], ![4, 1, 0]]
  ![5669, -474, -591] ![![65536, 0, 0], ![995, 1, 0]] where
    su := ![![2031616, 0, 0], ![262144, 65536, 0]]
    hsu := by decide
    w := ![![371523584, -31064064, -38731776], ![5570560, -458752, -589824]]
    hw := by decide
    g := ![![![-6212843355276, -3095066257371827, -15537481222549], ![-141553396003, 203652873880194227, 0]], ![![-877525044819, -437158640358902, -2194571489277], ![-19993478639, 28764687424251486, 0]]]
    h := ![![![-5846782853, -14976239956, -15016160221], ![-1237528098, 93100193252, 0]], ![![-87651985, -224516145, -225114609], ![-18552382, 1395710574, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N0 : Ideal.span {65536} * I31N0 =  Ideal.span {B.equivFun.symm ![5669, -474, -591]} * (J0 ^ 16) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_16 E31RS0 


noncomputable def E31RS1 : RelationCertificate Table 8192 ![![31, 0, 0], ![7, 1, 0]]
  ![3737, 254, 213] ![![8192, 0, 0], ![995, 1, 0]] where
    su := ![![253952, 0, 0], ![57344, 8192, 0]]
    hsu := by decide
    w := ![![30613504, 2080768, 1744896], ![3743744, 253952, 212992]]
    hw := by decide
    g := ![![![34956011208, 17796308323223, 89338901138], ![6418158224, -146372855624499, 0]], ![![10307102161, 5247405626481, 26342398883], ![1892454027, -43159386329906, 0]]]
    h := ![![![-505223744, -2181550121, -1367187682], ![-184455363, 8476563671, 0]], ![![-61785058, -266787130, -167196744], ![-22557483, 1036619818, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {8192} * I31N1 =  Ideal.span {B.equivFun.symm ![3737, 254, 213]} * (J0 ^ 13) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_13 E31RS1 


noncomputable def E31RS2 : RelationCertificate Table 2097152 ![![31, 0, 0], ![-11, 1, 0]]
  ![-177429, -13638, -9953] ![![2097152, 0, 0], ![525283, 1, 0]] where
    su := ![![65011712, 0, 0], ![-23068672, 2097152, 0]]
    hsu := by decide
    w := ![![-372095582208, -28600958976, -20872953856], ![-93201629184, -7163871232, -5228199936]]
    hw := by decide
    g := ![![![-2112900808029205094244055050, -608850702550442596896324675282785, -5795443060809327801137181528], ![-819550312850211876112625899, 2430785001172480683362088503161634, 0]], ![![783818041688255662153106832, 225863970300971263048436291895520, 2149922425784111397738096331], ![304026728960563307778826613, -901742823015600157197848839349861, 0]]]
    h := ![![![-8677614008001, 51654286660776, -25903682373983], ![4745420669346, 160602830716704, 0]], ![![-2173548465230, 12938244935840, -6488293788583], ![1188621872704, 40227421488716, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N2 : Ideal.span {2097152} * I31N2 =  Ideal.span {B.equivFun.symm ![-177429, -13638, -9953]} * (J0 ^ 21) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_21 E31RS2 
