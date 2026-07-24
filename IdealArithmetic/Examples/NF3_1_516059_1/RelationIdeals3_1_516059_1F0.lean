import IdealArithmetic.Examples.NF3_1_516059_1.PrimesBelow3_1_516059_1F0
import IdealArithmetic.Examples.NF3_1_516059_1.ClassGroupData3_1_516059_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 2097152 ![![2, 0, 0], ![16, 0, 1]]
  ![-103398, 844, -4587] ![![2097152, 0, 0], ![-611271, 1, 0]] where
    su := ![![4194304, 0, 0], ![33554432, 0, 2097152]]
    hsu := by decide
    w := ![![-216841322496, 1769996288, -9619636224], ![63203966976, -515899392, 2803892224]]
    hw := by decide
    g := ![![![-12061902315328, -2593077684061751555, 29694611235591], ![2279288815567, -8896301905991733835, 0]], ![![-96495214056368, -20744620190559608108, 237556875204665], ![18234304262631, -71170410849887659149, 0]]]
    h := ![![![-859, 422, 884], ![-6355, 0, 0]], ![![245, -123, -258], ![1853, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {2097152} * I2N0 =  Ideal.span {B.equivFun.symm ![-103398, 844, -4587]} * (J0 ^ 21) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_21 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 1 ![![2, 0, 0], ![1, 1, 0]]
  ![1, 0, 0] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![2, 0, 0], ![1, 1, 0]]
    hsu := by decide
    w := ![![2, 0, 0], ![1, 1, 0]]
    hw := by decide
    g := ![![![-2, -2, 7], ![0, -2, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![-2, -2, 7], ![0, -2, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {1} * I2N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS1 


noncomputable def E7RS0 : RelationCertificate Table 4096 ![![7, 0, 0], ![16, 0, 1]]
  ![226, -68, 25] ![![4096, 0, 0], ![-967, 1, 0]] where
    su := ![![28672, 0, 0], ![65536, 0, 4096]]
    hsu := by decide
    w := ![![925696, -278528, 102400], ![-217088, 65536, -24576]]
    hw := by decide
    g := ![![![396538878, 132883660326, -958954142], ![-61170895, 561125166520, 0]], ![![906361121, 303730107666, -2191866510], ![-139824142, 1282555032140, 0]]]
    h := ![![![158, -204, 9], ![370, -136, 0]], ![![-51, 48, -3], ![-81, 32, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {4096} * I7N0 =  Ideal.span {B.equivFun.symm ![226, -68, 25]} * (J0 ^ 12) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_12 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 256 ![![7, 0, 0], ![14, 0, 1]]
  ![194, -4, 9] ![![256, 0, 0], ![57, 1, 0]] where
    su := ![![1792, 0, 0], ![3584, 0, 256]]
    hsu := by decide
    w := ![![49664, -1024, 2304], ![11520, -256, 512]]
    hw := by decide
    g := ![![![140415, -2612101, -338595], ![21096, 12382903, 0]], ![![280819, -5224179, -677187], ![42236, 24765696, 0]]]
    h := ![![![197712, 8, 14122], ![-98860, 5, 0]], ![![45863, 5, 3276], ![-22939, 3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {256} * I7N1 =  Ideal.span {B.equivFun.symm ![194, -4, 9]} * (J0 ^ 8) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8 E7RS1 


noncomputable def E7RS2 : RelationCertificate Table 4 ![![7, 0, 0], ![-1, 1, 0]]
  ![26, 0, 1] ![![4, 0, 0], ![1, 1, 0]] where
    su := ![![28, 0, 0], ![-4, 4, 0]]
    hsu := by decide
    w := ![![104, 0, 4], ![76, 0, 4]]
    hw := by decide
    g := ![![![-12, 6, -1], ![1, 0, 1]], ![![0, 0, -2], ![3, 1, 0]]]
    h := ![![![28112, -14202, 1159], ![-6042, 0, -4056]], ![![20544, -10379, 847], ![-4411, 0, -2964]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N2 : Ideal.span {4} * I7N2 =  Ideal.span {B.equivFun.symm ![26, 0, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E7RS2 


noncomputable def E11RS0 : RelationCertificate Table 128 ![![11, 0, 0], ![11, 2, 1]]
  ![66, -4, 9] ![![128, 0, 0], ![57, 1, 0]] where
    su := ![![1408, 0, 0], ![1408, 256, 128]]
    hsu := by decide
    w := ![![8448, -512, 1152], ![4224, -384, 512]]
    hw := by decide
    g := ![![![-116393, 2362305, 306191], ![-33306, -5598921, 0]], ![![116306, -2361326, -306064], ![33380, 5596599, 0]]]
    h := ![![![-3, -2, 0], ![9, 0, 0]], ![![-1, -1, 0], ![4, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {128} * I11N0 =  Ideal.span {B.equivFun.symm ![66, -4, 9]} * (J0 ^ 7) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 32768 ![![11, 0, 0], ![5, 1, 0]]
  ![15338, -84, 573] ![![32768, 0, 0], ![11321, 1, 0]] where
    su := ![![360448, 0, 0], ![163840, 32768, 0]]
    hsu := by decide
    w := ![![502595584, -2752512, 18776064], ![173670400, -950272, 6488064]]
    hw := by decide
    g := ![![![-22938441147598, 93162905504195770, 57619750613515], ![-5081884331767, -269726284014808505, 0]], ![![-10426564159812, 42346775249120742, 26190795745749], ![-2309947433582, -122602856428100463, 0]]]
    h := ![![![97512, -78728, -263643], ![37168, 414378, 0]], ![![33691, -27205, -91101], ![12852, 143187, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {32768} * I11N1 =  Ideal.span {B.equivFun.symm ![15338, -84, 573]} * (J0 ^ 15) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_15 E11RS1 


noncomputable def E13RS0 : RelationCertificate Table 8 ![![13, 0, 0], ![10, -4, 1]]
  ![10, -4, 1] ![![8, 0, 0], ![1, 1, 0]] where
    su := ![![104, 0, 0], ![80, -32, 8]]
    hsu := by decide
    w := ![![80, -32, 8], ![72, -8, -24]]
    hw := by decide
    g := ![![![201880, 132841, -483251], ![41846, 552287, 0]], ![![157991, 103962, -378196], ![32752, 432224, 0]]]
    h := ![![![0, 0, 0], ![1, 0, 0]], ![![-7, 3, -1], ![10, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {8} * I13N0 =  Ideal.span {B.equivFun.symm ![10, -4, 1]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 524288 ![![13, 0, 0], ![-1, 1, 0]]
  ![-3298, 2116, -1561] ![![524288, 0, 0], ![-86983, 1, 0]] where
    su := ![![6815744, 0, 0], ![-524288, 524288, 0]]
    hsu := by decide
    w := ![![-1729101824, 1109393408, -818413568], ![286785536, -184025088, 135790592]]
    hw := by decide
    g := ![![![-39687546147291469199159, -1171677687002981288648613717, 94288090140514508760844], ![4349640158704514811918, -7062016314798581538457911315, 0]], ![![6105776330785219140909, 180258105705540329916501672, -14505860022645573469342], ![-669175409078884804487, 1086464048507543203299196926, 0]]]
    h := ![![![-19531, -25459, 44779], ![-453, -83384, 0]], ![![3240, 4222, -7427], ![83, 13830, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {524288} * I13N1 =  Ideal.span {B.equivFun.symm ![-3298, 2116, -1561]} * (J0 ^ 19) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_19 E13RS1 


noncomputable def E17RS1 : RelationCertificate Table 512 ![![17, 0, 0], ![-5, 1, 0]]
  ![-62, -4, 9] ![![512, 0, 0], ![57, 1, 0]] where
    su := ![![8704, 0, 0], ![-2560, 512, 0]]
    hsu := by decide
    w := ![![-31744, -2048, 4608], ![-3072, -512, 512]]
    hw := by decide
    g := ![![![-4812195, 87351236, 11323216], ![-364797, -828212371, 0]], ![![1415219, -25690325, -3330200], ![107876, 243580343, 0]]]
    h := ![![![-910399, -2528111, 2205969], ![119067, -5357352, 0]], ![![-87195, -242141, 211286], ![11412, -513123, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {512} * I17N1 =  Ideal.span {B.equivFun.symm ![-62, -4, 9]} * (J0 ^ 9) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_9 E17RS1 


noncomputable def E19RS0 : RelationCertificate Table 65536 ![![19, 0, 0], ![-7, 1, 0]]
  ![-7686, -116, -379] ![![65536, 0, 0], ![-21447, 1, 0]] where
    su := ![![1245184, 0, 0], ![-458752, 65536, 0]]
    hsu := by decide
    w := ![![-503709696, -7602176, -24838144], ![164823040, 2490368, 8126464]]
    hw := by decide
    g := ![![![-586315297306451786282, -4481124780864458258392508, 1462371722744064088570], ![123498220832321420013, -13691141888822140586931934, 0]], ![![231440248931171371019, 1768865045035383100500420, -577251995806093004667], ![-48749297695792316367, 5404398113878301593408075, 0]]]
    h := ![![![11312661977, 40328271143, -28154437321], ![-2045282233, 76419186960, 0]], ![![-3701702364, -13196121051, 9212628076], ![669252407, -25005704760, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N0 : Ideal.span {65536} * I19N0 =  Ideal.span {B.equivFun.symm ![-7686, -116, -379]} * (J0 ^ 16) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_16 E19RS0 


noncomputable def E19RS1 : RelationCertificate Table 4096 ![![19, 0, 0], ![-5, 1, 0]]
  ![-2878, -4, -119] ![![4096, 0, 0], ![-967, 1, 0]] where
    su := ![![77824, 0, 0], ![-20480, 4096, 0]]
    hsu := by decide
    w := ![![-11788288, -16384, -487424], ![2777088, 4096, 114688]]
    hw := by decide
    g := ![![![-6538720269, -2191186930923, 15812687415], ![1008733255, -9252681093121, 0]], ![![1720715807, 576627853668, -4161231466], ![-265452598, 2434914869249, 0]]]
    h := ![![![-6749, -18219, 15897], ![829, -43166, 0]], ![![1595, 4291, -3745], ![-176, 10169, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {4096} * I19N1 =  Ideal.span {B.equivFun.symm ![-2878, -4, -119]} * (J0 ^ 12) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_12 E19RS1 


noncomputable def E23RS1 : RelationCertificate Table 4 ![![23, 0, 0], ![4, 1, 0]]
  ![-22, 0, -1] ![![4, 0, 0], ![1, 1, 0]] where
    su := ![![92, 0, 0], ![16, 4, 0]]
    hsu := by decide
    w := ![![-88, 0, -4], ![-72, 4, -4]]
    hw := by decide
    g := ![![![945130, 597940, -2430339], ![385771, 1388765, 0]], ![![164413, 104017, -422779], ![67109, 241588, 0]]]
    h := ![![![1438, -504, -3455], ![240, 11352, 0]], ![![1188, -416, -2853], ![195, 9374, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {4} * I23N1 =  Ideal.span {B.equivFun.symm ![-22, 0, -1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E23RS1 


noncomputable def E31RS1 : RelationCertificate Table 32 ![![31, 0, 0], ![5, 1, 0]]
  ![18, -4, 1] ![![32, 0, 0], ![-7, 1, 0]] where
    su := ![![992, 0, 0], ![160, 32, 0]]
    hsu := by decide
    w := ![![576, -128, 32], ![-64, 32, -32]]
    hw := by decide
    g := ![![![303891838, 1038836598, -726441591], ![-34012685, 3320875845, 0]], ![![49042545, 167649089, -117234290], ![-5489018, 535928183, 0]]]
    h := ![![![82, -60, -205], ![40, 908, 0]], ![![-13, 6, 23], ![19, -102, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {32} * I31N1 =  Ideal.span {B.equivFun.symm ![18, -4, 1]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E31RS1 
