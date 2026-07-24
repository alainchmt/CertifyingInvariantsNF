import IdealArithmetic.Examples.NF3_1_126635_1.PrimesBelow3_1_126635_1F0
import IdealArithmetic.Examples.NF3_1_126635_1.ClassGroupData3_1_126635_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 65536 ![![2, 0, 0], ![-5, 2, 1]]
  ![5591, 1240, 167] ![![65536, 0, 0], ![-1592, 1, 0]] where
    su := ![![131072, 0, 0], ![-327680, 131072, 65536]]
    hsu := by decide
    w := ![![366411776, 81264640, 10944512], ![-8912896, -1966080, -262144]]
    hw := by decide
    g := ![![![1382, -2307481, 4351], ![56891, -95049037, 0]], ![![1477, 2230581, -4206], ![60802, 91881469, 0]]]
    h := ![![![938, 1363, 455], ![-743, 0, 0]], ![![-18, -35, -12], ![20, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {65536} * I2N0 =  Ideal.span {B.equivFun.symm ![5591, 1240, 167]} * (J0 ^ 16) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_16 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 1 ![![2, 0, 0], ![0, 1, 0]]
  ![1, 0, 0] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![2, 0, 0], ![0, 1, 0]]
    hsu := by decide
    w := ![![2, 0, 0], ![0, 1, 0]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {1} * I2N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS1 


noncomputable def E3RS0 : RelationCertificate Table 32768 ![![3, 0, 0], ![-4, 1, 1]]
  ![7049, -1496, 697] ![![32768, 0, 0], ![-1592, 1, 0]] where
    su := ![![98304, 0, 0], ![-131072, 32768, 32768]]
    hsu := by decide
    w := ![![230981632, -49020928, 22839296], ![-11272192, 2392064, -1114112]]
    hw := by decide
    g := ![![![91, -27690825, 52214], ![1873, -570316123, 0]], ![![900, 33598737, -63354], ![18524, 691994615, 0]]]
    h := ![![![14458813935, 3539002521, 4049982246], ![-16748756987, 1532936982, 0]], ![![-705601988, -172706228, -197642458], ![817353089, -74808583, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {32768} * I3N0 =  Ideal.span {B.equivFun.symm ![7049, -1496, 697]} * (J0 ^ 15) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_15 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 256 ![![3, 0, 0], ![-6, 1, 1]]
  ![237, -56, -35] ![![256, 0, 0], ![-56, 1, 0]] where
    su := ![![768, 0, 0], ![-1536, 256, 256]]
    hsu := by decide
    w := ![![60672, -14336, -8960], ![-10752, 3072, 1792]]
    hw := by decide
    g := ![![![25, 423, -23], ![109, 1972, 0]], ![![-8, -68087, 3714], ![-45, -316913, 0]]]
    h := ![![![129, 43, 43], ![-227, 21, 0]], ![![-24, -11, -11], ![55, -5, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {256} * I3N1 =  Ideal.span {B.equivFun.symm ![237, -56, -35]} * (J0 ^ 8) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8 E3RS1 


noncomputable def E3RS2 : RelationCertificate Table 2048 ![![3, 0, 0], ![-1, 1, 0]]
  ![-511, -280, -79] ![![2048, 0, 0], ![456, 1, 0]] where
    su := ![![6144, 0, 0], ![-2048, 2048, 0]]
    hsu := by decide
    w := ![![-1046528, -573440, -161792], ![-227328, -129024, -36864]]
    hw := by decide
    g := ![![![-123921, 1193282944, 7833369], ![556556, -5347579925, 0]], ![![-94370, 909702762, 5971792], ![423841, -4076743284, 0]]]
    h := ![![![-98482877, -276350, -1519395], ![32735512, 0, -4558106]], ![![-21103474, -59219, -325585], ![7014753, 0, -976737]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N2 : Ideal.span {2048} * I3N2 =  Ideal.span {B.equivFun.symm ![-511, -280, -79]} * (J0 ^ 11) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_11 E3RS2 


noncomputable def E5RS0 : RelationCertificate Table 1024 ![![5, 0, 0], ![1, 1, 0]]
  ![-1819, 392, -171] ![![1024, 0, 0], ![456, 1, 0]] where
    su := ![![5120, 0, 0], ![1024, 1024, 0]]
    hsu := by decide
    w := ![![-1862656, 401408, -175104], ![-817152, 176128, -76800]]
    hw := by decide
    g := ![![![-501953, 1382758882, 9077199], ![1127193, -3098350596, 0]], ![![536833595, -1479250183607, -9710621625], ![-1205521055, 3314558847997, 0]]]
    h := ![![![334578, 334979, -96], ![-1674709, 103, 0]], ![![146784, 146958, -45], ![-734718, 50, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {1024} * I5N0 =  Ideal.span {B.equivFun.symm ![-1819, 392, -171]} * (J0 ^ 10) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_10 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 4096 ![![5, 0, 0], ![-1, 1, 0]]
  ![-227, 72, 13] ![![4096, 0, 0], ![-1592, 1, 0]] where
    su := ![![20480, 0, 0], ![-4096, 4096, 0]]
    hsu := by decide
    w := ![![-929792, 294912, 53248], ![360448, -114688, -20480]]
    hw := by decide
    g := ![![![-51239, -629879520, 1187705], ![-131831, -1621613228, 0]], ![![13059, 157334512, -296671], ![33599, 405054805, 0]]]
    h := ![![![-43, 12, -13], ![12, 26, 0]], ![![17, -5, 5], ![-3, -10, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {4096} * I5N1 =  Ideal.span {B.equivFun.symm ![-227, 72, 13]} * (J0 ^ 12) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_12 E5RS1 


noncomputable def E11RS1 : RelationCertificate Table 8 ![![11, 0, 0], ![4, 1, 0]]
  ![53, 0, -3] ![![8, 0, 0], ![0, 1, 0]] where
    su := ![![88, 0, 0], ![32, 8, 0]]
    hsu := by decide
    w := ![![424, 0, -24], ![216, 32, 0]]
    hw := by decide
    g := ![![![16, 599, 1839], ![81, -4900, 0]], ![![-4, 690, 2100], ![88, -5601, 0]]]
    h := ![![![-301, -76, 0], ![841, -1, 0]], ![![-147, -37, 0], ![411, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {8} * I11N1 =  Ideal.span {B.equivFun.symm ![53, 0, -3]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E11RS1 


noncomputable def E13RS1 : RelationCertificate Table 2048 ![![13, 0, 0], ![-1, 1, 0]]
  ![-629, -8, 27] ![![2048, 0, 0], ![456, 1, 0]] where
    su := ![![26624, 0, 0], ![-2048, 2048, 0]]
    hsu := by decide
    w := ![![-1288192, -16384, 55296], ![-288768, -4096, 12288]]
    hw := by decide
    g := ![![![7439463345850, -71820840177536916, -471471705637743], ![-33412326605923, 321858017715365886, 0]], ![![-619955279152, 5985070015028688, 39289308804681], ![2784360551981, -26821501477328895, 0]]]
    h := ![![![-96, 47, 0], ![-619, 9, 0]], ![![-20, 9, 0], ![-119, 2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {2048} * I13N1 =  Ideal.span {B.equivFun.symm ![-629, -8, 27]} * (J0 ^ 11) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_11 E13RS1 


noncomputable def E19RS0 : RelationCertificate Table 4096 ![![19, 0, 0], ![5, 1, 0]]
  ![1003, -264, 123] ![![4096, 0, 0], ![-1592, 1, 0]] where
    su := ![![77824, 0, 0], ![20480, 4096, 0]]
    hsu := by decide
    w := ![![4108288, -1081344, 503808], ![-1605632, 421888, -196608]]
    hw := by decide
    g := ![![![-155321279, -1884129742210, 3552727542], ![-399620577, -4850657337343, 0]], ![![-53719481, -651651102928, 1228757643], ![-138212936, -1677663768577, 0]]]
    h := ![![![-2714223, -542852, 15], ![10314248, -54, 0]], ![![1060672, 212131, -9], ![-4030632, 41, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N0 : Ideal.span {4096} * I19N0 =  Ideal.span {B.equivFun.symm ![1003, -264, 123]} * (J0 ^ 12) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_12 E19RS0 


noncomputable def E19RS1 : RelationCertificate Table 2048 ![![19, 0, 0], ![-3, 1, 0]]
  ![-2407, 168, 201] ![![2048, 0, 0], ![456, 1, 0]] where
    su := ![![38912, 0, 0], ![-6144, 2048, 0]]
    hsu := by decide
    w := ![![-4929536, 344064, 411648], ![-1112064, 75776, 92160]]
    hw := by decide
    g := ![![![-130, -215695, -1416], ![581, 966615, 0]], ![![-111, 19189, 126], ![500, -85995, 0]]]
    h := ![![![-15754027, 5304024, -79062], ![-99774702, 500793, 0]], ![![-3553923, 1196527, -17838], ![-22507998, 112989, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {2048} * I19N1 =  Ideal.span {B.equivFun.symm ![-2407, 168, 201]} * (J0 ^ 11) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_11 E19RS1 


noncomputable def E31RS0 : RelationCertificate Table 256 ![![31, 0, 0], ![15, 1, 0]]
  ![65, -24, -15] ![![256, 0, 0], ![-56, 1, 0]] where
    su := ![![7936, 0, 0], ![3840, 256, 0]]
    hsu := by decide
    w := ![![16640, -6144, -3840], ![-2560, 1280, 768]]
    hw := by decide
    g := ![![![1096639, 1344737567, -73350390], ![5013208, 6259233279, 0]], ![![546729, 670404707, -36568062], ![2499333, 3120474624, 0]]]
    h := ![![![-25, 1968, 369], ![56, -3818, 0]], ![![-10, -305, -57], ![20, 590, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N0 : Ideal.span {256} * I31N0 =  Ideal.span {B.equivFun.symm ![65, -24, -15]} * (J0 ^ 8) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8 E31RS0 


noncomputable def E31RS1 : RelationCertificate Table 8192 ![![31, 0, 0], ![-8, 1, 0]]
  ![3547, 120, -149] ![![8192, 0, 0], ![-1592, 1, 0]] where
    su := ![![253952, 0, 0], ![-65536, 8192, 0]]
    hsu := by decide
    w := ![![29057024, 983040, -1220608], ![-5636096, -188416, 237568]]
    hw := by decide
    g := ![![![570205181, 24944034274630, -47034634757], ![2934121132, 128435909309799, 0]], ![![-101937264, -4459356727556, 8408592316], ![-524541499, -22961062750899, 0]]]
    h := ![![![6805, -853, 4], ![25926, -91, 0]], ![![-1312, 165, -1], ![-4998, 20, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {8192} * I31N1 =  Ideal.span {B.equivFun.symm ![3547, 120, -149]} * (J0 ^ 13) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_13 E31RS1 
