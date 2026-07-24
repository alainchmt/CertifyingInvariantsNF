import IdealArithmetic.Examples.NF3_1_455455_1.PrimesBelow3_1_455455_1F0
import IdealArithmetic.Examples.NF3_1_455455_1.ClassGroupData3_1_455455_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 16 ![![2, 0, 0], ![-3, 1, 1]]
  ![79433, -9974, 6001] ![![16, 0, 0], ![2, 0, 1]] where
    su := ![![32, 0, 0], ![-48, 16, 16]]
    hsu := by decide
    w := ![![1270928, -159584, 96016], ![1607456, -201840, 121440]]
    hw := by decide
    g := ![![![-56, 5, 2], ![5, -5, 0]], ![![-613, -5, 8], ![-69, -40, 0]]]
    h := ![![![70691725, 33262492, 29113054], ![-74849809, 2771617, 0]], ![![89410123, 42070038, 36821874], ![-94669224, 3505511, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {16} * I2N0 =  Ideal.span {B.equivFun.symm ![79433, -9974, 6001]} * (J0 ^ 4*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_0 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 1 ![![2, 0, 0], ![-2, 0, 1]]
  ![1, 0, 0] ![![2, 0, 0], ![-2, 0, 1]] where
    su := ![![2, 0, 0], ![-2, 0, 1]]
    hsu := by decide
    w := ![![2, 0, 0], ![-2, 0, 1]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {1} * I2N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS1 


noncomputable def E2RS2 : RelationCertificate Table 16 ![![2, 0, 0], ![1, 1, 0]]
  ![-61, 14, 11] ![![16, 0, 0], ![2, 0, 1]] where
    su := ![![32, 0, 0], ![16, 16, 0]]
    hsu := by decide
    w := ![![-976, 224, 176], ![-1728, -144, 16]]
    hw := by decide
    g := ![![![390, -17, -8], ![60, 55, 0]], ![![531, -47, 14], ![81, 35, 0]]]
    h := ![![![-128871, 30429, 1168], ![-49219, 0, -2325]], ![![-170118, 40158, 1535], ![-64980, 0, -3069]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N2 : Ideal.span {16} * I2N2 =  Ideal.span {B.equivFun.symm ![-61, 14, 11]} * (J0 ^ 4*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_0 E2RS2 


noncomputable def E3RS0 : RelationCertificate Table 72 ![![3, 0, 0], ![0, 1, 0]]
  ![-207, 26, -15] ![![72, 0, 0], ![10, 0, 1]] where
    su := ![![216, 0, 0], ![0, 72, 0]]
    hsu := by decide
    w := ![![-14904, 1872, -1080], ![-5832, 720, -432]]
    hw := by decide
    g := ![![![1091224180997, -126394314644, -2104579076], ![151529683766, 606692711240, 647]], ![![-3344286, 387361, 6449], ![-464332, -1859333, 0]]]
    h := ![![![-69, 7, -5], ![5, 0, 0]], ![![-27, 3, -2], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {72} * I3N0 =  Ideal.span {B.equivFun.symm ![-207, 26, -15]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 512 ![![3, 0, 0], ![-1, 1, 0]]
  ![-771, 98, -59] ![![1536, 0, 0], ![34, 0, 1]] where
    su := ![![1536, 0, 0], ![-512, 512, 0]]
    hsu := by decide
    w := ![![-1184256, 150528, -90624], ![-40448, 5120, -3072]]
    hw := by decide
    g := ![![![-874746773773568, 258574543826200, 12606039132], ![-19362876106989, -10183858956847258, 6]], ![![437324639545121, -129272862232485, -6302317065], ![9680359011970, 5091361958694793, -3]]]
    h := ![![![-196746, -12207, -1699], ![61515, 0, -4920]], ![![-6718, -417, -58], ![2101, 0, -168]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {512} * I3N1 =  Ideal.span {B.equivFun.symm ![-771, 98, -59]} * (J0 ^ 8*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8J1_1 E3RS1 


noncomputable def E5RS0 : RelationCertificate Table 96 ![![5, 0, 0], ![1, 1, 0]]
  ![-63, 10, 9] ![![96, 0, 0], ![34, 0, 1]] where
    su := ![![480, 0, 0], ![96, 96, 0]]
    hsu := by decide
    w := ![![-6048, 960, 864], ![-3264, 192, 288]]
    hw := by decide
    g := ![![![18717929684343, -6223909620737, -69047377012], ![6628547519707, 15320392922324, 17268]], ![![4679501776657, -1555983841120, -17261915653], ![1657143734312, 3830114072885, 4317]]]
    h := ![![![1008, 1021, -3], ![-5103, 4, 0]], ![![496, 502, -3], ![-2514, 3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {96} * I5N0 =  Ideal.span {B.equivFun.symm ![-63, 10, 9]} * (J0 ^ 4*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_1 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 12 ![![5, 0, 0], ![2, 1, 0]]
  ![-273, 22, 27] ![![12, 0, 0], ![-2, 0, 1]] where
    su := ![![60, 0, 0], ![24, 12, 0]]
    hsu := by decide
    w := ![![-3276, 264, 324], ![-1764, -528, -192]]
    hw := by decide
    g := ![![![3488831369, -81478929, 48121771], ![-577461740, 325915958, -5]], ![![1400834654, -32715512, 19321924], ![-231862280, 130861589, -2]]]
    h := ![![![19, -968, -2013], ![-184, 1682, 0]], ![![5, -468, -956], ![-86, 794, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {12} * I5N1 =  Ideal.span {B.equivFun.symm ![-273, 22, 27]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E5RS1 


noncomputable def E7RS0 : RelationCertificate Table 6 ![![7, 0, 0], ![2, 1, 0]]
  ![-45, -10, -3] ![![6, 0, 0], ![-2, 0, 1]] where
    su := ![![42, 0, 0], ![12, 6, 0]]
    hsu := by decide
    w := ![![-270, -60, -18], ![1344, 36, -54]]
    hw := by decide
    g := ![![![298869, -7520, 16162], ![-96925, 15048, 6]], ![![149004, -3725, 8040], ![-48323, 7513, 3]]]
    h := ![![![-293, -170, -51], ![1003, 59, 0]], ![![1392, 800, 237], ![-4760, -278, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {6} * I7N0 =  Ideal.span {B.equivFun.symm ![-45, -10, -3]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E7RS0 


noncomputable def E11RS0 : RelationCertificate Table 24 ![![11, 0, 0], ![0, 1, 0]]
  ![-363, 2, 21] ![![24, 0, 0], ![-14, 0, 1]] where
    su := ![![264, 0, 0], ![0, 24, 0]]
    hsu := by decide
    w := ![![-8712, 48, 504], ![5280, -480, -552]]
    hw := by decide
    g := ![![![610293637, 55745501, 14807773], ![-355387605, 148655058, -142]], ![![251192, 22966, 6086], ![-146268, 61205, 0]]]
    h := ![![![-33, -4, -21], ![4, 42, 0]], ![![20, 2, 23], ![4, -46, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {24} * I11N0 =  Ideal.span {B.equivFun.symm ![-363, 2, 21]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 1536 ![![11, 0, 0], ![5, 1, 0]]
  ![-449157, 56398, -33933] ![![1536, 0, 0], ![34, 0, 1]] where
    su := ![![16896, 0, 0], ![7680, 1536, 0]]
    hsu := by decide
    w := ![![-689905152, 86627328, -52121088], ![-23462400, 2946048, -1772544]]
    hw := by decide
    g := ![![![-11161685803700231810261373, 3299386635714917531141303, 160851862790402328353], ![-247068461246058002048304, -129945073652772136610731916, 658931]], ![![-6010138509603316981854313, 1776592803822425406394823, 86612541501350934676], ![-133036863746075049499680, -69970424273621677543965187, 354809]]]
    h := ![![![118023, -4434532, -4474515], ![-349482, 8197622, 0]], ![![4010, -150811, -152170], ![-11877, 278786, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {1536} * I11N1 =  Ideal.span {B.equivFun.symm ![-449157, 56398, -33933]} * (J0 ^ 8*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8J1_1 E11RS1 


noncomputable def E19RS1 : RelationCertificate Table 576 ![![19, 0, 0], ![8, 1, 0]]
  ![657, 170, 57] ![![576, 0, 0], ![226, 0, 1]] where
    su := ![![10944, 0, 0], ![4608, 576, 0]]
    hsu := by decide
    w := ![![378432, 97920, 32832], ![127296, 38016, 13824]]
    hw := by decide
    g := ![![![126530503202496854074, -255516566246378363077, -86190102761084382], ![49645499190384597293, 637132217133826567674, 30]], ![![63264425094052614181, -127756614068887595187, -43094488380013964], ![24822425306888039779, 318561946769174263325, 15]]]
    h := ![![![1523859, 254567, 42723], ![-3619083, -135280, 0]], ![![514311, 85844, 14370], ![-1221461, -45501, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {576} * I19N1 =  Ideal.span {B.equivFun.symm ![657, 170, 57]} * (J0 ^ 4*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_2 E19RS1 


noncomputable def E23RS1 : RelationCertificate Table 2 ![![23, 0, 0], ![-2, 1, 0]]
  ![-8617, 1082, -651] ![![2, 0, 0], ![-2, 0, 1]] where
    su := ![![46, 0, 0], ![-4, 2, 0]]
    hsu := by decide
    w := ![![-17234, 2164, -1302], ![-139912, 17568, -10570]]
    hw := by decide
    g := ![![![173, 7, 58], ![-143, 0, 0]], ![![140, 6, 57], ![-108, 3, 0]]]
    h := ![![![-387, -4115, 24981], ![-142, -95869, 0]], ![![-3144, -33406, 202805], ![-1178, -778300, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {2} * I23N1 =  Ideal.span {B.equivFun.symm ![-8617, 1082, -651]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E23RS1 


noncomputable def E29RS1 : RelationCertificate Table 2304 ![![29, 0, 0], ![-10, 1, 0]]
  ![315, -50, 51] ![![2304, 0, 0], ![802, 0, 1]] where
    su := ![![66816, 0, 0], ![-23040, 2304, 0]]
    hsu := by decide
    w := ![![725760, -115200, 117504], ![260352, -41472, 41472]]
    hw := by decide
    g := ![![![390623233810955, -2677490328297513, -59015678962], ![135972124350232, 7644284654767620, -27]], ![![-130211741944011, 892524175489939, 19672496908], ![-45325432883297, -2548173110692465, 9]]]
    h := ![![![1045, -107, 3], ![2999, -6, 0]], ![![387, -38, 0], ![1111, 3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {2304} * I29N1 =  Ideal.span {B.equivFun.symm ![315, -50, 51]} * (J0 ^ 6*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6J1_2 E29RS1 
