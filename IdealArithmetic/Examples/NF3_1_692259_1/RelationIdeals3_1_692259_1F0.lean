import IdealArithmetic.Examples.NF3_1_692259_1.PrimesBelow3_1_692259_1F0
import IdealArithmetic.Examples.NF3_1_692259_1.ClassGroupData3_1_692259_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 4 ![![2, 0, 0], ![10, 0, 1]]
  ![15400, -7058, 1899] ![![4, 0, 0], ![1, 1, 0]] where
    su := ![![8, 0, 0], ![40, 0, 4]]
    hsu := by decide
    w := ![![61600, -28232, 7596], ![314904, -14984, -17376]]
    hw := by decide
    g := ![![![-118234976, -49891, -4721703], ![-29571214, 3, 0]], ![![-1370505479, -578298, -54730996], ![-342770943, 14, 0]]]
    h := ![![![275, -3529, 207], ![1485, 0, 0]], ![![2073, -1873, -5901], ![7458, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {4} * I2N0 =  Ideal.span {B.equivFun.symm ![15400, -7058, 1899]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E2RS0 


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


noncomputable def E3RS0 : RelationCertificate Table 4 ![![3, 0, 0], ![10, 0, 1]]
  ![859376, -97914, -22639] ![![4, 0, 0], ![1, 1, 0]] where
    su := ![![12, 0, 0], ![40, 0, 4]]
    hsu := by decide
    w := ![![3437504, -391656, -90556], ![-2529116, 1221600, -339020]]
    hw := by decide
    g := ![![![-95234090512, -40184911, -3803162952], ![-23818568853, 46, 0]], ![![-735929121479, -310532136, -29389248528], ![-184059913402, 138, 0]]]
    h := ![![![-3661372, -16547466, 5270155], ![-10447834, 0, 1077054]], ![![11486807, 51612600, -16551335], ![32772250, 0, -3359400]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {4} * I3N0 =  Ideal.span {B.equivFun.symm ![859376, -97914, -22639]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 4 ![![3, 0, 0], ![11, 0, 1]]
  ![471440, 27930, 17719] ![![4, 0, 0], ![1, 1, 0]] where
    su := ![![12, 0, 0], ![44, 0, 4]]
    hsu := by decide
    w := ![![1885760, 111720, 70876], ![3172236, 187936, 119228]]
    hw := by decide
    g := ![![![-247, 40, 176], ![-51, -230, 0]], ![![543, -25, 558], ![133, -828, 0]]]
    h := ![![![-97166, 55860, 103817], ![-321662, 27930, 0]], ![![-163459, 93968, 174641], ![-541100, 46984, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {4} * I3N1 =  Ideal.span {B.equivFun.symm ![471440, 27930, 17719]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E3RS1 


noncomputable def E7RS0 : RelationCertificate Table 4 ![![7, 0, 0], ![10, -1, 1]]
  ![-428, 54, 9] ![![4, 0, 0], ![1, 1, 0]] where
    su := ![![28, 0, 0], ![40, -4, 4]]
    hsu := by decide
    w := ![![-1712, 216, 36], ![904, -572, 180]]
    hw := by decide
    g := ![![![-7133153, 419794, 22668942], ![-1678339, -30225079, 0]], ![![-10186683, 599707, 32384356], ![-2396741, -43178700, 0]]]
    h := ![![![-24, 4, 5], ![-26, 0, 0]], ![![8, -18, 4], ![17, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {4} * I7N0 =  Ideal.span {B.equivFun.symm ![-428, 54, 9]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 2 ![![7, 0, 0], ![2, 1, 0]]
  ![-248, 64, -9] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![14, 0, 0], ![4, 2, 0]]
    hsu := by decide
    w := ![![-496, 128, -18], ![-1698, -104, 174]]
    hw := by decide
    g := ![![![-55869, 7958, -2550], ![-23955, 0, 0]], ![![-61685, 8786, -2820], ![-26448, 3, 0]]]
    h := ![![![402, -451, -1359], ![53, 3168, 0]], ![![1267, -1463, -4287], ![157, 10032, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {2} * I7N1 =  Ideal.span {B.equivFun.symm ![-248, 64, -9]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E7RS1 


noncomputable def E23RS1 : RelationCertificate Table 4 ![![23, 0, 0], ![-4, 1, 0]]
  ![-2275332, 570390, -75275] ![![4, 0, 0], ![1, 1, 0]] where
    su := ![![92, 0, 0], ![-16, 4, 0]]
    hsu := by decide
    w := ![![-9101328, 2281560, -301100], ![-14438072, -1070932, 1560620]]
    hw := by decide
    g := ![![![-1288140598486, 710096770, 16617665441], ![-321857625425, -89619190213, 0]], ![![-91554075462, -256656384, -15492622521], ![-22952682961, 15585946138, 0]]]
    h := ![![![3342292, 17083445, -10242673], ![161495, 78502068, 0]], ![![5199028, 26540141, -15920621], ![249754, 122188146, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {4} * I23N1 =  Ideal.span {B.equivFun.symm ![-2275332, 570390, -75275]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E23RS1 


noncomputable def E23RS2 : RelationCertificate Table 2 ![![23, 0, 0], ![-1, 1, 0]]
  ![-707978, 236238, -48957] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![46, 0, 0], ![-2, 2, 0]]
    hsu := by decide
    w := ![![-1415956, 472476, -97914], ![-8483594, 75334, 610800]]
    hw := by decide
    g := ![![![-810548777021, 115457623616, -36995574156], ![-347545576702, -69, 0]], ![![-166649612184, 23738199038, -7606325844], ![-71455706573, 6, 0]]]
    h := ![![![26142261, 52208531, -78373431], ![1133329, 600846652, 0]], ![![154348732, 308195476, -462713718], ![6688995, 3547573638, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N2 : Ideal.span {2} * I23N2 =  Ideal.span {B.equivFun.symm ![-707978, 236238, -48957]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E23RS2 


noncomputable def E29RS0 : RelationCertificate Table 4 ![![29, 0, 0], ![9, 1, 0]]
  ![5410040, -1238694, 127911] ![![4, 0, 0], ![1, 1, 0]] where
    su := ![![116, 0, 0], ![36, 4, 0]]
    hsu := by decide
    w := ![![21640160, -4954776, 511644], ![26347028, 3363464, -3460260]]
    hw := by decide
    g := ![![![6034790743569, 2546435714, 240998685528], ![1509334294825, 24024, 0]], ![![2886829973720, 11774630507, 688392214785], ![724651151061, -754655042071, 0]]]
    h := ![![![-256432589, 2073275563, 777394149], ![-8090261, -7514767470, 0]], ![![-303787040, 2456257932, 920932140], ![-9580162, -8902632375, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N0 : Ideal.span {4} * I29N0 =  Ideal.span {B.equivFun.symm ![5410040, -1238694, 127911]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E29RS0 


noncomputable def E29RS1 : RelationCertificate Table 4 ![![29, 0, 0], ![10, 1, 0]]
  ![-175062959004, -10371433130, -6579714321] ![![4, 0, 0], ![1, 1, 0]] where
    su := ![![116, 0, 0], ![40, 4, 0]]
    hsu := by decide
    w := ![![-700251836016, -41485732520, -26318857284], ![-1177967531308, -69787529868, -44273728032]]
    hw := by decide
    g := ![![![8897511456603849, -523383026902211, -28262683450410327], ![2093532107425410, 37683577933908725, 0]], ![![2761296659054107, -162429215263440, -8771177622544584], ![649716860947667, 11694903496730517, 0]]]
    h := ![![![1821250673666, -16618429899087, -5538952489845], ![54968166841, 53541014163728, 0]], ![![3063718007741, -27955615159565, -9317656669944], ![92467755814, 90066991665456, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {4} * I29N1 =  Ideal.span {B.equivFun.symm ![-175062959004, -10371433130, -6579714321]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E29RS1 
