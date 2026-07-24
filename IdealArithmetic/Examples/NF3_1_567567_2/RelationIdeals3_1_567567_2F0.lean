import IdealArithmetic.Examples.NF3_1_567567_2.PrimesBelow3_1_567567_2F0
import IdealArithmetic.Examples.NF3_1_567567_2.ClassGroupData3_1_567567_2

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 2 ![![2, 0, 0], ![0, 1, 0]]
  ![915549, -277049, 27753] ![![2, 0, 0], ![18, 1, 1]] where
    su := ![![4, 0, 0], ![0, 2, 0]]
    hsu := by decide
    w := ![![1831098, -554098, 55506], ![-11029304, 3270706, -193128]]
    hw := by decide
    g := ![![![-33811067980, 40704552676, 50021048724], ![-258936811091, 7, 0]], ![![-58646398370, 70603371974, 86763137804], ![-449134330387, 0, 0]]]
    h := ![![![139163448, -29774608, -1359447], ![-14887302, 0, -2746647]], ![![-838227104, 179328866, 8223696], ![89664433, 0, 16543956]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {2} * I2N0 =  Ideal.span {B.equivFun.symm ![915549, -277049, 27753]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 1 ![![2, 0, 0], ![18, 1, 1]]
  ![1, 0, 0] ![![2, 0, 0], ![18, 1, 1]] where
    su := ![![2, 0, 0], ![18, 1, 1]]
    hsu := by decide
    w := ![![2, 0, 0], ![18, 1, 1]]
    hw := by decide
    g := ![![![-4, -14, -3], ![12, -2, 0]], ![![9, -123, -24], ![103, -18, 0]]]
    h := ![![![-4, -14, -3], ![12, -2, 0]], ![![9, -123, -24], ![103, -18, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {1} * I2N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS1 


noncomputable def E2RS2 : RelationCertificate Table 2 ![![2, 0, 0], ![18, 2, 1]]
  ![-15766478029, -591941569, -529812435] ![![2, 0, 0], ![18, 1, 1]] where
    su := ![![4, 0, 0], ![36, 4, 2]]
    hsu := by decide
    w := ![![-31532956058, -1183883138, -1059624870], ![-364369646224, -13680007652, -12244178386]]
    hw := by decide
    g := ![![![951, -8813, -2583], ![2920, 3, 0]], ![![-7233, 77326, 5778], ![-23503, 27, 0]]]
    h := ![![![-76229347892, 433571401930, -31653248817], ![-268319353410, 47299434087, 0]], ![![-880845438931, 5010004708848, -365759653230], ![-3100484068085, 546554469336, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N2 : Ideal.span {2} * I2N2 =  Ideal.span {B.equivFun.symm ![-15766478029, -591941569, -529812435]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS2 


noncomputable def E3RS0 : RelationCertificate Table 10 ![![3, 0, 0], ![-1, 1, 0]]
  ![-1129, 1029, -1487] ![![10, 0, 0], ![22, 1, 1]] where
    su := ![![30, 0, 0], ![-10, 10, 0]]
    hsu := by decide
    w := ![![-11290, 10290, -14870], ![26130, -12680, 10880]]
    hw := by decide
    g := ![![![732773792, -319341213, -35206895], ![1576647561, -406015592, 0]], ![![-301192280, 133055875, 14571689], ![-647860243, 169173065, 0]]]
    h := ![![![-58082, -5500, -127593], ![17529, 95323, 0]], ![![114891, 11108, 251464], ![-34592, -188326, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {10} * I3N0 =  Ideal.span {B.equivFun.symm ![-1129, 1029, -1487]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E3RS0 


noncomputable def E5RS0 : RelationCertificate Table 25 ![![5, 0, 0], ![17, 3, 1]]
  ![-3116797, -117018, -104736] ![![25, 0, 0], ![-1, 1, 0]] where
    su := ![![125, 0, 0], ![425, 75, 25]]
    hsu := by decide
    w := ![![-77919925, -2925450, -2618400], ![-7695575, -288925, -258600]]
    hw := by decide
    g := ![![![-7, -4, -48], ![10, 288, 0]], ![![-196, 32, -163], ![31, 1020, 0]]]
    h := ![![![-62560, 75561, 12041], ![-164941, 0, 0]], ![![-6182, 7462, 1189], ![-16289, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {25} * I5N0 =  Ideal.span {B.equivFun.symm ![-3116797, -117018, -104736]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 1 ![![5, 0, 0], ![-1, 1, 0]]
  ![1, 0, 0] ![![5, 0, 0], ![-1, 1, 0]] where
    su := ![![5, 0, 0], ![-1, 1, 0]]
    hsu := by decide
    w := ![![5, 0, 0], ![-1, 1, 0]]
    hw := by decide
    g := ![![![25, 0, 48], ![0, -60, 0]], ![![-5, -1, -12], ![6, 15, 0]]]
    h := ![![![25, 0, 48], ![0, -60, 0]], ![![-5, -1, -12], ![6, 15, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {1} * I5N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E5RS1 


noncomputable def E7RS0 : RelationCertificate Table 25 ![![7, 0, 0], ![0, 1, 0]]
  ![38567, 1448, 1296] ![![25, 0, 0], ![-1, 1, 0]] where
    su := ![![175, 0, 0], ![0, 25, 0]]
    hsu := by decide
    w := ![![964175, 36200, 32400], ![95225, 3575, 3200]]
    hw := by decide
    g := ![![![10, -1, 16], ![1, -96, 0]], ![![14, -3, 8], ![18, -54, 0]]]
    h := ![![![-1889783, -928491, -3790400], ![-132639, 6633524, 0]], ![![-186641, -91701, -374352], ![-13098, 655148, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {25} * I7N0 =  Ideal.span {B.equivFun.symm ![38567, 1448, 1296]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E7RS0 


noncomputable def E11RS0 : RelationCertificate Table 25 ![![11, 0, 0], ![3, 1, 0]]
  ![2642874934971, 99224920924, 88810449748] ![![25, 0, 0], ![-1, 1, 0]] where
    su := ![![275, 0, 0], ![75, 25, 0]]
    hsu := by decide
    w := ![![66071873374275, 2480623023100, 2220261243700], ![6525430331425, 244992791775, 219278784200]]
    hw := by decide
    g := ![![![10976, 357, -7324], ![-417, -444, 0]], ![![-64701, 19137, -1192], ![3358, -180, 0]]]
    h := ![![![-4834538658360, -11202829393423, -11416226125252], ![-2336949578943, 31416824456880, 0]], ![![-477471631855, -1106420614223, -1127496231356], ![-230803228160, 3102807424071, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {25} * I11N0 =  Ideal.span {B.equivFun.symm ![2642874934971, 99224920924, 88810449748]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 25 ![![11, 0, 0], ![5, 1, 0]]
  ![3765261, -1315216, 485768] ![![25, 0, 0], ![-1, 1, 0]] where
    su := ![![275, 0, 0], ![125, 25, 0]]
    hsu := by decide
    w := ![![94131525, -32880400, 12144200], ![42666875, -9350475, -6232400]]
    hw := by decide
    g := ![![![-605626094066, -23703847167, -20382582152], ![23276889879, 1068, 0]], ![![-466280621065, -18249947761, -15692855920], ![17921226942, 516, 0]]]
    h := ![![![1276811091, 5165611988, 3507499728], ![1049969776, -9645502810, 0]], ![![570683002, 2308834644, 1567665248], ![469295433, -4311141756, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {25} * I11N1 =  Ideal.span {B.equivFun.symm ![3765261, -1315216, 485768]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E11RS1 


noncomputable def E13RS0 : RelationCertificate Table 50 ![![13, 0, 0], ![2, 1, 0]]
  ![20016321, 751499, 672623] ![![50, 0, 0], ![12, 1, 1]] where
    su := ![![650, 0, 0], ![100, 50, 0]]
    hsu := by decide
    w := ![![1000816050, 37574950, 33631150], ![342487300, 12858450, 11508850]]
    hw := by decide
    g := ![![![166924676749, -24775403385, 4346005449], ![39653334481, -85651202392, 0]], ![![22470629509, -3335150439, 585039187], ![5337948878, -11529969547, 0]]]
    h := ![![![-121963607, -190336391, -257233333], ![-33404882, 836176488, 0]], ![![-41736928, -65134644, -88027315], ![-11431413, 286146318, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {50} * I13N0 =  Ideal.span {B.equivFun.symm ![20016321, 751499, 672623]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 50 ![![13, 0, 0], ![-4, 1, 0]]
  ![-699, 219, -37] ![![50, 0, 0], ![12, 1, 1]] where
    su := ![![650, 0, 0], ![-200, 50, 0]]
    hsu := by decide
    w := ![![-34950, 10950, -1850], ![12800, -3950, 550]]
    hw := by decide
    g := ![![![28608212, -4246559, 744824], ![6795941, -14680508, 0]], ![![-6519592, 967673, -169742], ![-1548732, 3345337, 0]]]
    h := ![![![897, -1557, 2135], ![-384, -6948, 0]], ![![-326, 569, -781], ![147, 2541, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {50} * I13N1 =  Ideal.span {B.equivFun.symm ![-699, 219, -37]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E13RS1 


noncomputable def E17RS1 : RelationCertificate Table 10 ![![17, 0, 0], ![3, 1, 0]]
  ![153812727, 5774793, 5168681] ![![10, 0, 0], ![22, 1, 1]] where
    su := ![![170, 0, 0], ![30, 10, 0]]
    hsu := by decide
    w := ![![1538127270, 57747930, 51686810], ![4169924870, 156556960, 140125020]]
    hw := by decide
    g := ![![![359, -556, -3], ![789, -60, 0]], ![![163, -158, -123], ![331, -33, 0]]]
    h := ![![![-17208127437, -35949123347, -36252181511], ![-5151382676, 154073063592, 0]], ![![-46651925339, -97459518742, -98281121610], ![-13965605562, 417698269968, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {10} * I17N1 =  Ideal.span {B.equivFun.symm ![153812727, 5774793, 5168681]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E17RS1 


noncomputable def E29RS1 : RelationCertificate Table 20 ![![29, 0, 0], ![0, 1, 0]]
  ![-4420168087533, -165952169417, -148534124949] ![![20, 0, 0], ![12, 1, 1]] where
    su := ![![580, 0, 0], ![0, 20, 0]]
    hsu := by decide
    w := ![![-88403361750660, -3319043388340, -2970682498980], ![-75630853123460, -2839508340440, -2541478596600]]
    hw := by decide
    g := ![![![-3654140744807117980, 780215086563990849, -36332036390886781], ![-2155290294375615567, 960643674064530904, 0]], ![![31501213317334892, -6725992125567447, 313207210270319], ![18580088744636084, -8281410983314919, 0]]]
    h := ![![![172386555413787, 86161313985574, 345072828139647], ![2971079792615, -2501815137543678, 0]], ![![147480163590747, 73712736189228, 295216741367098], ![2541818489284, -2140353143393918, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {20} * I29N1 =  Ideal.span {B.equivFun.symm ![-4420168087533, -165952169417, -148534124949]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E29RS1 


noncomputable def E31RS1 : RelationCertificate Table 4 ![![31, 0, 0], ![13, 1, 0]]
  ![9, -3, 1] ![![4, 0, 0], ![20, 1, 1]] where
    su := ![![124, 0, 0], ![52, 4, 0]]
    hsu := by decide
    w := ![![36, -12, 4], ![-92, 32, -8]]
    hw := by decide
    g := ![![![-55, 113, 18], ![-183, 42, 0]], ![![-25, 51, 8], ![-81, 19, 0]]]
    h := ![![![-675, -6051, -1733], ![-456, 13431, 0]], ![![1703, 15480, 4434], ![1224, -34364, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {4} * I31N1 =  Ideal.span {B.equivFun.symm ![9, -3, 1]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E31RS1 
