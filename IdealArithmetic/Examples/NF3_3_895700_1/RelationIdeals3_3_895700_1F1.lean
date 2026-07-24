import IdealArithmetic.Examples.NF3_3_895700_1.PrimesBelow3_3_895700_1F1
import IdealArithmetic.Examples.NF3_3_895700_1.ClassGroupData3_3_895700_1

set_option linter.all false

noncomputable section


noncomputable def E37RS0 : RelationCertificate Table 361 ![![37, 0, 0], ![8, 1, 0]]
  ![-151, 38, -2] ![![361, 0, 0], ![37, 1, 0]] where
    su := ![![13357, 0, 0], ![2888, 361, 0]]
    hsu := by decide
    w := ![![-54511, 13718, -722], ![-4693, 1083, 0]]
    hw := by decide
    g := ![![![-55388982, -2092873881, -113130036], ![-11474284, 20419971495, 0]], ![![-15315375, -578690748, -31281056], ![-3172434, 5646230607, 0]]]
    h := ![![![707205, 6203521, 1553046], ![320577, -28731352, 0]], ![![60794, 533295, 133510], ![27568, -2469935, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N0 : Ideal.span {361} * I37N0 =  Ideal.span {B.equivFun.symm ![-151, 38, -2]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E37RS0 


noncomputable def E37RS1 : RelationCertificate Table 3 ![![37, 0, 0], ![13, 1, 0]]
  ![-88, 9, 2] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![111, 0, 0], ![39, 3, 0]]
    hsu := by decide
    w := ![![-264, 27, 6], ![-759, 75, 18]]
    hw := by decide
    g := ![![![61, 28, -58], ![-8, 85, 0]], ![![35, 11, -22], ![-6, 32, 0]]]
    h := ![![![582, 9931, 1530], ![514, -28304, 0]], ![![1703, 28549, 4398], ![1392, -81360, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {3} * I37N1 =  Ideal.span {B.equivFun.symm ![-88, 9, 2]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E37RS1 


noncomputable def E37RS2 : RelationCertificate Table 171 ![![37, 0, 0], ![15, 1, 0]]
  ![-605, 0, 13] ![![171, 0, 0], ![-1, 1, 0]] where
    su := ![![6327, 0, 0], ![2565, 171, 0]]
    hsu := by decide
    w := ![![-103455, 0, 2223], ![-4959, 513, 0]]
    hw := by decide
    g := ![![![-152, 143, -285], ![103, 24387, 0]], ![![-70, 64, -128], ![126, 10957, 0]]]
    h := ![![![-370710, -7735923, -1032751], ![-359349, 19105900, 0]], ![![-18141, -378485, -50528], ![-17572, 934768, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N2 : Ideal.span {171} * I37N2 =  Ideal.span {B.equivFun.symm ![-605, 0, 13]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E37RS2 


noncomputable def E41RS1 : RelationCertificate Table 171 ![![41, 0, 0], ![-11, 1, 0]]
  ![259, 0, -5] ![![171, 0, 0], ![-1, 1, 0]] where
    su := ![![7011, 0, 0], ![-1881, 171, 0]]
    hsu := by decide
    w := ![![44289, 0, -855], ![1881, -171, 0]]
    hw := by decide
    g := ![![![703, -704, 1407], ![113, -120296, 0]], ![![-175, 175, -352], ![170, 30096, 0]]]
    h := ![![![-1407, 18046, -3285], ![854, 67340, 0]], ![![-59, 769, -140], ![40, 2870, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {171} * I41N1 =  Ideal.span {B.equivFun.symm ![259, 0, -5]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E41RS1 


noncomputable def E53RS0 : RelationCertificate Table 57 ![![53, 0, 0], ![6, 1, 0]]
  ![548, -57, -13] ![![57, 0, 0], ![-1, 1, 0]] where
    su := ![![3021, 0, 0], ![342, 57, 0]]
    hsu := by decide
    w := ![![31236, -3249, -741], ![4959, -513, -114]]
    hw := by decide
    g := ![![![25, -30, 59], ![46, -1680, 0]], ![![-58553, 58552, -117177], ![2082, 3339545, 0]]]
    h := ![![![-1646, -10161, -3389], ![-336, 89802, 0]], ![![-261, -1613, -538], ![-56, 14256, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N0 : Ideal.span {57} * I53N0 =  Ideal.span {B.equivFun.symm ![548, -57, -13]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E53RS0 


noncomputable def E53RS1 : RelationCertificate Table 57 ![![53, 0, 0], ![-13, 1, 0]]
  ![-115, 0, 2] ![![57, 0, 0], ![-1, 1, 0]] where
    su := ![![3021, 0, 0], ![-741, 57, 0]]
    hsu := by decide
    w := ![![-6555, 0, 114], ![-741, 57, 0]]
    hw := by decide
    g := ![![![-4123475, 4123476, -8252030], ![144710, 235182854, 0]], ![![860316, -860316, 1721690], ![-30152, -49068165, 0]]]
    h := ![![![192, -2819, 434], ![-93, -11500, 0]], ![![25, -325, 50], ![1, -1325, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {57} * I53N1 =  Ideal.span {B.equivFun.symm ![-115, 0, 2]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E53RS1 


noncomputable def E61RS1 : RelationCertificate Table 1083 ![![61, 0, 0], ![27, 1, 0]]
  ![1555, -114, -32] ![![1083, 0, 0], ![398, 1, 0]] where
    su := ![![66063, 0, 0], ![29241, 1083, 0]]
    hsu := by decide
    w := ![![1684065, -123462, -34656], ![632472, -46569, -12996]]
    hw := by decide
    g := ![![![5620, 3101610, 15586], ![5914, -8439823, 0]], ![![2613, 1471802, 7396], ![2953, -4004936, 0]]]
    h := ![![![-19626, -788149, -58408], ![-21581, 1781428, 0]], ![![-7393, -296002, -21936], ![-8055, 669042, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {1083} * I61N1 =  Ideal.span {B.equivFun.symm ![1555, -114, -32]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E61RS1 


noncomputable def E67RS1 : RelationCertificate Table 3 ![![67, 0, 0], ![3, 1, 0]]
  ![-62, 3, 1] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![201, 0, 0], ![9, 3, 0]]
    hsu := by decide
    w := ![![-186, 9, 3], ![-363, 21, 6]]
    hw := by decide
    g := ![![![-30213, 30208, -73845], ![20142, 110768, 0]], ![![-1479, 1477, -3612], ![988, 5418, 0]]]
    h := ![![![331, 1000, 667], ![35, -22344, 0]], ![![646, 1952, 1302], ![71, -43616, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {3} * I67N1 =  Ideal.span {B.equivFun.symm ![-62, 3, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E67RS1 


noncomputable def E71RS1 : RelationCertificate Table 9 ![![71, 0, 0], ![-4, 1, 0]]
  ![-173, 18, 4] ![![9, 0, 0], ![-1, 1, 0]] where
    su := ![![639, 0, 0], ![-36, 9, 0]]
    hsu := by decide
    w := ![![-1557, 162, 36], ![-1521, 153, 36]]
    hw := by decide
    g := ![![![-37, 64, -134], ![19, 601, 0]], ![![5, -4, 6], ![8, -27, 0]]]
    h := ![![![642, -2587, 1294], ![-45, -45935, 0]], ![![627, -2527, 1264], ![-46, -44870, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {9} * I71N1 =  Ideal.span {B.equivFun.symm ![-173, 18, 4]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E71RS1 


noncomputable def E73RS1 : RelationCertificate Table 3249 ![![73, 0, 0], ![-12, 1, 0]]
  ![19112, -1881, -433] ![![3249, 0, 0], ![-685, 1, 0]] where
    su := ![![237177, 0, 0], ![-38988, 3249, 0]]
    hsu := by decide
    w := ![![62094888, -6111369, -1406817], ![-12908277, 1270359, 292410]]
    hw := by decide
    g := ![![![-24654, 18810437, -54921], ![13309, 89219158, 0]], ![![4363, -2799938, 8175], ![1307, -13280288, 0]]]
    h := ![![![-358751101, 4542431455, -757348627], ![121197932, 27643224669, 0]], ![![74577076, -944279185, 157437388], ![-25194508, -5746464617, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {3249} * I73N1 =  Ideal.span {B.equivFun.symm ![19112, -1881, -433]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E73RS1 
