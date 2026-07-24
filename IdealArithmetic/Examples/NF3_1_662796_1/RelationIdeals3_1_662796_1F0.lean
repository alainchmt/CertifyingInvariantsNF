import IdealArithmetic.Examples.NF3_1_662796_1.PrimesBelow3_1_662796_1F0
import IdealArithmetic.Examples.NF3_1_662796_1.ClassGroupData3_1_662796_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 35 ![![2, 0, 0], ![15, 0, 1]]
  ![1263, 29, 53] ![![35, 0, 0], ![27, 0, 1]] where
    su := ![![70, 0, 0], ![525, 0, 35]]
    hsu := by decide
    w := ![![44205, 1015, 1855], ![35000, 805, 1470]]
    hw := by decide
    g := ![![![290458190, 22044131, -17409790], ![223570356, -192886146, 0]], ![![2178436519, 165330981, -130573420], ![1676777529, -1446646088, 0]]]
    h := ![![![-168, 13021, -5096], ![-3762, 0, -2001]], ![![-139, 10327, -4042], ![-2983, 0, -1587]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {35} * I2N0 =  Ideal.span {B.equivFun.symm ![1263, 29, 53]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E2RS0 


noncomputable def E3RS0 : RelationCertificate Table 4375 ![![3, 0, 0], ![1, 1, 0]]
  ![-12, -11, -37] ![![4375, 0, 0], ![377, 0, 1]] where
    su := ![![13125, 0, 0], ![4375, 4375, 0]]
    hsu := by decide
    w := ![![-52500, -48125, -161875], ![-4375, -4375, -13125]]
    hw := by decide
    g := ![![![110, 524, -3], ![166, -6476, 0]], ![![134799, 573257, -3242], ![14251, -7084744, 0]]]
    h := ![![![-4, -2, -9], ![-2, -1, 0]], ![![0, 0, -1], ![-1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {4375} * I3N0 =  Ideal.span {B.equivFun.symm ![-12, -11, -37]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E3RS0 


noncomputable def E5RS0 : RelationCertificate Table 5 ![![5, 0, 0], ![1, 1, 0]]
  ![-47, -1, -2] ![![5, 0, 0], ![17, 0, 1]] where
    su := ![![25, 0, 0], ![5, 5, 0]]
    hsu := by decide
    w := ![![-235, -5, -10], ![-825, -20, -35]]
    hw := by decide
    g := ![![![-2091, 1771, 1926], ![-6678, 1476, 0]], ![![-873, 738, 802], ![-2782, 615, 0]]]
    h := ![![![-1514, 464, 18], ![-205, 0, 92]], ![![-5296, 1627, 63], ![-733, 0, 322]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {5} * I5N0 =  Ideal.span {B.equivFun.symm ![-47, -1, -2]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 78125 ![![5, 0, 0], ![15, 0, 1]]
  ![-42, 274, 183] ![![78125, 0, 0], ![6002, 0, 1]] where
    su := ![![390625, 0, 0], ![1171875, 0, 78125]]
    hsu := by decide
    w := ![![-3281250, 21406250, 14296875], ![-234375, 1640625, 1093750]]
    hw := by decide
    g := ![![![4209400, 301424630, -100832], ![330183, -3938584917, 0]], ![![12624131, 904271877, -302496], ![1043145, -11815728448, 0]]]
    h := ![![![-90, 122, 95], ![-208, 42, 0]], ![![-6, 9, 7], ![-15, 3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {78125} * I5N1 =  Ideal.span {B.equivFun.symm ![-42, 274, 183]} * (J0 ^ 7*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7J1_0 E5RS1 


noncomputable def E5RS2 : RelationCertificate Table 1 ![![5, 0, 0], ![17, 0, 1]]
  ![1, 0, 0] ![![5, 0, 0], ![17, 0, 1]] where
    su := ![![5, 0, 0], ![17, 0, 1]]
    hsu := by decide
    w := ![![5, 0, 0], ![17, 0, 1]]
    hw := by decide
    g := ![![![-16, 0, -1], ![5, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![-16, 0, -1], ![5, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N2 : Ideal.span {1} * I5N2 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E5RS2 


noncomputable def E7RS0 : RelationCertificate Table 6125 ![![7, 0, 0], ![13, 2, 1]]
  ![-55812, -1286, -2337] ![![6125, 0, 0], ![1252, 0, 1]] where
    su := ![![42875, 0, 0], ![79625, 12250, 6125]]
    hsu := by decide
    w := ![![-341848500, -7876750, -14314125], ![-69916875, -1610875, -2927750]]
    hw := by decide
    g := ![![![-253876, -3859122, 6288], ![-48375, 19232809, 0]], ![![-471885, -7188111, 11713], ![-94956, 35823580, 0]]]
    h := ![![![-1891, 752, 134], ![-3275, 0, 0]], ![![-392, 153, 27], ![-667, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {6125} * I7N0 =  Ideal.span {B.equivFun.symm ![-55812, -1286, -2337]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 1953125 ![![7, 0, 0], ![3, 1, 0]]
  ![-48268, -1329, -1743] ![![13671875, 0, 0], ![2896627, 0, 1]] where
    su := ![![13671875, 0, 0], ![5859375, 1953125, 0]]
    hsu := by decide
    w := ![![-659914062500, -18169921875, -23830078125], ![-139814453125, -3849609375, -5048828125]]
    hw := by decide
    g := ![![![-267844126931992038323, -9650763100661394721967652, 6663506031262601558], ![-56747485125412444237, 45551282386841627631668496, 0]], ![![-108413098996277502227, -3906261255029457066667779, 2697133393606184028], ![-22969220169812121809, 18437423823244688722845284, 0]]]
    h := ![![![-6395949486950, 16462617705923, 32814001504397], ![-389318679274, -22969801054298, 0]], ![![-1355094917482, 3487896461230, 6952226053625], ![-82484041601, -4866558237796, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {1953125} * I7N1 =  Ideal.span {B.equivFun.symm ![-48268, -1329, -1743]} * (J0 ^ 8*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8J1_1 E7RS1 


noncomputable def E11RS0 : RelationCertificate Table 15625 ![![11, 0, 0], ![0, 1, 0]]
  ![1261, -42, 86] ![![15625, 0, 0], ![6002, 0, 1]] where
    su := ![![171875, 0, 0], ![0, 15625, 0]]
    hsu := by decide
    w := ![![19703125, -656250, 1343750], ![7562500, -250000, 515625]]
    hw := by decide
    g := ![![![56157, 4626334, -1549], ![23011, -12090060, 0]], ![![1066, 312245, -105], ![8645, -815994, 0]]]
    h := ![![![-39404989, 39082107, 197025526], ![3552921, -216728070, 0]], ![![-15124516, 15000586, 75622803], ![1363698, -83185080, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {15625} * I11N0 =  Ideal.span {B.equivFun.symm ![1261, -42, 86]} * (J0 ^ 6*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6J1_0 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 13671875 ![![11, 0, 0], ![5, 1, 0]]
  ![-37547, 3134, 12928] ![![13671875, 0, 0], ![2896627, 0, 1]] where
    su := ![![150390625, 0, 0], ![68359375, 13671875, 0]]
    hsu := by decide
    w := ![![-513337890625, 42847656250, 176750000000], ![-108759765625, 9078125000, 37447265625]]
    hw := by decide
    g := ![![![15836372236552835704576, 570604547426456923604312938, -393981989152908050843], ![3355213751476478386555, -2693234576368081640570376879, 0]], ![![6910416975950341950140, 248991075240636238696615455, -171919413448542033389], ![1464093273371556910893, -1175229633324256120591661623, 0]]]
    h := ![![![-8849972144691, 32735380826151, 46628885479718], ![-1046770899748, -51291774026397, 0]], ![![-1875024225288, 6935573476330, 9879159893739], ![-221777059093, -10867075882839, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {13671875} * I11N1 =  Ideal.span {B.equivFun.symm ![-37547, 3134, 12928]} * (J0 ^ 8*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8J1_1 E11RS1 


noncomputable def E11RS2 : RelationCertificate Table 765625 ![![11, 0, 0], ![-5, 1, 0]]
  ![-8227, 844, 1248] ![![765625, 0, 0], ![381002, 0, 1]] where
    su := ![![8421875, 0, 0], ![-3828125, 765625, 0]]
    hsu := by decide
    w := ![![-6298796875, 646187500, 955500000], ![-3134468750, 321562500, 475453125]]
    hw := by decide
    g := ![![![4775367536716409, 27022040212664009610, -141858902800307], ![2376391106732743, -54304173032689157034, 0]], ![![-1845032464951469, -10440356907648441273, 54809243273514], ![-918153147761062, 20981204364068197590, 0]]]
    h := ![![![2154, 4843, -15612], ![-535, 17298, 0]], ![![1072, 2410, -7769], ![-266, 8608, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N2 : Ideal.span {765625} * I11N2 =  Ideal.span {B.equivFun.symm ![-8227, 844, 1248]} * (J0 ^ 4*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_2 E11RS2 


noncomputable def E13RS0 : RelationCertificate Table 175 ![![13, 0, 0], ![2, 1, 0]]
  ![-83, 26, -8] ![![175, 0, 0], ![27, 0, 1]] where
    su := ![![2275, 0, 0], ![350, 175, 0]]
    hsu := by decide
    w := ![![-14525, 4550, -1400], ![175, 0, -175]]
    hw := by decide
    g := ![![![-86364, -4210, 2181], ![-13239, 184194, 0]], ![![-17623, -859, 445], ![-2687, 37584, 0]]]
    h := ![![![-475, 935, 2334], ![11, -3035, 0]], ![![5, -11, -27], ![3, 35, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {175} * I13N0 =  Ideal.span {B.equivFun.symm ![-83, 26, -8]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 19140625 ![![13, 0, 0], ![3, 1, 0]]
  ![-1443068, -35104, -62793] ![![19140625, 0, 0], ![-8040873, 0, 1]] where
    su := ![![248828125, 0, 0], ![57421875, 19140625, 0]]
    hsu := by decide
    w := ![![-27621223437500, -671912500000, -1201897265625], ![11603525390625, 282266796875, 504910546875]]
    hw := by decide
    g := ![![![3152887600, -354417573295709, -88153683], ![-1308205272, -843658948438480, 0]], ![![1167601464, -130935433266748, -32567349], ![-476626562, -311679945539819, 0]]]
    h := ![![![-491683120387505, 1240980495133773, 2479190944516299], ![-18005297386813, -3222948227877468, 0]], ![![206553398456565, -521329140781115, -1041494600443077], ![7563927276052, 1353942980578638, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {19140625} * I13N1 =  Ideal.span {B.equivFun.symm ![-1443068, -35104, -62793]} * (J0 ^ 6*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6J1_2 E13RS1 


noncomputable def E13RS2 : RelationCertificate Table 25 ![![13, 0, 0], ![-5, 1, 0]]
  ![23, -6, -2] ![![25, 0, 0], ![27, 0, 1]] where
    su := ![![325, 0, 0], ![-125, 25, 0]]
    hsu := by decide
    w := ![![575, -150, -50], ![175, -50, 25]]
    hw := by decide
    g := ![![![233, 26, -24], ![298, -160, 0]], ![![-93, -9, 8], ![-90, 56, 0]]]
    h := ![![![-32, -57, 186], ![9, -242, 0]], ![![-7, -18, 57], ![10, -74, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N2 : Ideal.span {25} * I13N2 =  Ideal.span {B.equivFun.symm ![23, -6, -2]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E13RS2 


noncomputable def E17RS0 : RelationCertificate Table 625 ![![17, 0, 0], ![3, 1, 0]]
  ![1746, 38, 71] ![![625, 0, 0], ![-248, 0, 1]] where
    su := ![![10625, 0, 0], ![1875, 625, 0]]
    hsu := by decide
    w := ![![1091250, 23750, 44375], ![-431875, -9375, -17500]]
    hw := by decide
    g := ![![![-135082, 505255, 3642], ![54255, 1165256, 0]], ![![-24632, 92114, 664], ![9879, 212440, 0]]]
    h := ![![![88362, -221918, -443537], ![2544, 754020, 0]], ![![-34850, 87516, 174916], ![-987, -297360, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N0 : Ideal.span {625} * I17N0 =  Ideal.span {B.equivFun.symm ![1746, 38, 71]} * (J0 ^ 4*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_0 E17RS0 


noncomputable def E17RS1 : RelationCertificate Table 5 ![![17, 0, 0], ![-6, 1, 0]]
  ![-6, 2, -1] ![![5, 0, 0], ![17, 0, 1]] where
    su := ![![85, 0, 0], ![-30, 5, 0]]
    hsu := by decide
    w := ![![-30, 10, -5], ![95, -25, -5]]
    hw := by decide
    g := ![![![-18477, 15737, 17116], ![-59341, 13113, 0]], ![![4754, -4061, -4418], ![15320, -3384, 0]]]
    h := ![![![-748, -1629, 4047], ![175, -6880, 0]], ![![2365, 5132, -12753], ![-529, 21680, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {5} * I17N1 =  Ideal.span {B.equivFun.symm ![-6, 2, -1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E17RS1 


noncomputable def E19RS0 : RelationCertificate Table 4375 ![![19, 0, 0], ![0, 1, 0]]
  ![963, -211, -312] ![![4375, 0, 0], ![377, 0, 1]] where
    su := ![![83125, 0, 0], ![0, 4375, 0]]
    hsu := by decide
    w := ![![4213125, -923125, -1365000], ![354375, -78750, -109375]]
    hw := by decide
    g := ![![![-428029, -1815733, 10266], ![-32720, 22440204, 0]], ![![-7496, -30555, 172], ![2858, 377622, 0]]]
    h := ![![![-8425287, 8402052, 42126672], ![442217, -80040708, 0]], ![![-708669, 706714, 3543365], ![37208, -6732396, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N0 : Ideal.span {4375} * I19N0 =  Ideal.span {B.equivFun.symm ![963, -211, -312]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E19RS0 


noncomputable def E31RS1 : RelationCertificate Table 15625 ![![31, 0, 0], ![-2, 1, 0]]
  ![1687, -589, 462] ![![15625, 0, 0], ![6002, 0, 1]] where
    su := ![![484375, 0, 0], ![-31250, 15625, 0]]
    hsu := by decide
    w := ![![26359375, -9203125, 7218750], ![10062500, -3515625, 2765625]]
    hw := by decide
    g := ![![![-1591365036087, -129984652088502, 43519521003], ![-611285071045, 339690615300693, 0]], ![![-391432618326, -31972696991223, 10704621167], ![-150359526721, 83554673103840, 0]]]
    h := ![![![-805835109, -1675352, 4045929162], ![51935323, -12542380356, 0]], ![![-307626478, -639564, 1544528067], ![19826259, -4788036990, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {15625} * I31N1 =  Ideal.span {B.equivFun.symm ![1687, -589, 462]} * (J0 ^ 6*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6J1_0 E31RS1 
