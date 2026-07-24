import IdealArithmetic.Examples.NF3_1_538412_3.PrimesBelow3_1_538412_3F3
import IdealArithmetic.Examples.NF3_1_538412_3.ClassGroupData3_1_538412_3

set_option linter.all false

noncomputable section


noncomputable def E149RS1 : RelationCertificate Table 5 ![![149, 0, 0], ![7, 1, 0]]
  ![152, 19, 15] ![![5, 0, 0], ![-1, 1, 0]] where
    su := ![![745, 0, 0], ![35, 5, 0]]
    hsu := by decide
    w := ![![760, 95, 75], ![2030, 260, 205]]
    hw := by decide
    g := ![![![17081, 1915, 119], ![-3033, 0, -596]], ![![746, 83, 5], ![-128, 0, -26]]]
    h := ![![![-93311, 233621, 467205], ![-2745, -6961353, 0]], ![![-249219, 623985, 1247869], ![-7493, -18593244, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R149N1 : Ideal.span {5} * I149N1 =  Ideal.span {B.equivFun.symm ![152, 19, 15]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E149RS1 


noncomputable def E151RS1 : RelationCertificate Table 25 ![![151, 0, 0], ![40, 1, 0]]
  ![34895688, 4421386, 3505315] ![![25, 0, 0], ![4, 1, 0]] where
    su := ![![3775, 0, 0], ![1000, 25, 0]]
    hsu := by decide
    w := ![![872392200, 110534650, 87632875], ![649526600, 82296925, 65245750]]
    hw := by decide
    g := ![![![-4243190692, 4344225363, 21620099035], ![-505141488, -54050247625, -250]], ![![-1188093538, 1216383136, 6053627716], ![-141439629, -15134069336, -70]]]
    h := ![![![-56356401368, 1108999807932, 291828852245], ![-7584478362, -4406615318368, 0]], ![![-41959318040, 825689265269, 217276819050], ![-5646910206, -3280879706672, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N1 : Ideal.span {25} * I151N1 =  Ideal.span {B.equivFun.symm ![34895688, 4421386, 3505315]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E151RS1 


noncomputable def E157RS1 : RelationCertificate Table 25 ![![157, 0, 0], ![-53, 1, 0]]
  ![-14, -8, 5] ![![25, 0, 0], ![4, 1, 0]] where
    su := ![![3925, 0, 0], ![-1325, 25, 0]]
    hsu := by decide
    w := ![![-350, -200, 125], ![700, 25, -50]]
    hw := by decide
    g := ![![![367104, -130184, -716523], ![53551, 1814668, -38936]], ![![-125100, 44361, 244165], ![-18225, -618373, 13268]]]
    h := ![![![607, 17243, -3135], ![-59, 49220, 0]], ![![-1160, -34729, 6314], ![304, -99130, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R157N1 : Ideal.span {25} * I157N1 =  Ideal.span {B.equivFun.symm ![-14, -8, 5]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E157RS1 


noncomputable def E163RS0 : RelationCertificate Table 5 ![![163, 0, 0], ![52, 1, 0]]
  ![858078, 108721, 86195] ![![5, 0, 0], ![-1, 1, 0]] where
    su := ![![815, 0, 0], ![260, 5, 0]]
    hsu := by decide
    w := ![![4290390, 543605, 430975], ![11681340, 1480060, 1173405]]
    hw := by decide
    g := ![![![82431390, 9270920, 576469], ![-14632094, 0, -2883684]], ![![26661888, 2998616, 186479], ![-4732652, 0, -932717]]]
    h := ![![![73177276, -1921537900, -384293005], ![11556371, 6263984601, 0]], ![![199237980, -5231724280, -1046305173], ![31464252, 17054797788, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R163N0 : Ideal.span {5} * I163N0 =  Ideal.span {B.equivFun.symm ![858078, 108721, 86195]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E163RS0 


noncomputable def E163RS1 : RelationCertificate Table 5 ![![163, 0, 0], ![-49, 1, 0]]
  ![995707, 126159, 100020] ![![5, 0, 0], ![-1, 1, 0]] where
    su := ![![815, 0, 0], ![-245, 5, 0]]
    hsu := by decide
    w := ![![4978535, 630795, 500100], ![13554935, 1717450, 1361610]]
    hw := by decide
    g := ![![![31664, 3860, 538], ![-5559, 0, -1292]], ![![-9262, -1163, -164], ![1621, 0, 388]]]
    h := ![![![111200061, 2952917977, -578984340], ![-15312148, 9437454744, 0]], ![![302761692, 8039837269, -1576386446], ![-41689955, 25695126302, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R163N1 : Ideal.span {5} * I163N1 =  Ideal.span {B.equivFun.symm ![995707, 126159, 100020]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E163RS1 


noncomputable def E163RS2 : RelationCertificate Table 5 ![![163, 0, 0], ![-3, 1, 0]]
  ![-19159, -2843, 2480] ![![5, 0, 0], ![-1, 1, 0]] where
    su := ![![815, 0, 0], ![-15, 5, 0]]
    hsu := by decide
    w := ![![-95795, -14215, 12400], ![391885, 16650, -25950]]
    hw := by decide
    g := ![![![26495983, 2330243, -1026396], ![-4833146, 0, -1364790]], ![![-1474073, -212064, -96650], ![252402, 0, 20370]]]
    h := ![![![240400, 601309, -1202630], ![-625, 19603117, 0]], ![![-985372, -2464769, 4929510], ![3017, -80351532, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R163N2 : Ideal.span {5} * I163N2 =  Ideal.span {B.equivFun.symm ![-19159, -2843, 2480]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E163RS2 


noncomputable def E173RS0 : RelationCertificate Table 5 ![![173, 0, 0], ![-78, 1, 0]]
  ![671271, 85052, 67430] ![![5, 0, 0], ![-1, 1, 0]] where
    su := ![![865, 0, 0], ![-390, 5, 0]]
    hsu := by decide
    w := ![![3356355, 425260, 337150], ![9138265, 1157845, 917950]]
    hw := by decide
    g := ![![![45726710, 5142315, 319704], ![-8116877, 0, -1599510]], ![![-20391825, -2293189, -142571], ![3619729, 0, 713295]]]
    h := ![![![-293462043, -12791695481, 1598920210], ![58372065, -27661312890, 0]], ![![-799002005, -34827633870, 4353340630], ![158927879, -75312774540, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R173N0 : Ideal.span {5} * I173N0 =  Ideal.span {B.equivFun.symm ![671271, 85052, 67430]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E173RS0 


noncomputable def E173RS1 : RelationCertificate Table 5 ![![173, 0, 0], ![-57, 1, 0]]
  ![-26779, -3393, -2690] ![![5, 0, 0], ![-1, 1, 0]] where
    su := ![![865, 0, 0], ![-285, 5, 0]]
    hsu := by decide
    w := ![![-133895, -16965, -13450], ![-364555, -46190, -36620]]
    hw := by decide
    g := ![![![-41653188, -4684578, -291460], ![7393725, 0, 1457188]], ![![13595976, 1529093, 95134], ![-2413375, 0, -475640]]]
    h := ![![![21538522, 666914859, -113033260], ![-3241389, 1955475129, 0]], ![![58642694, 1815804551, -307754888], ![-8825591, 5324158830, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R173N1 : Ideal.span {5} * I173N1 =  Ideal.span {B.equivFun.symm ![-26779, -3393, -2690]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E173RS1 


noncomputable def E173RS2 : RelationCertificate Table 5 ![![173, 0, 0], ![-38, 1, 0]]
  ![-3056, 318, -65] ![![5, 0, 0], ![-1, 1, 0]] where
    su := ![![865, 0, 0], ![-190, 5, 0]]
    hsu := by decide
    w := ![![-15280, 1590, -325], ![-7200, -4725, 3115]]
    hw := by decide
    g := ![![![-273237, -44398, -27407], ![45773, 0, 346]], ![![37802, 6098, 3711], ![-6336, 0, -77]]]
    h := ![![![-356102, -7280989, 1820195], ![36215, -31489380, 0]], ![![-166836, -3411093, 852751], ![16944, -14752530, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R173N2 : Ideal.span {5} * I173N2 =  Ideal.span {B.equivFun.symm ![-3056, 318, -65]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E173RS2 


noncomputable def E191RS0 : RelationCertificate Table 5 ![![191, 0, 0], ![49, 1, 0]]
  ![4121, -148, -80] ![![5, 0, 0], ![-1, 1, 0]] where
    su := ![![955, 0, 0], ![245, 5, 0]]
    hsu := by decide
    w := ![![20605, -740, -400], ![-15665, 3685, -1560]]
    hw := by decide
    g := ![![![-199240, -32921, -21004], ![33269, 0, -116]], ![![-66433, -10973, -6996], ![11094, 0, -36]]]
    h := ![![![-1467306, 35627559, 7580120], ![-189817, -144780300, 0]], ![![1121183, -27224239, -5792232], ![145186, 110631600, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R191N0 : Ideal.span {5} * I191N0 =  Ideal.span {B.equivFun.symm ![4121, -148, -80]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E191RS0 


noncomputable def E191RS1 : RelationCertificate Table 5 ![![191, 0, 0], ![-30, 1, 0]]
  ![-646, -82, -65] ![![5, 0, 0], ![-1, 1, 0]] where
    su := ![![955, 0, 0], ![-150, 5, 0]]
    hsu := by decide
    w := ![![-3230, -410, -325], ![-8810, -1115, -885]]
    hw := by decide
    g := ![![![-122682509, -13797424, -858369], ![21777019, 0, 4291826]], ![![18695774, 2102611, 130808], ![-3318632, 0, -654038]]]
    h := ![![![10762, 173938, -54355], ![-672, 1038174, 0]], ![![29320, 474429, -148257], ![-2050, 2831691, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R191N1 : Ideal.span {5} * I191N1 =  Ideal.span {B.equivFun.symm ![-646, -82, -65]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E191RS1 


noncomputable def E191RS2 : RelationCertificate Table 5 ![![191, 0, 0], ![-19, 1, 0]]
  ![21373057, 2708029, 2146950] ![![5, 0, 0], ![-1, 1, 0]] where
    su := ![![955, 0, 0], ![-95, 5, 0]]
    hsu := by decide
    w := ![![106865285, 13540145, 10734750], ![290959485, 36865420, 29227240]]
    hw := by decide
    g := ![![![236579, 27593, 3472], ![-41794, 0, -9168]], ![![-22989, -2808, -382], ![4038, 0, 936]]]
    h := ![![![2310795, 23216176, -11037060], ![-108226, 211022541, 0]], ![![6291522, 63210113, -30050332], ![-294893, 574545886, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R191N2 : Ideal.span {5} * I191N2 =  Ideal.span {B.equivFun.symm ![21373057, 2708029, 2146950]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E191RS2 


noncomputable def E193RS1 : RelationCertificate Table 25 ![![193, 0, 0], ![41, 1, 0]]
  ![-16047687, -2033289, -1612010] ![![25, 0, 0], ![4, 1, 0]] where
    su := ![![4825, 0, 0], ![1025, 25, 0]]
    hsu := by decide
    w := ![![-401192175, -50832225, -40300250], ![-298701650, -37846375, -30004950]]
    hw := by decide
    g := ![![![3059572993490109, -3132419969534258, -15589252871633436], ![364234880177072, 38973132179083943, 633]], ![![667015913262783, -682897244532589, -3398604891394252], ![79406656340749, 8496512228485687, 138]]]
    h := ![![![-1229228604, 24524370660, 6288116410], ![-134062023, -121360807914, 0]], ![![-915203817, 18259254387, 4681723284], ![-99813907, -90357379401, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R193N1 : Ideal.span {25} * I193N1 =  Ideal.span {B.equivFun.symm ![-16047687, -2033289, -1612010]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E193RS1 
