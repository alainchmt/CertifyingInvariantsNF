import IdealArithmetic.Examples.NF3_1_567567_2.PrimesBelow3_1_567567_2F2
import IdealArithmetic.Examples.NF3_1_567567_2.ClassGroupData3_1_567567_2

set_option linter.all false

noncomputable section


noncomputable def E89RS1 : RelationCertificate Table 100 ![![89, 0, 0], ![4, 1, 0]]
  ![5812617, -1846227, 360721] ![![100, 0, 0], ![12, 1, 1]] where
    su := ![![8900, 0, 0], ![400, 100, 0]]
    hsu := by decide
    w := ![![581261700, -184622700, 36072100], ![-107063300, 33463400, -5497600]]
    hw := by decide
    g := ![![![-48056483727, -1772374374, -1580263311], ![-5800304361, 13486, 0]], ![![-4033000525, -148741282, -132618997], ![-486773640, 1573, 0]]]
    h := ![![![175350553, 439488667, 351726809], ![12819010, -7825831320, 0]], ![![-32295605, -80943921, -64779984], ![-2360897, 1441340900, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {100} * I89N1 =  Ideal.span {B.equivFun.symm ![5812617, -1846227, 360721]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E89RS1 


noncomputable def E97RS1 : RelationCertificate Table 20 ![![97, 0, 0], ![44, 1, 0]]
  ![377, -147, 81] ![![20, 0, 0], ![12, 1, 1]] where
    su := ![![1940, 0, 0], ![880, 20, 0]]
    hsu := by decide
    w := ![![7540, -2940, 1620], ![-7620, 2840, -1360]]
    hw := by decide
    g := ![![![-129567332, 27661318, -1288330], ![-76421737, 34058498, 0]], ![![-60651977, 12948515, -603084], ![-35773908, 15943101, 0]]]
    h := ![![![20933, 634425, 56409], ![16038, -1367898, 0]], ![![-21169, -641029, -56996], ![-16165, 1382136, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {20} * I97N1 =  Ideal.span {B.equivFun.symm ![377, -147, 81]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E97RS1 


noncomputable def E101RS1 : RelationCertificate Table 25 ![![101, 0, 0], ![37, 1, 0]]
  ![-17, 2, 4] ![![25, 0, 0], ![-1, 1, 0]] where
    su := ![![2525, 0, 0], ![925, 25, 0]]
    hsu := by decide
    w := ![![-425, 50, 100], ![425, -125, 0]]
    hw := by decide
    g := ![![![-9982128, -15947, -19996100], ![398653, 124975620, 0]], ![![-3740777, -5977, -7493488], ![149416, 46834298, 0]]]
    h := ![![![-48967, -1132796, -119272], ![-29124, 3011619, 0]], ![![49056, 1135606, 119568], ![29285, -3019092, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {25} * I101N1 =  Ideal.span {B.equivFun.symm ![-17, 2, 4]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E101RS1 


noncomputable def E103RS0 : RelationCertificate Table 5 ![![103, 0, 0], ![15, 1, 0]]
  ![-57981309066543, -2176868353122, -1948388123494] ![![5, 0, 0], ![-1, 1, 0]] where
    su := ![![515, 0, 0], ![75, 5, 0]]
    hsu := by decide
    w := ![![-289906545332715, -10884341765610, -9741940617470], ![-143159628112595, -5374829732205, -4810697165500]]
    hw := by decide
    g := ![![![-849956, -29875, 521750], ![164017, 9476, 0]], ![![370658, -126932, 70976], ![-99517, 1357, 0]]]
    h := ![![![29474773028087568, 243493132380954801, 60889425903451910], ![6656453667983271, -1567903204110917556, 0]], ![![14555026829633969, 120240080263185071, 30067991594751724], ![3287043521433934, -774251024099715168, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N0 : Ideal.span {5} * I103N0 =  Ideal.span {B.equivFun.symm ![-57981309066543, -2176868353122, -1948388123494]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E103RS0 


noncomputable def E103RS1 : RelationCertificate Table 5 ![![103, 0, 0], ![20, 1, 0]]
  ![-431839, 131084, -13952] ![![5, 0, 0], ![-1, 1, 0]] where
    su := ![![515, 0, 0], ![100, 5, 0]]
    hsu := by decide
    w := ![![-2159195, 655420, -69760], ![-715145, -55135, 552240]]
    hw := by decide
    g := ![![![-82214098245, -6239744712, -2864683360], ![15194870708, -175032, 0]], ![![-18732893945, -1421757058, -652733448], ![3462227379, -38610, 0]]]
    h := ![![![-258018465, -2867295584, -546296048], ![-77938472, 14067119748, 0]], ![![-84974759, -944303858, -179913776], ![-25667877, 4632807344, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {5} * I103N1 =  Ideal.span {B.equivFun.symm ![-431839, 131084, -13952]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E103RS1 


noncomputable def E103RS2 : RelationCertificate Table 5 ![![103, 0, 0], ![-35, 1, 0]]
  ![4583, 172, 154] ![![5, 0, 0], ![-1, 1, 0]] where
    su := ![![515, 0, 0], ![-175, 5, 0]]
    hsu := by decide
    w := ![![22915, 860, 770], ![11315, 425, 380]]
    hw := by decide
    g := ![![![113, 12, 278], ![-16, -352, 0]], ![![-40, -4, -92], ![9, 117, 0]]]
    h := ![![![1900101, -38160544, 4490638], ![-1016056, -115633890, 0]], ![![938236, -18842954, 2217392], ![-501703, -57097825, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N2 : Ideal.span {5} * I103N2 =  Ideal.span {B.equivFun.symm ![4583, 172, 154]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E103RS2 


noncomputable def E107RS1 : RelationCertificate Table 100 ![![107, 0, 0], ![-45, 1, 0]]
  ![-59387, -46503, 134469] ![![100, 0, 0], ![12, 1, 1]] where
    su := ![![10700, 0, 0], ![-4500, 100, 0]]
    hsu := by decide
    w := ![![-5938700, -4650300, 13446900], ![-527100, 1264000, -2350400]]
    hw := by decide
    g := ![![![-9736392007, 1086857563, -282929930], ![-1160327665, 8093260644, 0]], ![![3997601169, -452238040, 116012023], ![476349923, -3356499027, 0]]]
    h := ![![![167486364, -4745721438, 431527967], ![-114790637, -11543339500, 0]], ![![17461427, -494768220, 44988888], ![-11967540, -1203458630, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {100} * I107N1 =  Ideal.span {B.equivFun.symm ![-59387, -46503, 134469]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E107RS1 


noncomputable def E131RS1 : RelationCertificate Table 5 ![![131, 0, 0], ![-20, 1, 0]]
  ![-3, -2, 6] ![![5, 0, 0], ![-1, 1, 0]] where
    su := ![![655, 0, 0], ![-100, 5, 0]]
    hsu := by decide
    w := ![![-15, -10, 30], ![605, -165, -20]]
    hw := by decide
    g := ![![![-1179, -90, -34], ![220, -9, 0]], ![![150, 11, 6], ![-26, -1, 0]]]
    h := ![![![-133, 1396, -294], ![92, 9630, 0]], ![![5821, -57067, 12016], ![-1231, -393525, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {5} * I131N1 =  Ideal.span {B.equivFun.symm ![-3, -2, 6]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E131RS1 


noncomputable def E137RS1 : RelationCertificate Table 25 ![![137, 0, 0], ![-10, 1, 0]]
  ![-61130882273, -2295116912, -2054225524] ![![25, 0, 0], ![-1, 1, 0]] where
    su := ![![3425, 0, 0], ![-250, 25, 0]]
    hsu := by decide
    w := ![![-1528272056825, -57377922800, -51355638100], ![-150936129475, -5666793125, -5072016600]]
    hw := by decide
    g := ![![![-5042363, -13648, -10153504], ![201152, 63439233, 0]], ![![207725, 1514, 424736], ![-8239, -2654003, 0]]]
    h := ![![![124132200840143, -562826377519260, 250187755942692], ![-13168966320530, -8568931154593582, 0]], ![![12259619518891, -55586199204400, 24709194515064], ![-1300601418897, -846289962861108, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {25} * I137N1 =  Ideal.span {B.equivFun.symm ![-61130882273, -2295116912, -2054225524]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E137RS1 
