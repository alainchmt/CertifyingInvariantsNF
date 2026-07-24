import IdealArithmetic.Examples.NF3_1_892863_2.PrimesBelow3_1_892863_2F1
import IdealArithmetic.Examples.NF3_1_892863_2.ClassGroupData3_1_892863_2

set_option linter.all false

noncomputable section


noncomputable def E41RS1 : RelationCertificate Table 32 ![![41, 0, 0], ![-1, 1, 0]]
  ![3272097699, 144538815, 101360479] ![![32, 0, 0], ![175, 13, 10]] where
    su := ![![1312, 0, 0], ![-32, 32, 0]]
    hsu := by decide
    w := ![![104707126368, 4625242080, 3243535328], ![898875967168, 39706169888, 27844675488]]
    hw := by decide
    g := ![![![17550987, -51281345, -11055803], ![71694157, -8646644, 0]], ![![42457, -124564, -26691], ![174019, -20987, 0]]]
    h := ![![![8234952901401, 4899452433, 16479540514679], ![-200733010938, -168915264935340, 0]], ![![70694340591623, 42060174864, 141471391990597], ![-1723226351615, -1450081550367092, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {32} * I41N1 =  Ideal.span {B.equivFun.symm ![3272097699, 144538815, 101360479]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E41RS1 


noncomputable def E43RS1 : RelationCertificate Table 4 ![![43, 0, 0], ![-19, 1, 0]]
  ![1578654135, 69734103, 48902311] ![![4, 0, 0], ![20, 1, 1]] where
    su := ![![172, 0, 0], ![-76, 4, 0]]
    hsu := by decide
    w := ![![6314616540, 278936412, 195609244], ![45085973224, 1991588804, 1396637956]]
    hw := by decide
    g := ![![![628, -4381, 1182], ![2367, -44, 0]], ![![39, 722, -1189], ![81, 17, 0]]]
    h := ![![![-2965444169, 35461750367, -7889924939], ![2135004418, 84828918672, 0]], ![![-21173088757, 253194713788, -56333578181], ![15243800041, 605673255318, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {4} * I43N1 =  Ideal.span {B.equivFun.symm ![1578654135, 69734103, 48902311]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E43RS1 


noncomputable def E47RS1 : RelationCertificate Table 2 ![![47, 0, 0], ![3, 1, 0]]
  ![-1517, -67, -47] ![![2, 0, 0], ![18, 1, 1]] where
    su := ![![94, 0, 0], ![6, 2, 0]]
    hsu := by decide
    w := ![![-3034, -134, -94], ![-40290, -1780, -1248]]
    hw := by decide
    g := ![![![-15815, 84919, 27334], ![-86085, 10472, 0]], ![![-1426, 7583, 2439], ![-7685, 935, 0]]]
    h := ![![![91018, 183132, 183339], ![9709, -2154245, 0]], ![![1208672, 2431899, 2434648], ![128937, -28607270, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {2} * I47N1 =  Ideal.span {B.equivFun.symm ![-1517, -67, -47]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E47RS1 


noncomputable def E59RS1 : RelationCertificate Table 8 ![![59, 0, 0], ![-11, 1, 0]]
  ![21, 1, 1] ![![8, 0, 0], ![20, 1, 1]] where
    su := ![![472, 0, 0], ![-88, 8, 0]]
    hsu := by decide
    w := ![![168, 8, 8], ![632, 32, 16]]
    hw := by decide
    g := ![![![3835574, -2223837, -619369], ![9233535, -1426194, 0]], ![![-700153, 405938, 113059], ![-1685483, 260337, 0]]]
    h := ![![![-5021, 26379, -10561], ![1390, 155775, 0]], ![![-18879, 99216, -39722], ![5260, 585900, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {8} * I59N1 =  Ideal.span {B.equivFun.symm ![21, 1, 1]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E59RS1 


noncomputable def E61RS1 : RelationCertificate Table 8 ![![61, 0, 0], ![-17, 1, 0]]
  ![-1265543, -55903, -39203] ![![8, 0, 0], ![-33, 1, -2]] where
    su := ![![488, 0, 0], ![-136, 8, 0]]
    hsu := by decide
    w := ![![-10124344, -447224, -313624], ![45569232, 2012936, 1411608]]
    hw := by decide
    g := ![![![-275, 136, 416], ![1143, -150, 0]], ![![109, -34, -117], ![-295, 39, 0]]]
    h := ![![![-772875127, 6910227069, -1728904663], ![328673848, 26365786310, 0]], ![![3478677341, -31102631484, 7781724691], ![-1479346659, -118671257425, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {8} * I61N1 =  Ideal.span {B.equivFun.symm ![-1265543, -55903, -39203]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E61RS1 


noncomputable def E67RS1 : RelationCertificate Table 32 ![![67, 0, 0], ![26, 1, 0]]
  ![-1201, -53, -37] ![![32, 0, 0], ![12, 1, 1]] where
    su := ![![2144, 0, 0], ![832, 32, 0]]
    hsu := by decide
    w := ![![-38432, -1696, -1184], ![-24672, -1088, -768]]
    hw := by decide
    g := ![![![-147156889, 17254570, -1621917], ![-54695281, 35532210, 0]], ![![-60510455, 7095026, -666927], ![-22490538, 14610735, 0]]]
    h := ![![![-2990999, -50368405, -7466215], ![-1912402, 125059092, 0]], ![![-1920111, -32334775, -4793052], ![-1227714, 80283615, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {32} * I67N1 =  Ideal.span {B.equivFun.symm ![-1201, -53, -37]} * (J0 ^ 5*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_0 E67RS1 


noncomputable def E71RS1 : RelationCertificate Table 16 ![![71, 0, 0], ![9, 1, 0]]
  ![-419447, 85237, 4797] ![![16, 0, 0], ![103, 1, 6]] where
    su := ![![1136, 0, 0], ![144, 16, 0]]
    hsu := by decide
    w := ![![-6711152, 1363792, 76752], ![31351248, -4226304, -2974976]]
    hw := by decide
    g := ![![![-192365527, -270244945, 201196426], ![-1179794477, 1152, 0]], ![![-37129097, -52161135, 38833414], ![-227715651, 165, 0]]]
    h := ![![![1128662, 5813490, 2326251], ![225007, -41289756, 0]], ![![-5228406, -26929497, -10778800], ![-1042017, 191277216, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {16} * I71N1 =  Ideal.span {B.equivFun.symm ![-419447, 85237, 4797]} * (J0 ^ 4*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_1 E71RS1 


noncomputable def E73RS0 : RelationCertificate Table 16 ![![73, 0, 0], ![15, 1, 0]]
  ![12213, -3207, 745] ![![16, 0, 0], ![12, 1, 1]] where
    su := ![![1168, 0, 0], ![240, 16, 0]]
    hsu := by decide
    w := ![![195408, -51312, 11920], ![-292256, 69776, -9328]]
    hw := by decide
    g := ![![![-39418513, 8377783, 669731], ![-28998407, 7173504, 0]], ![![-8976692, 1945248, 155458], ![-6601217, 1662609, 0]]]
    h := ![![![-14144877, -120591205, -30163391], ![-4558394, 550482072, 0]], ![![21142488, 180249031, 45085569], ![6813578, -822811780, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N0 : Ideal.span {16} * I73N0 =  Ideal.span {B.equivFun.symm ![12213, -3207, 745]} * (J0 ^ 4*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_0 E73RS0 


noncomputable def E73RS1 : RelationCertificate Table 2 ![![73, 0, 0], ![29, 1, 0]]
  ![1860894729, 82201555, 57645339] ![![2, 0, 0], ![18, 1, 1]] where
    su := ![![146, 0, 0], ![58, 2, 0]]
    hsu := by decide
    w := ![![3721789458, 164403110, 115290678], ![49424905606, 2183253052, 1531046004]]
    hw := by decide
    g := ![![![47207, -255020, -76067], ![259437, -32010, 0]], ![![19658, -107527, -31759], ![107427, -13095, 0]]]
    h := ![![![316068255721, 5973630114367, 796863452783], ![207391911414, -14542743601955, 0]], ![![4197347507423, 79329072173370, 10582248506834], ![2754139039616, -193125843868970, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {2} * I73N1 =  Ideal.span {B.equivFun.symm ![1860894729, 82201555, 57645339]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E73RS1 


noncomputable def E79RS1 : RelationCertificate Table 32 ![![79, 0, 0], ![36, 1, 0]]
  ![-2850579, -125919, -88303] ![![32, 0, 0], ![12, 1, 1]] where
    su := ![![2528, 0, 0], ![1152, 32, 0]]
    hsu := by decide
    w := ![![-91218528, -4029408, -2825696], ![-58607200, -2588864, -1815488]]
    hw := by decide
    g := ![![![-415382340, 48704773, -4578197], ![-154389419, 100297400, 0]], ![![-189936907, 22270644, -2093419], ![-70595780, 45861795, 0]]]
    h := ![![![-1466259921, -36655357931, -3964291657], ![-1132160920, 78294738150, 0]], ![![-942060683, -23550784461, -2547026782], ![-727404640, 50303764761, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {32} * I79N1 =  Ideal.span {B.equivFun.symm ![-2850579, -125919, -88303]} * (J0 ^ 5*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_0 E79RS1 
