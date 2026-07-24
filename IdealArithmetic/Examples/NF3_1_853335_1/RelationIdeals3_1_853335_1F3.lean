import IdealArithmetic.Examples.NF3_1_853335_1.PrimesBelow3_1_853335_1F3
import IdealArithmetic.Examples.NF3_1_853335_1.ClassGroupData3_1_853335_1

set_option linter.all false

noncomputable section


noncomputable def E139RS0 : RelationCertificate Table 400 ![![139, 0, 0], ![11, 1, 0]]
  ![-10908, -816, -853] ![![400, 0, 0], ![143, 0, 1]] where
    su := ![![55600, 0, 0], ![4400, 400, 0]]
    hsu := by decide
    w := ![![-4363200, -326400, -341200], ![-1785200, -133600, -139600]]
    hw := by decide
    g := ![![![-22443666069, -20671847146, -401812894], ![-8024614897, 56249924206, 0]], ![![-1695385589, -1561543020, -30352785], ![-606175957, 4249096653, 0]]]
    h := ![![![-212873, -285583, -428575], ![-18827, 4964256, 0]], ![![-87097, -116846, -175351], ![-7700, 2031120, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N0 : Ideal.span {400} * I139N0 =  Ideal.span {B.equivFun.symm ![-10908, -816, -853]} * (J0 ^ 4*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_2 E139RS0 


noncomputable def E139RS1 : RelationCertificate Table 50 ![![139, 0, 0], ![35, 1, 0]]
  ![-177242, -13284, -13847] ![![50, 0, 0], ![-7, 0, 1]] where
    su := ![![6950, 0, 0], ![1750, 50, 0]]
    hsu := by decide
    w := ![![-8862100, -664200, -692350], ![-2424350, -181700, -189400]]
    hw := by decide
    g := ![![![-22403678838876538, 380692497611966, -443245500160764], ![3127650127439503, 6344874960199502, 0]], ![![-5560625323918528, 94488425676480, -110014170915088], ![776287261930327, 1574807094608001, 0]]]
    h := ![![![-192913231, -1104359687, -414287429], ![-56520215, 4798828232, 0]], ![![-52774116, -302112899, -113334068], ![-15461777, 1312785972, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N1 : Ideal.span {50} * I139N1 =  Ideal.span {B.equivFun.symm ![-177242, -13284, -13847]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E139RS1 


noncomputable def E139RS2 : RelationCertificate Table 50 ![![139, 0, 0], ![-46, 1, 0]]
  ![198, -4, -7] ![![50, 0, 0], ![-7, 0, 1]] where
    su := ![![6950, 0, 0], ![-2300, 50, 0]]
    hsu := by decide
    w := ![![9900, -200, -350], ![-2750, -100, 200]]
    hw := by decide
    g := ![![![102533, -1743, 2028], ![-14311, -29040, 0]], ![![-51402821, 873458, -1016979], ![7176064, 14557631, 0]]]
    h := ![![![-157260, 1452845, -355909], ![62529, 4122612, 0]], ![![42883, -396010, 97012], ![-16990, -1123722, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N2 : Ideal.span {50} * I139N2 =  Ideal.span {B.equivFun.symm ![198, -4, -7]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E139RS2 


noncomputable def E149RS1 : RelationCertificate Table 5 ![![149, 0, 0], ![39, 1, 0]]
  ![-131407, -2384, 8028] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![745, 0, 0], ![195, 5, 0]]
    hsu := by decide
    w := ![![-657035, -11920, 40140], ![1693550, -87375, -20580]]
    hw := by decide
    g := ![![![334941125, 53463680, 30003204], ![-123283712, 7152, 0]], ![![120291993, 19200392, 10777128], ![-44276715, 1848, 0]]]
    h := ![![![-382682276, -2478736763, -826506828], ![-116800897, 10262460450, 0]], ![![987031109, 6393268046, 2131763316], ![301258271, -26469394850, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R149N1 : Ideal.span {5} * I149N1 =  Ideal.span {B.equivFun.symm ![-131407, -2384, 8028]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E149RS1 


noncomputable def E151RS1 : RelationCertificate Table 25 ![![151, 0, 0], ![73, 1, 0]]
  ![534557, 40064, 41762] ![![25, 0, 0], ![8, 1, 0]] where
    su := ![![3775, 0, 0], ![1825, 25, 0]]
    hsu := by decide
    w := ![![13363925, 1001600, 1044050], ![12034000, 901925, 940150]]
    hw := by decide
    g := ![![![1571, 1190, 2806], ![554, -5920, 0]], ![![721, 577, 1360], ![262, -2866, 0]]]
    h := ![![![62573818, 935302615, 160379198], ![36445159, -2018101428, 0]], ![![56346728, 842224995, 144418894], ![32818262, -1817267949, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N1 : Ideal.span {25} * I151N1 =  Ideal.span {B.equivFun.symm ![534557, 40064, 41762]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E151RS1 


noncomputable def E157RS0 : RelationCertificate Table 4 ![![157, 0, 0], ![10, 1, 0]]
  ![-30000, 1000, 749] ![![4, 0, 0], ![-1, 0, 1]] where
    su := ![![628, 0, 0], ![40, 4, 0]]
    hsu := by decide
    w := ![![-120000, 4000, 2996], ![278908, 14984, -24004]]
    hw := by decide
    g := ![![![-28072046, -2205221, -3814622], ![6064359, 4710, 0]], ![![-4363673, -343959, -594125], ![942390, 285, 0]]]
    h := ![![![-73341070, -85918907, -147346543], ![-5218601, 1927784000, 0]], ![![170326879, 199537628, 342196763], ![12119862, -4477074816, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R157N0 : Ideal.span {4} * I157N0 =  Ideal.span {B.equivFun.symm ![-30000, 1000, 749]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E157RS0 


noncomputable def E157RS1 : RelationCertificate Table 4 ![![157, 0, 0], ![45, 1, 0]]
  ![0, 0, 1] ![![4, 0, 0], ![-1, 0, 1]] where
    su := ![![628, 0, 0], ![180, 4, 0]]
    hsu := by decide
    w := ![![0, 0, 4], ![92, 16, 4]]
    hw := by decide
    g := ![![![0, -2903190, -432233], ![-247701, -411804, 803011]], ![![0, -832015, -123891], ![-70913, -118017, 230132]]]
    h := ![![![-45, -165, -47], ![75, 615, 0]], ![![-46, -165, -47], ![79, 615, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R157N1 : Ideal.span {4} * I157N1 =  Ideal.span {B.equivFun.symm ![0, 0, 1]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E157RS1 


noncomputable def E157RS2 : RelationCertificate Table 4 ![![157, 0, 0], ![-55, 1, 0]]
  ![3088, 256, -329] ![![4, 0, 0], ![-1, 0, 1]] where
    su := ![![628, 0, 0], ![-220, 4, 0]]
    hsu := by decide
    w := ![![12352, 1024, -1316], ![12724, -4496, 2540]]
    hw := by decide
    g := ![![![-655861, -51809, -89409], ![141617, 0, 0]], ![![169775, 13372, 23105], ![-36667, -15, 0]]]
    h := ![![![535134, -5933922, 1228003], ![-225190, -16066400, 0]], ![![553032, -6132117, 1269023], ![-232639, -16602998, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R157N2 : Ideal.span {4} * I157N2 =  Ideal.span {B.equivFun.symm ![3088, 256, -329]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E157RS2 


noncomputable def E167RS1 : RelationCertificate Table 400 ![![167, 0, 0], ![68, 1, 0]]
  ![235404, 33808, -35111] ![![400, 0, 0], ![143, 0, 1]] where
    su := ![![66800, 0, 0], ![27200, 400, 0]]
    hsu := by decide
    w := ![![94161600, 13523200, -14044400], ![36518000, 4408000, -4859600]]
    hw := by decide
    g := ![![![-3969671403619555509102, -3656285052711839605926, -71069724297479848459], ![-1419335201104734794059, 9949074973365549786124, 0]], ![![-1615936021625418066964, -1488365691079727566904, -28930386387792645423], ![-577769453697056440508, 4049974669604700782295, 0]]]
    h := ![![![65924043876, 854980045540, 157877804159], ![31962964308, -2197132777472, 0]], ![![25571024513, 331634930626, 61238615933], ![12397991678, -852237406080, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R167N1 : Ideal.span {400} * I167N1 =  Ideal.span {B.equivFun.symm ![235404, 33808, -35111]} * (J0 ^ 4*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_2 E167RS1 


noncomputable def E173RS1 : RelationCertificate Table 2 ![![173, 0, 0], ![12, 1, 0]]
  ![5466, -76, -211] ![![2, 0, 0], ![-3, 0, 1]] where
    su := ![![346, 0, 0], ![24, 2, 0]]
    hsu := by decide
    w := ![![10932, -152, -422], ![-49490, -3452, 4816]]
    hw := by decide
    g := ![![![1364861, 273597, 1047068], ![-1523751, 0, 0]], ![![209067, 41927, 160400], ![-233398, 3, 0]]]
    h := ![![![971382, 1464492, 1953241], ![75986, -28159242, 0]], ![![-4393931, -6624393, -8835140], ![-342958, 127373469, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R173N1 : Ideal.span {2} * I173N1 =  Ideal.span {B.equivFun.symm ![5466, -76, -211]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E173RS1 


noncomputable def E179RS1 : RelationCertificate Table 10 ![![179, 0, 0], ![-64, 1, 0]]
  ![-7698, 264, 187] ![![10, 0, 0], ![-7, 0, 1]] where
    su := ![![1790, 0, 0], ![-640, 10, 0]]
    hsu := by decide
    w := ![![-76980, 2640, 1870], ![118610, 2200, -7280]]
    hw := by decide
    g := ![![![-212021, -23302, -38807], ![144537, 104, 0]], ![![9439592, -225492, 890532], ![-6518648, -773143, 0]]]
    h := ![![![-65303690, 841048055, -150663535], ![28047401, 2247397746, 0]], ![![100587105, -1295463344, 232066508], ![-43201139, -3461658805, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R179N1 : Ideal.span {10} * I179N1 =  Ideal.span {B.equivFun.symm ![-7698, 264, 187]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E179RS1 


noncomputable def E191RS1 : RelationCertificate Table 2 ![![191, 0, 0], ![-13, 1, 0]]
  ![167103270, 12524068, 13054859] ![![2, 0, 0], ![-3, 0, 1]] where
    su := ![![382, 0, 0], ![-26, 2, 0]]
    hsu := by decide
    w := ![![334206540, 25048136, 26109718], ![2954069458, 221401812, 230785192]]
    hw := by decide
    g := ![![![43025, 863, 20514], ![-54275, 0, 0]], ![![-5059, 442, -2713], ![6237, -3, 0]]]
    h := ![![![67413672400, -180742963394, 135579073045], ![-5534663326, -2157965824728, 0]], ![![595873051076, -1597596707443, 1198390668316], ![-48921185161, -19074375187980, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R191N1 : Ideal.span {2} * I191N1 =  Ideal.span {B.equivFun.symm ![167103270, 12524068, 13054859]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E191RS1 


noncomputable def E193RS1 : RelationCertificate Table 32 ![![193, 0, 0], ![29, 1, 0]]
  ![2867692, 214928, 224037] ![![32, 0, 0], ![-17, 0, 1]] where
    su := ![![6176, 0, 0], ![928, 32, 0]]
    hsu := by decide
    w := ![![91766144, 6877696, 7169184], ![10547680, 790528, 824032]]
    hw := by decide
    g := ![![![84131993, -7787333, 3190741], ![-44595389, -19168752, 0]], ![![1078289778407908, -99806264906536, 40893574995956], ![-571563520560553, -245676959769917, 0]]]
    h := ![![![-10624725715, -47229832571, -21802786587], ![-1841175413, 350661502944, 0]], ![![-1221215171, -5428637834, -2506031161], ![-211626286, 40305336652, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R193N1 : Ideal.span {32} * I193N1 =  Ideal.span {B.equivFun.symm ![2867692, 214928, 224037]} * (J0 ^ 5*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_0 E193RS1 
