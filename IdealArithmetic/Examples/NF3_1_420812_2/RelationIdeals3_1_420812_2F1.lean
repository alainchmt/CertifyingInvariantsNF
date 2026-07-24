import IdealArithmetic.Examples.NF3_1_420812_2.PrimesBelow3_1_420812_2F1
import IdealArithmetic.Examples.NF3_1_420812_2.ClassGroupData3_1_420812_2

set_option linter.all false

noncomputable section


noncomputable def E41RS1 : RelationCertificate Table 6250 ![![41, 0, 0], ![-7, 1, 0]]
  ![7373, -59, 202] ![![6250, 0, 0], ![1456, 0, 1]] where
    su := ![![256250, 0, 0], ![-43750, 6250, 0]]
    hsu := by decide
    w := ![![46081250, -368750, 1262500], ![10731250, -87500, 293750]]
    hw := by decide
    g := ![![![3164278, -125222649937989, -88312713990], ![-13388977, 551933400842608, 14862471]], ![![-436702, 17272089655909, 12181064005], ![1847828, -76128744984754, -2049996]]]
    h := ![![![1521875241, -11279396127, 3226412414], ![-534939554, -66141454386, 0]], ![![354410838, -2626720061, 751359569], ![-124575500, -15402871141, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {6250} * I41N1 =  Ideal.span {B.equivFun.symm ![7373, -59, 202]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E41RS1 


noncomputable def E43RS1 : RelationCertificate Table 125 ![![43, 0, 0], ![10, 1, 0]]
  ![-26, -17, 1] ![![125, 0, 0], ![33, 1, 0]] where
    su := ![![5375, 0, 0], ![1250, 125, 0]]
    hsu := by decide
    w := ![![-3250, -2125, 125], ![-875, -625, 0]]
    hw := by decide
    g := ![![![-15985875, -606498458, -36761881], ![-9072224, 2297617560, 0]], ![![-4248879, -161200906, -9770921], ![-2411295, 610682562, 0]]]
    h := ![![![35915, 399794, 80041], ![17651, -1720881, 0]], ![![9613, 107109, 21444], ![4768, -461046, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {125} * I43N1 =  Ideal.span {B.equivFun.symm ![-26, -17, 1]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E43RS1 


noncomputable def E47RS1 : RelationCertificate Table 625 ![![47, 0, 0], ![8, 1, 0]]
  ![1679, -32, 46] ![![625, 0, 0], ![-217, 1, 0]] where
    su := ![![29375, 0, 0], ![5000, 625, 0]]
    hsu := by decide
    w := ![![1049375, -20000, 28750], ![-364375, 6875, -10000]]
    hw := by decide
    g := ![![![1065, -274720, 2532], ![-579, -791247, 0]], ![![424, -75733, 698], ![216, -218124, 0]]]
    h := ![![![5956081, 50446028, 12622610], ![2087148, -296631312, 0]], ![![-2068073, -17515844, -4382816], ![-724665, 102996168, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {625} * I47N1 =  Ideal.span {B.equivFun.symm ![1679, -32, 46]} * (J0 ^ 4*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_0 E47RS1 


noncomputable def E53RS1 : RelationCertificate Table 25 ![![53, 0, 0], ![9, 1, 0]]
  ![219, -2, 6] ![![25, 0, 0], ![8, 1, 0]] where
    su := ![![1325, 0, 0], ![225, 25, 0]]
    hsu := by decide
    w := ![![5475, -50, 150], ![1750, -25, 50]]
    hw := by decide
    g := ![![![-53, -472, -118], ![-18, 1476, 0]], ![![-11, -96, -24], ![-3, 300, 0]]]
    h := ![![![420, 4019, 894], ![183, -23688, 0]], ![![128, 1285, 286], ![96, -7578, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {25} * I53N1 =  Ideal.span {B.equivFun.symm ![219, -2, 6]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E53RS1 


noncomputable def E59RS0 : RelationCertificate Table 3125 ![![59, 0, 0], ![-29, 1, 0]]
  ![1022, -101, 28] ![![3125, 0, 0], ![-217, 1, 0]] where
    su := ![![184375, 0, 0], ![-90625, 3125, 0]]
    hsu := by decide
    w := ![![3193750, -315625, 87500], ![-221875, 21875, -6250]]
    hw := by decide
    g := ![![![69509, -15214518, 140226], ![-8699, -219103122, 0]], ![![-33313, 7319625, -67462], ![6020, 105409374, 0]]]
    h := ![![![-4094616, 194280667, -13404868], ![5305526, 395443620, 0]], ![![284431, -13495487, 931154], ![-368536, -27469044, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N0 : Ideal.span {3125} * I59N0 =  Ideal.span {B.equivFun.symm ![1022, -101, 28]} * (J0 ^ 5*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_0 E59RS0 


noncomputable def E59RS1 : RelationCertificate Table 1250 ![![59, 0, 0], ![-17, 1, 0]]
  ![3577, -41, 98] ![![1250, 0, 0], ![206, 0, 1]] where
    su := ![![73750, 0, 0], ![-21250, 1250, 0]]
    hsu := by decide
    w := ![![4471250, -51250, 122500], ![735000, -8750, 20000]]
    hw := by decide
    g := ![![![3452921, -4422219755950, -26323394716], ![-20489645, 32903421370368, 5014966]], ![![-812556, 1040522304309, 6193739985], ![4821724, -7741981564322, -1179992]]]
    h := ![![![196895232, -3951038016, 465074662], ![-123699257, -13719702480, 0]], ![![32366620, -649491229, 76451280], ![-20334280, -2255312752, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {1250} * I59N1 =  Ideal.span {B.equivFun.symm ![3577, -41, 98]} * (J0 ^ 4*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_1 E59RS1 


noncomputable def E59RS2 : RelationCertificate Table 250 ![![59, 0, 0], ![-14, 1, 0]]
  ![902, -16, 23] ![![250, 0, 0], ![33, 1, 0]] where
    su := ![![14750, 0, 0], ![-3500, 250, 0]]
    hsu := by decide
    w := ![![225500, -4000, 5750], ![29750, -500, 750]]
    hw := by decide
    g := ![![![-3385421, -115676608, -7010924], ![-909401, 876365498, 0]], ![![806677, 27564016, 1670599], ![216837, -208824874, 0]]]
    h := ![![![-7730, 121393, -17351], ![3921, 511866, 0]], ![![-1012, 16014, -2289], ![550, 67527, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N2 : Ideal.span {250} * I59N2 =  Ideal.span {B.equivFun.symm ![902, -16, 23]} * (J0 ^ 3*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_2 E59RS2 


noncomputable def E61RS0 : RelationCertificate Table 250 ![![61, 0, 0], ![16, 1, 0]]
  ![-31, 23, 6] ![![250, 0, 0], ![-44, 0, 1]] where
    su := ![![15250, 0, 0], ![4000, 250, 0]]
    hsu := by decide
    w := ![![-7750, 5750, 1500], ![1250, -2000, -500]]
    hw := by decide
    g := ![![![391838, -53008297802, 646211889], ![2516103, -161610508560, -670978]], ![![106888, -14456808363, 176239604], ![686341, -44075592852, -182994]]]
    h := ![![![288480, 5294904, 662196], ![162479, -20196975, 0]], ![![-47469, -871162, -108950], ![-26710, 3322974, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N0 : Ideal.span {250} * I61N0 =  Ideal.span {B.equivFun.symm ![-31, 23, 6]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E61RS0 


noncomputable def E61RS1 : RelationCertificate Table 250 ![![61, 0, 0], ![-14, 1, 0]]
  ![-167, 11, -8] ![![250, 0, 0], ![-44, 0, 1]] where
    su := ![![15250, 0, 0], ![-3500, 250, 0]]
    hsu := by decide
    w := ![![-41750, 2750, -2000], ![7500, -750, 500]]
    hw := by decide
    g := ![![![-416443, 47306559434, -577000643], ![-2234451, 144227386016, -304990]], ![![83306, -9461310230, 115400108], ![446989, -28845472152, 60998]]]
    h := ![![![490635, -7628597, 1090356], ![-237640, -33255862, 0]], ![![-88361, 1373986, -196384], ![42833, 5989713, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {250} * I61N1 =  Ideal.span {B.equivFun.symm ![-167, 11, -8]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E61RS1 


noncomputable def E61RS2 : RelationCertificate Table 2 ![![61, 0, 0], ![-3, 1, 0]]
  ![-3, 1, 0] ![![2, 0, 0], ![26, 0, 1]] where
    su := ![![122, 0, 0], ![-6, 2, 0]]
    hsu := by decide
    w := ![![-6, 2, 0], ![-78, -12, -2]]
    hw := by decide
    g := ![![![569, -34628, -20516], ![-2709, 0, -3645]], ![![-25, 0, -1], ![2, 0, 0]]]
    h := ![![![8, -24, 16], ![1, -488, 0]], ![![102, -305, 203], ![23, -6192, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N2 : Ideal.span {2} * I61N2 =  Ideal.span {B.equivFun.symm ![-3, 1, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E61RS2 


noncomputable def E71RS0 : RelationCertificate Table 50 ![![71, 0, 0], ![27, 1, 0]]
  ![23, -9, 2] ![![50, 0, 0], ![6, 0, 1]] where
    su := ![![3550, 0, 0], ![1350, 50, 0]]
    hsu := by decide
    w := ![![1150, -450, 100], ![100, 250, -50]]
    hw := by decide
    g := ![![![5618640059, 76026203342073, -2374882677648], ![-46823416715, 118790942987536, -447237]], ![![2140434229, 28962362166420, -904717178936], ![-17837491422, 45253690986192, -170376]]]
    h := ![![![-433, -14981, -1110], ![-320, 39406, 0]], ![![-39, -1228, -91], ![-17, 3230, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N0 : Ideal.span {50} * I71N0 =  Ideal.span {B.equivFun.symm ![23, -9, 2]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E71RS0 


noncomputable def E71RS1 : RelationCertificate Table 125 ![![71, 0, 0], ![-16, 1, 0]]
  ![-292, 11, -8] ![![125, 0, 0], ![33, 1, 0]] where
    su := ![![8875, 0, 0], ![-2000, 125, 0]]
    hsu := by decide
    w := ![![-36500, 1375, -1000], ![-9625, 375, -250]]
    hw := by decide
    g := ![![![63775764, 2419631865, 146661904], ![36193893, -9166369001, 0]], ![![-13506920, -512447751, -31061156], ![-7665371, 1941322250, 0]]]
    h := ![![![1023052, -18113033, 2264984], ![-485622, -80406936, 0]], ![![269797, -4776581, 597298], ![-128026, -21204080, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {125} * I71N1 =  Ideal.span {B.equivFun.symm ![-292, 11, -8]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E71RS1 


noncomputable def E71RS2 : RelationCertificate Table 10 ![![71, 0, 0], ![-12, 1, 0]]
  ![117, -1, 3] ![![10, 0, 0], ![3, 1, 0]] where
    su := ![![710, 0, 0], ![-120, 10, 0]]
    hsu := by decide
    w := ![![1170, -10, 30], ![350, 0, 10]]
    hw := by decide
    g := ![![![-24, -85, -57], ![-13, 284, 0]], ![![4, 15, 10], ![3, -50, 0]]]
    h := ![![![70627, -896948, 149549], ![-24549, -5308988, 0]], ![![21131, -268283, 44731], ![-7307, -1587950, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N2 : Ideal.span {10} * I71N2 =  Ideal.span {B.equivFun.symm ![117, -1, 3]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E71RS2 


noncomputable def E73RS1 : RelationCertificate Table 250 ![![73, 0, 0], ![30, 1, 0]]
  ![99, -17, 1] ![![250, 0, 0], ![33, 1, 0]] where
    su := ![![18250, 0, 0], ![7500, 250, 0]]
    hsu := by decide
    w := ![![24750, -4250, 250], ![3250, -500, 0]]
    hw := by decide
    g := ![![![506, 18066, 1095], ![320, -136873, 0]], ![![221, 7705, 467], ![97, -58374, 0]]]
    h := ![![![-987829, -41662127, -2778367], ![-976626, 101410396, 0]], ![![-129679, -5469044, -364720], ![-128190, 13312280, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {250} * I73N1 =  Ideal.span {B.equivFun.symm ![99, -17, 1]} * (J0 ^ 3*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_2 E73RS1 


noncomputable def E79RS0 : RelationCertificate Table 6250 ![![79, 0, 0], ![18, 1, 0]]
  ![518, -94, 57] ![![6250, 0, 0], ![-217, 1, 0]] where
    su := ![![493750, 0, 0], ![112500, 6250, 0]]
    hsu := by decide
    w := ![![3237500, -587500, 356250], ![-112500, 18750, -12500]]
    hw := by decide
    g := ![![![44498944181, -9679579301781, 89212717021], ![-3093730693, -278789740690608, 0]], ![![10696700550, -2326786919784, 21445041832], ![-743674137, -67015755724996, 0]]]
    h := ![![![-2620, -52345, -5817], ![-1239, 229800, 0]], ![![78, 1817, 202], ![100, -7980, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N0 : Ideal.span {6250} * I79N0 =  Ideal.span {B.equivFun.symm ![518, -94, 57]} * (J0 ^ 5*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_2 E79RS0 


noncomputable def E79RS1 : RelationCertificate Table 625 ![![79, 0, 0], ![27, 1, 0]]
  ![89, -62, 11] ![![625, 0, 0], ![-217, 1, 0]] where
    su := ![![49375, 0, 0], ![16875, 625, 0]]
    hsu := by decide
    w := ![![55625, -38750, 6875], ![-19375, 13125, -2500]]
    hw := by decide
    g := ![![![7098, -1942681, 17905], ![-5344, -5595304, 0]], ![![2585, -700255, 6454], ![-1850, -2016872, 0]]]
    h := ![![![-631, -21556, -1597], ![-487, 63087, 0]], ![![198, 7504, 556], ![233, -21964, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {625} * I79N1 =  Ideal.span {B.equivFun.symm ![89, -62, 11]} * (J0 ^ 4*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_0 E79RS1 


noncomputable def E79RS2 : RelationCertificate Table 250 ![![79, 0, 0], ![33, 1, 0]]
  ![1387, -21, 38] ![![250, 0, 0], ![-44, 0, 1]] where
    su := ![![19750, 0, 0], ![8250, 250, 0]]
    hsu := by decide
    w := ![![346750, -5250, 9500], ![-61750, 1000, -1750]]
    hw := by decide
    g := ![![![605104, -115804290376, 1410627249], ![5536026, -353060735181, -4858377]], ![![255844, -48957911478, 596362740], ![2340591, -149261449323, -2053948]]]
    h := ![![![2926270, 137344350, 8326172], ![2960904, -328883775, 0]], ![![-521165, -24460728, -1482873], ![-527324, 58573480, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N2 : Ideal.span {250} * I79N2 =  Ideal.span {B.equivFun.symm ![1387, -21, 38]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E79RS2 
