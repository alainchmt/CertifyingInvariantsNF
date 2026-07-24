import IdealArithmetic.Examples.NF3_1_325983_1.PrimesBelow3_1_325983_1F2
import IdealArithmetic.Examples.NF3_1_325983_1.ClassGroupData3_1_325983_1

set_option linter.all false

noncomputable section


noncomputable def E83RS0 : RelationCertificate Table 19683 ![![83, 0, 0], ![12, 1, 0]]
  ![-2903, 840, -391] ![![19683, 0, 0], ![-543, 1, 0]] where
    su := ![![1633689, 0, 0], ![236196, 19683, 0]]
    hsu := by decide
    w := ![![-57139749, 16533720, -7696053], ![1535274, -452709, 216513]]
    hw := by decide
    g := ![![![-541761838, -386831451422082, 3568555834131], ![-19638118329, -14047976896640144, 0]], ![![-101524110, -72490774771095, 668734086329], ![-3680108759, -2632538604242752, 0]]]
    h := ![![![-2617, -224, -12], ![17859, 121, 0]], ![![66, -3, -3], ![-450, 52, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N0 : Ideal.span {19683} * I83N0 =  Ideal.span {B.equivFun.symm ![-2903, 840, -391]} * (J0 ^ 9) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_9 E83RS0 


noncomputable def E83RS1 : RelationCertificate Table 531441 ![![83, 0, 0], ![22, 1, 0]]
  ![253403, 15477, 13627] ![![531441, 0, 0], ![-118641, 1, 0]] where
    su := ![![44109603, 0, 0], ![11691702, 531441, 0]]
    hsu := by decide
    w := ![![134668743723, 8225112357, 7241946507], ![-30062554488, -1836128655, -1616643522]]
    hw := by decide
    g := ![![![499084, 1004839252279, -42348249], ![2235599, 4501119159412, 0]], ![![220361, 276477137409, -11651936], ![987086, 1238463303968, 0]]]
    h := ![![![-627249738739, -28511344354, 1764], ![2366442207670, -26557, 0]], ![![140023057712, 6364682787, -394], ![-528268811212, 5932, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {531441} * I83N1 =  Ideal.span {B.equivFun.symm ![253403, 15477, 13627]} * (J0 ^ 12) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_12 E83RS1 


noncomputable def E83RS2 : RelationCertificate Table 19683 ![![83, 0, 0], ![-35, 1, 0]]
  ![-3398, 651, -139] ![![19683, 0, 0], ![-543, 1, 0]] where
    su := ![![1633689, 0, 0], ![-688905, 19683, 0]]
    hsu := by decide
    w := ![![-66882834, 12813633, -2735937], ![1830519, -354294, 78732]]
    hw := by decide
    g := ![![![-18988, -13820928530, 127499341], ![-688285, -501913905801, 0]], ![![8251, 5836028887, -53837905], ![299086, 211938296830, 0]]]
    h := ![![![-44146, 1379, -18], ![-104592, 271, 0]], ![![1216, -21, -2], ![2881, 34, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N2 : Ideal.span {19683} * I83N2 =  Ideal.span {B.equivFun.symm ![-3398, 651, -139]} * (J0 ^ 9) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_9 E83RS2 


noncomputable def E89RS1 : RelationCertificate Table 177147 ![![89, 0, 0], ![36, 1, 0]]
  ![-72776, -4605, -4066] ![![177147, 0, 0], ![58506, 1, 0]] where
    su := ![![15766083, 0, 0], ![6377292, 177147, 0]]
    hsu := by decide
    w := ![![-12892050072, -815761935, -720279702], ![-4258259586, -269440587, -237908421]]
    hw := by decide
    g := ![![![-42164, -9650226482, -824707], ![127666, 29218874160, 0]], ![![16154790953019, -9610151671217020631, -821282211657848], ![-48914175519681, 29097535989710559920, 0]]]
    h := ![![![-289235870296, -9929033961, -256041154], ![715055343988, 4557531728, 0]], ![![-95534952670, -3279571778, -84570702], ![236183632322, 1505358227, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {177147} * I89N1 =  Ideal.span {B.equivFun.symm ![-72776, -4605, -4066]} * (J0 ^ 11) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_11 E89RS1 


noncomputable def E97RS1 : RelationCertificate Table 3 ![![97, 0, 0], ![-11, 1, 0]]
  ![11, -3, 1] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![291, 0, 0], ![-33, 3, 0]]
    hsu := by decide
    w := ![![33, -9, 3], ![105, -6, -15]]
    hw := by decide
    g := ![![![-107, -42, -204], ![-11, 119, 0]], ![![6, 4, 22], ![2, -13, 0]]]
    h := ![![![352, -28, -2], ![3103, 39, 0]], ![![1088, -99, 0], ![9591, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {3} * I97N1 =  Ideal.span {B.equivFun.symm ![11, -3, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E97RS1 


noncomputable def E103RS1 : RelationCertificate Table 729 ![![103, 0, 0], ![33, 1, 0]]
  ![-5647, -327, -293] ![![729, 0, 0], ![186, 1, 0]] where
    su := ![![75087, 0, 0], ![24057, 729, 0]]
    hsu := by decide
    w := ![![-4116663, -238383, -213597], ![-1081107, -62694, -56133]]
    hw := by decide
    g := ![![![1765, -5437914, -145399], ![-6920, 21199178, 0]], ![![566, -1782070, -47649], ![-2219, 6947226, 0]]]
    h := ![![![19648760, 595258, -26], ![-61328119, 477, 0]], ![![5160062, 156309, -9], ![-16105693, 170, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {729} * I103N1 =  Ideal.span {B.equivFun.symm ![-5647, -327, -293]} * (J0 ^ 6) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6 E103RS1 


noncomputable def E107RS1 : RelationCertificate Table 729 ![![107, 0, 0], ![-43, 1, 0]]
  ![-3821, -213, -202] ![![729, 0, 0], ![186, 1, 0]] where
    su := ![![78003, 0, 0], ![-31347, 729, 0]]
    hsu := by decide
    w := ![![-2785509, -155277, -147258], ![-731916, -40824, -38637]]
    hw := by decide
    g := ![![![310561310, -945103366117, -25270188123], ![-1217199972, 3684393428338, 0]], ![![-121621019, 370117957369, 9896219552], ![476675929, -1442868810684, 0]]]
    h := ![![![-77105118, 1793174, -6], ![-191866135, 88, 0]], ![![-20260022, 471192, -4], ![-50414450, 75, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {729} * I107N1 =  Ideal.span {B.equivFun.symm ![-3821, -213, -202]} * (J0 ^ 6) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6 E107RS1 


noncomputable def E109RS0 : RelationCertificate Table 2187 ![![109, 0, 0], ![52, 1, 0]]
  ![391, 30, -40] ![![2187, 0, 0], ![-543, 1, 0]] where
    su := ![![238383, 0, 0], ![113724, 2187, 0]]
    hsu := by decide
    w := ![![855117, 65610, -87480], ![-216513, -15309, 21870]]
    hw := by decide
    g := ![![![-2174, -23930379, 220760], ![-8757, -96560420, 0]], ![![-815, -11571698, 106750], ![-3283, -46692448, 0]]]
    h := ![![![23481375, 614756, 15395], ![-49220567, -335619, 0]], ![![-5945003, -155668, -3900], ![12461639, 85022, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N0 : Ideal.span {2187} * I109N0 =  Ideal.span {B.equivFun.symm ![391, 30, -40]} * (J0 ^ 7) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7 E109RS0 


noncomputable def E109RS1 : RelationCertificate Table 59049 ![![109, 0, 0], ![-34, 1, 0]]
  ![2354, 24, -761] ![![59049, 0, 0], ![-543, 1, 0]] where
    su := ![![6436341, 0, 0], ![-2007666, 59049, 0]]
    hsu := by decide
    w := ![![139001346, 1417176, -44936289], ![-1358127, 0, 413343]]
    hw := by decide
    g := ![![![-50671409, -325406963145214, 3001909254968], ![-5510305759, -35451947919321120, 0]], ![![54300487826465, 348711057761207586568, -3216891677686425138], ![5904953049106687, 37990847335141143594761, 0]]]
    h := ![![![5108569638, -161900506, 1764911], ![16377473182, -38475212, 0]], ![![-49916161, 1581953, -17247], ![-160025339, 375986, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {59049} * I109N1 =  Ideal.span {B.equivFun.symm ![2354, 24, -761]} * (J0 ^ 10) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_10 E109RS1 


noncomputable def E109RS2 : RelationCertificate Table 1594323 ![![109, 0, 0], ![-19, 1, 0]]
  ![62329, 8211, 2903] ![![1594323, 0, 0], ![-118641, 1, 0]] where
    su := ![![173781207, 0, 0], ![-30292137, 1594323, 0]]
    hsu := by decide
    w := ![![99372558267, 13090986153, 4628319669], ![-7394470074, -974131353, -344373768]]
    hw := by decide
    g := ![![![140182232115547, 3020014891435356087622, -127276419902079301], ![1883798660270524, 40583944721508555481676, 0]], ![![-24328896176710, -524129396729571123467, 22089067630216461], ![-326936883026448, -7043421714281919750188, 0]]]
    h := ![![![476724658806, -25090771754, 122], ![2734894091975, -2079, 0]], ![![-35473839298, 1867044209, -14], ![-203507814676, 262, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N2 : Ideal.span {1594323} * I109N2 =  Ideal.span {B.equivFun.symm ![62329, 8211, 2903]} * (J0 ^ 13) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_13 E109RS2 


noncomputable def E113RS0 : RelationCertificate Table 729 ![![113, 0, 0], ![-55, 1, 0]]
  ![1826, 114, 91] ![![729, 0, 0], ![186, 1, 0]] where
    su := ![![82377, 0, 0], ![-40095, 729, 0]]
    hsu := by decide
    w := ![![1331154, 83106, 66339], ![349191, 21870, 17496]]
    hw := by decide
    g := ![![![-33550350, 102100650273, 2729968734], ![131495728, -398029441416, 0]], ![![-777387426, 2365752786114, 63255533840], ![3046857169, -9222656833873, 0]]]
    h := ![![![38037032, -691648, 7], ![78148778, -140, 0]], ![![9977948, -181393, -2], ![20500139, 50, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N0 : Ideal.span {729} * I113N0 =  Ideal.span {B.equivFun.symm ![1826, 114, 91]} * (J0 ^ 6) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6 E113RS0 


noncomputable def E113RS1 : RelationCertificate Table 19683 ![![113, 0, 0], ![-39, 1, 0]]
  ![-3893, 462, 113] ![![19683, 0, 0], ![-543, 1, 0]] where
    su := ![![2224179, 0, 0], ![-767637, 19683, 0]]
    hsu := by decide
    w := ![![-76625919, 9093546, 2224179], ![2125764, -255879, -59049]]
    hw := by decide
    g := ![![![2817668234, 2011884022064420, -18559815749571], ![102136581679, 73062570679761182, 0]], ![![-954478377, -681521351560310, 6287097355333], ![-34598522827, -24749787449003883, 0]]]
    h := ![![![-40786, 1163, -14], ![-118075, 339, 0]], ![![1182, -23, -1], ![3422, 22, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {19683} * I113N1 =  Ideal.span {B.equivFun.symm ![-3893, 462, 113]} * (J0 ^ 9) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_9 E113RS1 


noncomputable def E127RS0 : RelationCertificate Table 9 ![![127, 0, 0], ![14, 1, 0]]
  ![214, 12, 11] ![![9, 0, 0], ![-3, 1, 0]] where
    su := ![![1143, 0, 0], ![126, 9, 0]]
    hsu := by decide
    w := ![![1926, 108, 99], ![513, 36, 27]]
    hw := by decide
    g := ![![![-2, -281, 708], ![-26, -1276, 0]], ![![-1, -32, 81], ![-3, -146, 0]]]
    h := ![![![26646, 1927, 8], ![-241702, -201, 0]], ![![7099, 504, -1], ![-64394, 26, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N0 : Ideal.span {9} * I127N0 =  Ideal.span {B.equivFun.symm ![214, 12, 11]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E127RS0 


noncomputable def E127RS1 : RelationCertificate Table 243 ![![127, 0, 0], ![-13, 1, 0]]
  ![1180, 75, 62] ![![243, 0, 0], ![-57, 1, 0]] where
    su := ![![30861, 0, 0], ![-3159, 243, 0]]
    hsu := by decide
    w := ![![286740, 18225, 15066], ![-60750, -3888, -3159]]
    hw := by decide
    g := ![![![106, 61162, -5461], ![450, 265408, 0]], ![![4, -5141, 459], ![17, -22308, 0]]]
    h := ![![![196, 230073, -95869], ![1824, 2435085, 0]], ![![-38, -48744, 20311], ![-352, -515902, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N1 : Ideal.span {243} * I127N1 =  Ideal.span {B.equivFun.symm ![1180, 75, 62]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E127RS1 


noncomputable def E127RS2 : RelationCertificate Table 6561 ![![127, 0, 0], ![-2, 1, 0]]
  ![-3050, 426, 161] ![![6561, 0, 0], ![-543, 1, 0]] where
    su := ![![833247, 0, 0], ![-13122, 6561, 0]]
    hsu := by decide
    w := ![![-20011050, 2794986, 1056321], ![1673055, -236196, -85293]]
    hw := by decide
    g := ![![![91813827287053330, 7328463024548305567175, -67605749018768852997], ![1109374808159036636, 88712263862428488902715, 0]], ![![-1686868216507988, -134643677507478159419, 1242100374668352957], ![-20382214306646242, -1629884111639812750174, 0]]]
    h := ![![![-24, -1513, 7583], ![1, -192576, 0]], ![![3, 126, -634], ![63, 16101, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N2 : Ideal.span {6561} * I127N2 =  Ideal.span {B.equivFun.symm ![-3050, 426, 161]} * (J0 ^ 8) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8 E127RS2 


noncomputable def E131RS1 : RelationCertificate Table 2187 ![![131, 0, 0], ![9, 1, 0]]
  ![5759, 330, 289] ![![2187, 0, 0], ![-543, 1, 0]] where
    su := ![![286497, 0, 0], ![19683, 2187, 0]]
    hsu := by decide
    w := ![![12594933, 721710, 632043], ![-3096792, -177147, -155277]]
    hw := by decide
    g := ![![![76713095044, 717375937744494, -6617860507573], ![308971526447, 2894652186012426, 0]], ![![5075166660, 47459985701563, -437822832547], ![20440864614, 191503706956057, 0]]]
    h := ![![![99940273, 11177326, 36429], ![-1454685556, -954382, 0]], ![![-24572922, -2748245, -8961], ![357672374, 234764, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {2187} * I131N1 =  Ideal.span {B.equivFun.symm ![5759, 330, 289]} * (J0 ^ 7) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7 E131RS1 
