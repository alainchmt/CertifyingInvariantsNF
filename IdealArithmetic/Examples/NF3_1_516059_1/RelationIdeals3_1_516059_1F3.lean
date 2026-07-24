import IdealArithmetic.Examples.NF3_1_516059_1.PrimesBelow3_1_516059_1F3
import IdealArithmetic.Examples.NF3_1_516059_1.ClassGroupData3_1_516059_1

set_option linter.all false

noncomputable section


noncomputable def E139RS1 : RelationCertificate Table 4096 ![![139, 0, 0], ![-55, 1, 0]]
  ![-722, 36, 47] ![![4096, 0, 0], ![-967, 1, 0]] where
    su := ![![569344, 0, 0], ![-225280, 4096, 0]]
    hsu := by decide
    w := ![![-2957312, 147456, 192512], ![700416, -36864, -45056]]
    hw := by decide
    g := ![![![353071740811123722, 118317660027790288622, -853838687741057920], ![-54468435873183684, 499617609283910462899, 0]], ![![-142244732045233000, -47667547134210790418, 343992569523010467], ![21944118348032507, -201284794966607267546, 0]]]
    h := ![![![388859904, 8242085422, -994652335], ![-94569694, 19750953516, 0]], ![![-92103678, -1952185401, 235589134], ![22399452, -4678127091, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N1 : Ideal.span {4096} * I139N1 =  Ideal.span {B.equivFun.symm ![-722, 36, 47]} * (J0 ^ 12) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_12 E139RS1 


noncomputable def E149RS1 : RelationCertificate Table 32 ![![149, 0, 0], ![54, 1, 0]]
  ![50, -4, 1] ![![32, 0, 0], ![-7, 1, 0]] where
    su := ![![4768, 0, 0], ![1728, 32, 0]]
    hsu := by decide
    w := ![![1600, -128, 32], ![-288, 64, -32]]
    hw := by decide
    g := ![![![2486, 8483, -5932], ![-271, 27118, 0]], ![![902, 3070, -2147], ![-88, 9815, 0]]]
    h := ![![![2578, -48477, -6653], ![755, 141614, 0]], ![![-510, 8743, 1200], ![-12, -25543, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R149N1 : Ideal.span {32} * I149N1 =  Ideal.span {B.equivFun.symm ![50, -4, 1]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E149RS1 


noncomputable def E157RS0 : RelationCertificate Table 1024 ![![157, 0, 0], ![-59, 1, 0]]
  ![350, -60, 7] ![![1024, 0, 0], ![57, 1, 0]] where
    su := ![![160768, 0, 0], ![-60416, 1024, 0]]
    hsu := by decide
    w := ![![358400, -61440, 7168], ![20480, -3072, 0]]
    hw := by decide
    g := ![![![-917395677, 16548129697, 2145123505], ![-34905239, -313800924157, 0]], ![![344753745, -6218723334, -806129142], ![13117490, 117925177343, 0]]]
    h := ![![![38541, 866011, -97769], ![-8947, 2192820, 0]], ![![2216, 49479, -5586], ![-474, 125286, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R157N0 : Ideal.span {1024} * I157N0 =  Ideal.span {B.equivFun.symm ![350, -60, 7]} * (J0 ^ 10) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_10 E157RS0 


noncomputable def E157RS1 : RelationCertificate Table 64 ![![157, 0, 0], ![-49, 1, 0]]
  ![-258, 4, -9] ![![64, 0, 0], ![-7, 1, 0]] where
    su := ![![10048, 0, 0], ![-3136, 64, 0]]
    hsu := by decide
    w := ![![-16512, 256, -576], ![1344, -64, 64]]
    hw := by decide
    g := ![![![-4697090, -15758698, 11028162], ![267570, -100828909, 0]], ![![1495867, 5018614, -3512098], ![-85193, 32110610, 0]]]
    h := ![![![-744898, -13698848, 1843951], ![145364, -41357188, 0]], ![![60773, 1117258, -150390], ![-11791, 3373033, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R157N1 : Ideal.span {64} * I157N1 =  Ideal.span {B.equivFun.symm ![-258, 4, -9]} * (J0 ^ 6) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6 E157RS1 


noncomputable def E163RS1 : RelationCertificate Table 64 ![![163, 0, 0], ![-43, 1, 0]]
  ![34, -4, -7] ![![64, 0, 0], ![-7, 1, 0]] where
    su := ![![10432, 0, 0], ![-2752, 64, 0]]
    hsu := by decide
    w := ![![2176, -256, -448], ![-576, 256, 0]]
    hw := by decide
    g := ![![![94, 260, -182], ![37, 1668, 0]], ![![3213, 10772, -7539], ![-137, 68927, 0]]]
    h := ![![![448090, 7170704, -1091125], ![-74052, 25407624, 0]], ![![-119097, -1906730, 290136], ![19890, -6756024, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R163N1 : Ideal.span {64} * I163N1 =  Ideal.span {B.equivFun.symm ![34, -4, -7]} * (J0 ^ 6) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6 E163RS1 


noncomputable def E167RS1 : RelationCertificate Table 262144 ![![167, 0, 0], ![9, 1, 0]]
  ![72654, -1308, 3071] ![![262144, 0, 0], ![-86983, 1, 0]] where
    su := ![![43778048, 0, 0], ![2359296, 262144, 0]]
    hsu := by decide
    w := ![![19045810176, -342884352, 805044224], ![-6319505408, 113770496, -267124736]]
    hw := by decide
    g := ![![![38540945331255607818, 1196627680154344512536232, -96295883945241953389], ![-8223645658852599271, 3606198314420215232743722, 0]], ![![1961665284042079390, 60906211767951749818394, -4901288510386559376], ![-418568876776964047, 183549053609539174437451, 0]]]
    h := ![![![5926359, -11880111, -13858367], ![248349, 330621480, 0]], ![![-1966405, 3941886, 4598283], ![-82288, -109702040, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R167N1 : Ideal.span {262144} * I167N1 =  Ideal.span {B.equivFun.symm ![72654, -1308, 3071]} * (J0 ^ 18) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_18 E167RS1 


noncomputable def E173RS0 : RelationCertificate Table 262144 ![![173, 0, 0], ![13, 1, 0]]
  ![-11438, -292, -1519] ![![262144, 0, 0], ![-86983, 1, 0]] where
    su := ![![45350912, 0, 0], ![3407872, 262144, 0]]
    hsu := by decide
    w := ![![-2998403072, -76546048, -398196736], ![994836480, 25427968, 132120576]]
    hw := by decide
    g := ![![![-88328489688710059, -2742442220847038389396, 220691784257535682], ![18847026053566844, -8264718156058204831769, 0]], ![![-6126831654621790, -190227206069889944858, 15308100642107014], ![1307308165781625, -573275247817785868290, 0]]]
    h := ![![![31508, -105730, -74011], ![1878, 1828912, 0]], ![![-10467, 35079, 24556], ![-450, -606812, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R173N0 : Ideal.span {262144} * I173N0 =  Ideal.span {B.equivFun.symm ![-11438, -292, -1519]} * (J0 ^ 18) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_18 E173RS0 


noncomputable def E173RS1 : RelationCertificate Table 4 ![![173, 0, 0], ![80, 1, 0]]
  ![34, 0, 1] ![![4, 0, 0], ![1, 1, 0]] where
    su := ![![692, 0, 0], ![320, 4, 0]]
    hsu := by decide
    w := ![![136, 0, 4], ![84, 8, 4]]
    hw := by decide
    g := ![![![-230, -150, 605], ![-93, -346, 0]], ![![-106, -69, 278], ![-42, -159, 0]]]
    h := ![![![30858, -900766, -81883], ![9158, 2023680, 0]], ![![19017, -555786, -50523], ![5700, 1248640, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R173N1 : Ideal.span {4} * I173N1 =  Ideal.span {B.equivFun.symm ![34, 0, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E173RS1 


noncomputable def E179RS0 : RelationCertificate Table 2048 ![![179, 0, 0], ![80, 1, 0]]
  ![-4430, 28, -191] ![![2048, 0, 0], ![-967, 1, 0]] where
    su := ![![366592, 0, 0], ![163840, 2048, 0]]
    hsu := by decide
    w := ![![-9072640, 57344, -391168], ![4274176, -26624, 184320]]
    hw := by decide
    g := ![![![-686027682813687021, -252449108722835974966, 1821796984773507276], ![200654131131838022, -533005746402306128755, 0]], ![![-302771994055866438, -111416087077054082340, 804033306035905891], ![88556851159654977, -235237172965933609255, 0]]]
    h := ![![![-241518, 6987409, 635183], ![-68755, -16242564, 0]], ![![113745, -3291805, -299238], ![32470, 7651956, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R179N0 : Ideal.span {2048} * I179N0 =  Ideal.span {B.equivFun.symm ![-4430, 28, -191]} * (J0 ^ 11) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_11 E179RS0 


noncomputable def E179RS1 : RelationCertificate Table 4 ![![179, 0, 0], ![-46, 1, 0]]
  ![10, 0, 1] ![![4, 0, 0], ![1, 1, 0]] where
    su := ![![716, 0, 0], ![-184, 4, 0]]
    hsu := by decide
    w := ![![40, 0, 4], ![60, -16, 4]]
    hw := by decide
    g := ![![![13, -1, 1], ![3, 0, 0]], ![![-3, 0, -2], ![2, 1, 0]]]
    h := ![![![-46, -1534, 219], ![186, -5600, 0]], ![![-95, -2318, 331], ![182, -8464, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R179N1 : Ideal.span {4} * I179N1 =  Ideal.span {B.equivFun.symm ![10, 0, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E179RS1 


noncomputable def E179RS2 : RelationCertificate Table 512 ![![179, 0, 0], ![-34, 1, 0]]
  ![326, -12, 27] ![![512, 0, 0], ![57, 1, 0]] where
    su := ![![91648, 0, 0], ![-17408, 512, 0]]
    hsu := by decide
    w := ![![166912, -6144, 13824], ![19968, -1024, 1536]]
    hw := by decide
    g := ![![![-785747846369771, 14263047201538791, 1848898431787915], ![-59618320393425, -135233713867916066, 0]], ![![151443021049006, -2749023070881949, -356351933277910], ![11490681892812, 26064598548327131, 0]]]
    h := ![![![26216, 330327, -62491], ![-2989, 1597988, 0]], ![![3149, 39523, -7477], ![-293, 191198, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R179N2 : Ideal.span {512} * I179N2 =  Ideal.span {B.equivFun.symm ![326, -12, 27]} * (J0 ^ 9) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_9 E179RS2 


noncomputable def E181RS1 : RelationCertificate Table 2 ![![181, 0, 0], ![62, 1, 0]]
  ![20, 0, 1] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![362, 0, 0], ![124, 2, 0]]
    hsu := by decide
    w := ![![40, 0, 2], ![70, -6, 4]]
    hw := by decide
    g := ![![![-582, -319, 1902], ![-450, -543, 0]], ![![-196, -108, 641], ![-151, -183, 0]]]
    h := ![![![7492, -158964, -18859], ![1724, 487640, 0]], ![![13105, -278514, -33042], ![3083, 854372, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R181N1 : Ideal.span {2} * I181N1 =  Ideal.span {B.equivFun.symm ![20, 0, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E181RS1 


noncomputable def E191RS0 : RelationCertificate Table 4 ![![191, 0, 0], ![18, 1, 0]]
  ![74, 0, 3] ![![4, 0, 0], ![1, 1, 0]] where
    su := ![![764, 0, 0], ![72, 4, 0]]
    hsu := by decide
    w := ![![296, 0, 12], ![224, -4, 12]]
    hw := by decide
    g := ![![![-18160031, -11489005, 46697237], ![-7412259, -26684135, 0]], ![![-1714779, -1084861, 4409433], ![-699909, -2519676, 0]]]
    h := ![![![10342, -52134, -24327], ![894, 663780, 0]], ![![7825, -39458, -18412], ![702, 502385, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R191N0 : Ideal.span {4} * I191N0 =  Ideal.span {B.equivFun.symm ![74, 0, 3]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E191RS0 


noncomputable def E191RS1 : RelationCertificate Table 4096 ![![191, 0, 0], ![57, 1, 0]]
  ![5982, -60, 263] ![![4096, 0, 0], ![-967, 1, 0]] where
    su := ![![782336, 0, 0], ![233472, 4096, 0]]
    hsu := by decide
    w := ![![24502272, -245760, 1077248], ![-5771264, 57344, -253952]]
    hw := by decide
    g := ![![![1001321385407397, 335552210961195079, -2421510528592460], ![-154474015798975, 1416929589302102314, 0]], ![![296202539891297, 99260256098972899, -716311045979796], ![-45695214837711, 419144292047606347, 0]]]
    h := ![![![142983, -2726659, -353435], ![28553, 9643764, 0]], ![![-33715, 642236, 83248], ![-6602, -2271490, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R191N1 : Ideal.span {4096} * I191N1 =  Ideal.span {B.equivFun.symm ![5982, -60, 263]} * (J0 ^ 12) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_12 E191RS1 


noncomputable def E191RS2 : RelationCertificate Table 256 ![![191, 0, 0], ![-75, 1, 0]]
  ![82, -36, 17] ![![256, 0, 0], ![57, 1, 0]] where
    su := ![![48896, 0, 0], ![-19200, 256, 0]]
    hsu := by decide
    w := ![![20992, -9216, 4352], ![5632, -2304, 768]]
    hw := by decide
    g := ![![![-91292712798951, 1698202457556919, 220130421796431], ![-13693289734163, -8050483997126613, 0]], ![![35847919165155, -666833338151337, -86438635948244], ![5376945524538, 3161184400392921, 0]]]
    h := ![![![-1015, -30477, 2735], ![399, -74624, 0]], ![![-283, -8168, 733], ![79, -20000, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R191N2 : Ideal.span {256} * I191N2 =  Ideal.span {B.equivFun.symm ![82, -36, 17]} * (J0 ^ 8) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8 E191RS2 
