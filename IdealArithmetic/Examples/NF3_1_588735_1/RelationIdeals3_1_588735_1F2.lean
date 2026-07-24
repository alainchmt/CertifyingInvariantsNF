import IdealArithmetic.Examples.NF3_1_588735_1.PrimesBelow3_1_588735_1F2
import IdealArithmetic.Examples.NF3_1_588735_1.ClassGroupData3_1_588735_1

set_option linter.all false

noncomputable section


noncomputable def E83RS1 : RelationCertificate Table 3025 ![![83, 0, 0], ![-19, 1, 0]]
  ![-1459, 34, -65] ![![3025, 0, 0], ![-1348, 1, 0]] where
    su := ![![251075, 0, 0], ![-57475, 3025, 0]]
    hsu := by decide
    w := ![![-4413475, 102850, -196625], ![1963225, -45375, 87725]]
    hw := by decide
    g := ![![![5201704, -4669123780, 17305687], ![-3861259, -10470054324, -422]], ![![-1133295, 1017894678, -3772735], ![843358, 2282529460, 92]]]
    h := ![![![-7808, 84383, -21105], ![2845, 350330, 0]], ![![3482, -37536, 9388], ![-1227, -155835, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {3025} * I83N1 =  Ideal.span {B.equivFun.symm ![-1459, 34, -65]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E83RS1 


noncomputable def E89RS0 : RelationCertificate Table 275 ![![89, 0, 0], ![29, 1, 0]]
  ![-2932, -18, -95] ![![275, 0, 0], ![27, 1, 0]] where
    su := ![![24475, 0, 0], ![7975, 275, 0]]
    hsu := by decide
    w := ![![-806300, -4950, -26125], ![-84425, -550, -2750]]
    hw := by decide
    g := ![![![-207043, -2728796, -524838], ![-30101, 28863880, 395]], ![![-68158, -898114, -172737], ![-9753, 9499808, 130]]]
    h := ![![![59409852, 969394558, 173166865], ![30250368, -3082370216, 0]], ![![6220555, 101501204, 18131570], ![3167386, -322741948, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N0 : Ideal.span {275} * I89N0 =  Ideal.span {B.equivFun.symm ![-2932, -18, -95]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E89RS0 


noncomputable def E89RS1 : RelationCertificate Table 275 ![![89, 0, 0], ![31, 1, 0]]
  ![2, -27, -5] ![![275, 0, 0], ![27, 1, 0]] where
    su := ![![24475, 0, 0], ![8525, 275, 0]]
    hsu := by decide
    w := ![![550, -7425, -1375], ![-275, -550, -275]]
    hw := by decide
    g := ![![![-27369166130, -360788821657, -69389800459], ![-3999113567, 3816232068024, 36956646]], ![![-9606396056, -126634487113, -24355360434], ![-1403662440, 1339472183256, 12971538]]]
    h := ![![![-65, -960, -160], ![3, 2847, 0]], ![![-14, 275, 46], ![93, -819, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {275} * I89N1 =  Ideal.span {B.equivFun.symm ![2, -27, -5]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E89RS1 


noncomputable def E97RS1 : RelationCertificate Table 3025 ![![97, 0, 0], ![-30, 1, 0]]
  ![-282781, -1519, -9285] ![![3025, 0, 0], ![-1348, 1, 0]] where
    su := ![![293425, 0, 0], ![-90750, 3025, 0]]
    hsu := by decide
    w := ![![-855412525, -4594975, -28087125], ![380675075, 2044900, 12499300]]
    hw := by decide
    g := ![![![1013858518626682, -910070307005793308, 3373130147743006], ![-752645153756381, -2040743833452337476, -349175274]], ![![-302453591691069, 271491562174004703, -1006269918024202], ![224528596288882, 608793328466890692, 104165733]]]
    h := ![![![-62327696507, 1113185154498, -179597128015], ![30752742829, 3484184281634, 0]], ![![27737027229, -495388866231, 79924186256], ![-13685563657, -1550529212540, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {3025} * I97N1 =  Ideal.span {B.equivFun.symm ![-282781, -1519, -9285]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E97RS1 


noncomputable def E103RS0 : RelationCertificate Table 121 ![![103, 0, 0], ![5, 1, 0]]
  ![-15, 21, -1] ![![121, 0, 0], ![-17, 1, 0]] where
    su := ![![12463, 0, 0], ![605, 121, 0]]
    hsu := by decide
    w := ![![-1815, 2541, -121], ![242, -363, 121]]
    hw := by decide
    g := ![![![9800, -90785, 25223], ![-2090, -610393, 0]], ![![513, -4701, 1306], ![-69, -31605, 0]]]
    h := ![![![-114, -222, -277], ![63, 5706, 0]], ![![12, 29, 37], ![58, -762, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N0 : Ideal.span {121} * I103N0 =  Ideal.span {B.equivFun.symm ![-15, 21, -1]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E103RS0 


noncomputable def E103RS1 : RelationCertificate Table 121 ![![103, 0, 0], ![36, 1, 0]]
  ![13587, 72, 446] ![![121, 0, 0], ![-17, 1, 0]] where
    su := ![![12463, 0, 0], ![4356, 121, 0]]
    hsu := by decide
    w := ![![1644027, 8712, 53966], ![-206305, -1089, -6776]]
    hw := by decide
    g := ![![![-73940763, 685634980, -190491018], ![16054888, 4609882632, 0]], ![![-26751222, 248057667, -68918242], ![5808536, 1667821456, 0]]]
    h := ![![![201987, 4213916, 602147], ![111589, -12404139, 0]], ![![-25371, -528795, -75562], ![-13934, 1556566, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {121} * I103N1 =  Ideal.span {B.equivFun.symm ![13587, 72, 446]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E103RS1 


noncomputable def E103RS2 : RelationCertificate Table 121 ![![103, 0, 0], ![-41, 1, 0]]
  ![53, -50, 60] ![![121, 0, 0], ![-17, 1, 0]] where
    su := ![![12463, 0, 0], ![-4961, 121, 0]]
    hsu := by decide
    w := ![![6413, -6050, 7260], ![2299, -847, -1210]]
    hw := by decide
    g := ![![![-2340, 19641, -5465], ![531, 132069, 0]], ![![924, -7692, 2140], ![-135, -51718, 0]]]
    h := ![![![5, 256, -30], ![42, 630, 0]], ![![1, 83, -10], ![12, 204, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N2 : Ideal.span {121} * I103N2 =  Ideal.span {B.equivFun.symm ![53, -50, 60]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E103RS2 


noncomputable def E107RS0 : RelationCertificate Table 275 ![![107, 0, 0], ![41, 1, 0]]
  ![-44461, -239, -1460] ![![275, 0, 0], ![27, 1, 0]] where
    su := ![![29425, 0, 0], ![11275, 275, 0]]
    hsu := by decide
    w := ![![-12226775, -65725, -401500], ![-1281225, -6875, -42075]]
    hw := by decide
    g := ![![![-12968151020, -170981023364, -32883049981], ![-1894985740, 1808533145612, 6179166]], ![![-5249013507, -69206604681, -13309805942], ![-767018039, 732025320696, 2501091]]]
    h := ![![![62855, 1561825, 195260], ![38726, -4178856, 0]], ![![6575, 163661, 20461], ![4088, -437896, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N0 : Ideal.span {275} * I107N0 =  Ideal.span {B.equivFun.symm ![-44461, -239, -1460]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E107RS0 


noncomputable def E107RS1 : RelationCertificate Table 121 ![![107, 0, 0], ![-30, 1, 0]]
  ![-1913, -8, -63] ![![121, 0, 0], ![-17, 1, 0]] where
    su := ![![12947, 0, 0], ![-3630, 121, 0]]
    hsu := by decide
    w := ![![-231473, -968, -7623], ![29040, 121, 968]]
    hw := by decide
    g := ![![![6983, -64648, 17961], ![-1437, -434656, 0]], ![![-1889, 17643, -4902], ![512, 118628, 0]]]
    h := ![![![-33646735, 586189974, -94569249], ![14912170, 2023781916, 0]], ![![4221238, -73541882, 11864414], ![-1870823, -253898458, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {121} * I107N1 =  Ideal.span {B.equivFun.symm ![-1913, -8, -63]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E107RS1 


noncomputable def E107RS2 : RelationCertificate Table 5 ![![107, 0, 0], ![-11, 1, 0]]
  ![-11, 1, 0] ![![5, 0, 0], ![2, 1, 0]] where
    su := ![![535, 0, 0], ![-55, 5, 0]]
    hsu := by decide
    w := ![![-55, 5, 0], ![-20, -10, 5]]
    hw := by decide
    g := ![![![3823448, -2514759, 230947], ![1026433, 0, -384912]], ![![-265519, 174635, -16038], ![-71275, 0, 26730]]]
    h := ![![![-6711, 40981, -17080], ![1178, 365512, 0]], ![![-2421, 14773, -6157], ![407, 131760, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N2 : Ideal.span {5} * I107N2 =  Ideal.span {B.equivFun.symm ![-11, 1, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E107RS2 


noncomputable def E113RS1 : RelationCertificate Table 55 ![![113, 0, 0], ![-19, 1, 0]]
  ![129, -64, -20] ![![55, 0, 0], ![27, 1, 0]] where
    su := ![![6215, 0, 0], ![-1045, 55, 0]]
    hsu := by decide
    w := ![![7095, -3520, -1100], ![2255, -935, -880]]
    hw := by decide
    g := ![![![6573717919, 119862830000, 23069447916], ![5406422084, -253763926032, -162]], ![![-892562624, -16274668368, -3132310611], ![-734070119, 34455416577, 22]]]
    h := ![![![3299, -34354, 8590], ![-822, -194138, 0]], ![![1059, -10911, 2728], ![-194, -61656, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {55} * I113N1 =  Ideal.span {B.equivFun.symm ![129, -64, -20]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E113RS1 


noncomputable def E131RS1 : RelationCertificate Table 275 ![![131, 0, 0], ![64, 1, 0]]
  ![-93, 18, 95] ![![275, 0, 0], ![27, 1, 0]] where
    su := ![![36025, 0, 0], ![17600, 275, 0]]
    hsu := by decide
    w := ![![-25575, 4950, 26125], ![2750, -2475, 2750]]
    hw := by decide
    g := ![![![13872235994, 183147055669, 35211720594], ![2027990754, -1937113675773, 83757660]], ![![6861536086, 90588866244, 17416549971], ![1003092161, -958142248221, 41428520]]]
    h := ![![![2471, 110099, 8740], ![2096, -228969, 0]], ![![-316, -12033, -955], ![-135, 25023, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {275} * I131N1 =  Ideal.span {B.equivFun.symm ![-93, 18, 95]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E131RS1 


noncomputable def E137RS1 : RelationCertificate Table 11 ![![137, 0, 0], ![-44, 1, 0]]
  ![-8408, -45, -276] ![![11, 0, 0], ![5, 1, 0]] where
    su := ![![1507, 0, 0], ![-484, 11, 0]]
    hsu := by decide
    w := ![![-92488, -495, -3036], ![-57310, -308, -1881]]
    hw := by decide
    g := ![![![-1389224, -3559898, -4558397], ![-955087, 10028480, 0]], ![![433986, 1112099, 1424028], ![298375, -3132864, 0]]]
    h := ![![![56010, -1468762, 163217], ![-28696, -4472201, 0]], ![![34722, -910115, 101137], ![-17733, -2771188, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {11} * I137N1 =  Ideal.span {B.equivFun.symm ![-8408, -45, -276]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E137RS1 
