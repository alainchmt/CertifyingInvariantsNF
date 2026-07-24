import IdealArithmetic.Examples.NF3_1_960204_2.PrimesBelow3_1_960204_2F4
import IdealArithmetic.Examples.NF3_1_960204_2.ClassGroupData3_1_960204_2

set_option linter.all false

noncomputable section


noncomputable def E197RS1 : RelationCertificate Table 363 ![![197, 0, 0], ![71, 1, 0]]
  ![1668, 12, 41] ![![363, 0, 0], ![62, 0, 1]] where
    su := ![![71511, 0, 0], ![25773, 363, 0]]
    hsu := by decide
    w := ![![605484, 4356, 14883], ![105996, 363, 2541]]
    hw := by decide
    g := ![![![15569316490121, 6283785521199, 306861266561], ![2660067448131, -114050707209764, 0]], ![![5532495964219, 2232918706361, 109041955689], ![945244605349, -40527474520453, 0]]]
    h := ![![![-67060854, 4701873270, 201508789], ![-301698, -13232410464, 0]], ![![-11740065, 823137664, 35277317], ![-52827, -2316543814, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R197N1 : Ideal.span {363} * I197N1 =  Ideal.span {B.equivFun.symm ![1668, 12, 41]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E197RS1 


noncomputable def E197RS2 : RelationCertificate Table 99 ![![197, 0, 0], ![-78, 1, 0]]
  ![282, -186, -47] ![![99, 0, 0], ![62, 0, 1]] where
    su := ![![19503, 0, 0], ![-7722, 99, 0]]
    hsu := by decide
    w := ![![27918, -18414, -4653], ![5742, -3861, -891]]
    hw := by decide
    g := ![![![-2188805609, -1195119701, -45905192], ![-1371230800, 5915842512, 0]], ![![1098366439531, 599724248978, 23035722204], ![688098535137, -2968635032438, 0]]]
    h := ![![![-16272, -1286259, 48845], ![21, -3207504, 0]], ![![-3302, -264573, 10047], ![118, -659756, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R197N2 : Ideal.span {99} * I197N2 =  Ideal.span {B.equivFun.symm ![282, -186, -47]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E197RS2 


noncomputable def E199RS1 : RelationCertificate Table 11 ![![199, 0, 0], ![49, 1, 0]]
  ![-21, 19, -2] ![![11, 0, 0], ![0, 1, 0]] where
    su := ![![2189, 0, 0], ![539, 11, 0]]
    hsu := by decide
    w := ![![-231, 209, -22], ![-121, 44, 55]]
    hw := by decide
    g := ![![![-180, 212, -653], ![20, 2360, 0]], ![![-45, 53, -166], ![15, 600, 0]]]
    h := ![![![14599, -703713, -43982], ![250, 2917472, 0]], ![![7586, -365585, -22849], ![123, 1515652, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R199N1 : Ideal.span {11} * I199N1 =  Ideal.span {B.equivFun.symm ![-21, 19, -2]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E199RS1 


noncomputable def E211RS1 : RelationCertificate Table 99 ![![211, 0, 0], ![-57, 1, 0]]
  ![133203, 219, 3160] ![![99, 0, 0], ![62, 0, 1]] where
    su := ![![20889, 0, 0], ![-5643, 99, 0]]
    hsu := by decide
    w := ![![13187097, 21681, 312840], ![8421435, 13860, 199782]]
    hw := by decide
    g := ![![![72357788144, 39508417782, 1517538999], ![45330307114, -195566667998, 0]], ![![-19546890669, -10672890108, -409951294], ![-12245627920, 52830806028, 0]]]
    h := ![![![488249841, 28284695493, -1463002004], ![2153940, 102897808668, 0]], ![![311802056, 18062937862, -934290217], ![1375488, 65711745935, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R211N1 : Ideal.span {99} * I211N1 =  Ideal.span {B.equivFun.symm ![133203, 219, 3160]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E211RS1 


noncomputable def E227RS1 : RelationCertificate Table 3 ![![227, 0, 0], ![-37, 1, 0]]
  ![-34608, -57, -821] ![![3, 0, 0], ![29, 0, 1]] where
    su := ![![681, 0, 0], ![-111, 3, 0]]
    hsu := by decide
    w := ![![-103824, -171, -2463], ![-1045947, -1722, -24813]]
    hw := by decide
    g := ![![![-65, 1048, 70], ![-402, 227, 0]], ![![6, -178, -11], ![68, -38, 0]]]
    h := ![![![9263438, 351769363, -27771283], ![39862, 2101360140, 0]], ![![93321866, 3543805989, -279774333], ![400643, 21169588440, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R227N1 : Ideal.span {3} * I227N1 =  Ideal.span {B.equivFun.symm ![-34608, -57, -821]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E227RS1 


noncomputable def E229RS1 : RelationCertificate Table 9 ![![229, 0, 0], ![54, 1, 0]]
  ![23691, 39, 562] ![![9, 0, 0], ![26, 0, 1]] where
    su := ![![2061, 0, 0], ![486, 9, 0]]
    hsu := by decide
    w := ![![213219, 351, 5058], ![644931, 1062, 15300]]
    hw := by decide
    g := ![![![11001, -32160, -1516], ![31680, -18091, 0]], ![![2542, -7442, -351], ![7333, -4187, 0]]]
    h := ![![![-1372839, 72836150, 4122802], ![-5615, -314707032, 0]], ![![-4152467, 220310061, 12470384], ![-17015, -951905412, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R229N1 : Ideal.span {9} * I229N1 =  Ideal.span {B.equivFun.symm ![23691, 39, 562]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E229RS1 


noncomputable def E233RS1 : RelationCertificate Table 121 ![![233, 0, 0], ![-11, 1, 0]]
  ![9121, 16, 216] ![![121, 0, 0], ![-55, 1, 0]] where
    su := ![![28193, 0, 0], ![-1331, 121, 0]]
    hsu := by decide
    w := ![![1103641, 1936, 26136], ![-490655, -847, -11616]]
    hw := by decide
    g := ![![![6863, 382307, -20481], ![77, 826059, 0]], ![![-291, -16520, 885], ![9, -35695, 0]]]
    h := ![![![-382832, -4593626, 1148409], ![-1450, -89193027, 0]], ![![170205, 2042227, -510558], ![774, 39653306, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R233N1 : Ideal.span {121} * I233N1 =  Ideal.span {B.equivFun.symm ![9121, 16, 216]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E233RS1 


noncomputable def E241RS0 : RelationCertificate Table 3 ![![241, 0, 0], ![16, 1, 0]]
  ![0, 0, 1] ![![3, 0, 0], ![29, 0, 1]] where
    su := ![![723, 0, 0], ![48, 3, 0]]
    hsu := by decide
    w := ![![0, 0, 3], ![48, 3, -12]]
    hw := by decide
    g := ![![![0, 2117995, 147567], ![-870255, 489968, 5200]], ![![0, 140578, 9780], ![-57755, 32520, 342]]]
    h := ![![![-13, -41, -8], ![236, 643, 0]], ![![-12, 160, 32], ![21, -2572, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R241N0 : Ideal.span {3} * I241N0 =  Ideal.span {B.equivFun.symm ![0, 0, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E241RS0 


noncomputable def E241RS1 : RelationCertificate Table 1089 ![![241, 0, 0], ![29, 1, 0]]
  ![-519, 435, 4] ![![1089, 0, 0], ![62, 0, 1]] where
    su := ![![262449, 0, 0], ![31581, 1089, 0]]
    hsu := by decide
    w := ![![-565191, 473715, 4356], ![-9801, 8712, 0]]
    hw := by decide
    g := ![![![-10652497912491, -4190995077332, -208992664597], ![-606670214069, 228199681960729, 0]], ![![-1283797565050, -505082405984, -25186982070], ![-73113531533, 27501737005829, 0]]]
    h := ![![![834, -24210, -2594], ![237, 208386, 0]], ![![14, -420, -45], ![8, 3615, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R241N1 : Ideal.span {1089} * I241N1 =  Ideal.span {B.equivFun.symm ![-519, 435, 4]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E241RS1 


noncomputable def E241RS2 : RelationCertificate Table 11 ![![241, 0, 0], ![-45, 1, 0]]
  ![-58, 53, -5] ![![11, 0, 0], ![0, 1, 0]] where
    su := ![![2651, 0, 0], ![-495, 11, 0]]
    hsu := by decide
    w := ![![-638, 583, -55], ![-308, 99, 154]]
    hw := by decide
    g := ![![![-3416, -402, 1129], ![-35, -4402, 0]], ![![622, 74, -209], ![10, 814, 0]]]
    h := ![![![106526, 4894888, -319232], ![619, 25644969, 0]], ![![51245, 2354663, -153565], ![304, 12336393, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R241N2 : Ideal.span {11} * I241N2 =  Ideal.span {B.equivFun.symm ![-58, 53, -5]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E241RS2 
