import IdealArithmetic.Examples.NF3_1_960204_2.PrimesBelow3_1_960204_2F2
import IdealArithmetic.Examples.NF3_1_960204_2.ClassGroupData3_1_960204_2

set_option linter.all false

noncomputable section


noncomputable def E89RS0 : RelationCertificate Table 9 ![![89, 0, 0], ![17, 1, 0]]
  ![-52818, -87, -1253] ![![9, 0, 0], ![26, 0, 1]] where
    su := ![![801, 0, 0], ![153, 9, 0]]
    hsu := by decide
    w := ![![-475362, -783, -11277], ![-1437849, -2367, -34110]]
    hw := by decide
    g := ![![![-4360, 12679, 592], ![-12465, 7120, 0]], ![![-788, 2280, 107], ![-2240, 1280, 0]]]
    h := ![![![9811340, -157317656, -29496850], ![106513, 875072799, 0]], ![![29676831, -475845869, -89220464], ![322046, 2646872502, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N0 : Ideal.span {9} * I89N0 =  Ideal.span {B.equivFun.symm ![-52818, -87, -1253]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E89RS0 


noncomputable def E89RS1 : RelationCertificate Table 33 ![![89, 0, 0], ![23, 1, 0]]
  ![-87, -3, -2] ![![33, 0, 0], ![29, 0, 1]] where
    su := ![![2937, 0, 0], ![759, 33, 0]]
    hsu := by decide
    w := ![![-2871, -99, -66], ![-2772, 33, -66]]
    hw := by decide
    g := ![![![-8282397, 3742066, -67230], ![-7280501, 9499090, 0]], ![![-2140506, 967100, -17375], ![-1881571, 2454946, 0]]]
    h := ![![![1252, -27970, -3814], ![71, 113148, 0]], ![![1209, -27046, -3688], ![75, 109410, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {33} * I89N1 =  Ideal.span {B.equivFun.symm ![-87, -3, -2]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E89RS1 


noncomputable def E89RS2 : RelationCertificate Table 121 ![![89, 0, 0], ![-40, 1, 0]]
  ![332, 5, 7] ![![121, 0, 0], ![-55, 1, 0]] where
    su := ![![10769, 0, 0], ![-4840, 121, 0]]
    hsu := by decide
    w := ![![40172, 605, 847], ![-17908, -242, -363]]
    hw := by decide
    g := ![![![778, 42298, -2266], ![49, 91395, 0]], ![![-327, -18480, 990], ![7, -39930, 0]]]
    h := ![![![1303, 51961, -3802], ![71, 112795, 0]], ![![-546, -23166, 1695], ![46, -50286, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N2 : Ideal.span {121} * I89N2 =  Ideal.span {B.equivFun.symm ![332, 5, 7]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E89RS2 


noncomputable def E101RS1 : RelationCertificate Table 3 ![![101, 0, 0], ![5, 1, 0]]
  ![87, 0, 2] ![![3, 0, 0], ![29, 0, 1]] where
    su := ![![303, 0, 0], ![15, 3, 0]]
    hsu := by decide
    w := ![![261, 0, 6], ![2619, 6, 63]]
    hw := by decide
    g := ![![![145, -3500, -200], ![1406, -808, 0]], ![![3, -173, -10], ![70, -40, 0]]]
    h := ![![![-19806, 79263, 59446], ![-171, -2001348, 0]], ![![-198726, 795343, 596493], ![-1945, -20081924, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {3} * I101N1 =  Ideal.span {B.equivFun.symm ![87, 0, 2]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E101RS1 


noncomputable def E103RS1 : RelationCertificate Table 33 ![![103, 0, 0], ![-17, 1, 0]]
  ![108, -60, -29] ![![33, 0, 0], ![29, 0, 1]] where
    su := ![![3399, 0, 0], ![-561, 33, 0]]
    hsu := by decide
    w := ![![3564, -1980, -957], ![-1320, 693, 396]]
    hw := by decide
    g := ![![![14620, -6083, 127], ![12857, -15450, 0]], ![![-2410, 1006, -21], ![-2107, 2555, 0]]]
    h := ![![![309, 5319, -887], ![75, 30444, 0]], ![![-94, -1962, 327], ![93, -11223, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {33} * I103N1 =  Ideal.span {B.equivFun.symm ![108, -60, -29]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E103RS1 


noncomputable def E109RS1 : RelationCertificate Table 1089 ![![109, 0, 0], ![50, 1, 0]]
  ![-63183, -102, -1498] ![![1089, 0, 0], ![62, 0, 1]] where
    su := ![![118701, 0, 0], ![54450, 1089, 0]]
    hsu := by decide
    w := ![![-68806287, -111078, -1631322], ![-3994452, -6534, -94743]]
    hw := by decide
    g := ![![![-179570840111, -70648266066, -3523022362], ![-10226735012, 3846798087288, 0]], ![![-7382950789111, -2904662424477, -144847018106], ![-420466295311, 158158869012769, 0]]]
    h := ![![![41093, -2044907, -125212], ![131, 4548870, 0]], ![![2340, -118715, -7269], ![107, 264078, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {1089} * I109N1 =  Ideal.span {B.equivFun.symm ![-63183, -102, -1498]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E109RS1 


noncomputable def E113RS1 : RelationCertificate Table 363 ![![113, 0, 0], ![41, 1, 0]]
  ![17910, 27, 425] ![![363, 0, 0], ![62, 0, 1]] where
    su := ![![41019, 0, 0], ![14883, 363, 0]]
    hsu := by decide
    w := ![![6501330, 9801, 154275], ![1132197, 1815, 26862]]
    hw := by decide
    g := ![![![25074127334, 10119932909, 494195007], ![4283994750, -183676782292, 0]], ![![8875797504, 3582277228, 174936290], ![1516458419, -65018331686, 0]]]
    h := ![![![660615869, -26499860762, -1987486115], ![5180533, 74861977140, 0]], ![![115045138, -4614907220, -346117442], ![902265, 13037090340, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {363} * I113N1 =  Ideal.span {B.equivFun.symm ![17910, 27, 425]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E113RS1 


noncomputable def E127RS1 : RelationCertificate Table 363 ![![127, 0, 0], ![-34, 1, 0]]
  ![3483504, 5736, 82639] ![![363, 0, 0], ![62, 0, 1]] where
    su := ![![46101, 0, 0], ![-12342, 363, 0]]
    hsu := by decide
    w := ![![1264511952, 2082168, 29997957], ![220236456, 362637, 5224659]]
    hw := by decide
    g := ![![![163110, 65831, 3215], ![27976, -1194927, 0]], ![![1024760735307, 413594050542, 20197378437], ![175083644612, -7506732017312, 0]]]
    h := ![![![-70940605508, -2478043896562, 212404114297], ![-520183490, -8991774144360, 0]], ![![-12355523803, -431593869157, 36993821474], ![-90598787, -1566071770935, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N1 : Ideal.span {363} * I127N1 =  Ideal.span {B.equivFun.symm ![3483504, 5736, 82639]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E127RS1 


noncomputable def E131RS1 : RelationCertificate Table 33 ![![131, 0, 0], ![-26, 1, 0]]
  ![-21, -3, -2] ![![33, 0, 0], ![29, 0, 1]] where
    su := ![![4323, 0, 0], ![-858, 33, 0]]
    hsu := by decide
    w := ![![-693, -99, -66], ![-858, 33, 0]]
    hw := by decide
    g := ![![![-2354683, 1063859, -19114], ![-2069808, 2700565, 0]], ![![468279, -211575, 3801], ![411643, -537075, 0]]]
    h := ![![![17, -127, 14], ![110, -612, 0]], ![![-6, -162, 18], ![1, -786, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {33} * I131N1 =  Ideal.span {B.equivFun.symm ![-21, -3, -2]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E131RS1 


noncomputable def E137RS1 : RelationCertificate Table 1089 ![![137, 0, 0], ![-18, 1, 0]]
  ![-5772, 2301, 2447] ![![1089, 0, 0], ![62, 0, 1]] where
    su := ![![149193, 0, 0], ![-19602, 1089, 0]]
    hsu := by decide
    w := ![![-6285708, 2505789, 2664783], ![-123057, 53361, 47916]]
    hw := by decide
    g := ![![![31194776, 12268851, 612057], ![1776762, -668038004, 0]], ![![-4325930, -1701423, -84876], ![-245354, 92642368, 0]]]
    h := ![![![241531905, 4584771978, -723913340], ![1731486, 33058710009, 0]], ![![4732850, 89839082, -14185157], ![33984, 647788851, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {1089} * I137N1 =  Ideal.span {B.equivFun.symm ![-5772, 2301, 2447]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E137RS1 
