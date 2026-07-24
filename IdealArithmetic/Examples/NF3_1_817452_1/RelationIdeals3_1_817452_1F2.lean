import IdealArithmetic.Examples.NF3_1_817452_1.PrimesBelow3_1_817452_1F2
import IdealArithmetic.Examples.NF3_1_817452_1.ClassGroupData3_1_817452_1

set_option linter.all false

noncomputable section


noncomputable def E89RS1 : RelationCertificate Table 26 ![![89, 0, 0], ![-11, 1, 0]]
  ![-536, -96, -17] ![![26, 0, 0], ![2, 1, 0]] where
    su := ![![2314, 0, 0], ![-286, 26, 0]]
    hsu := by decide
    w := ![![-13936, -2496, -442], ![-4030, -728, -130]]
    hw := by decide
    g := ![![![6383, -2171892, -1087544], ![-83043, 28276140, 0]], ![![3784273, -1286652956, -644272546], ![-49195545, 16751086197, 0]]]
    h := ![![![-156032, 14401, -20], ![-1262392, 1763, 0]], ![![-45123, 4167, -6], ![-365072, 529, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {26} * I89N1 =  Ideal.span {B.equivFun.symm ![-536, -96, -17]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E89RS1 


noncomputable def E97RS0 : RelationCertificate Table 650 ![![97, 0, 0], ![-42, 1, 0]]
  ![1168, -168, -7] ![![650, 0, 0], ![-24, 1, 0]] where
    su := ![![63050, 0, 0], ![-27300, 650, 0]]
    hsu := by decide
    w := ![![759200, -109200, -4550], ![-29250, 5200, 0]]
    hw := by decide
    g := ![![![16, 25994, -1083], ![359, 704006, 0]], ![![888, 15327562, -638650], ![24078, 415122479, 0]]]
    h := ![![![39093412, -1050584, 2852], ![90287138, -276651, 0]], ![![-1506453, 40488, -110], ![-3479188, 10670, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N0 : Ideal.span {650} * I97N0 =  Ideal.span {B.equivFun.symm ![1168, -168, -7]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E97RS0 


noncomputable def E97RS1 : RelationCertificate Table 81250 ![![97, 0, 0], ![-40, 1, 0]]
  ![-7972, -1578, 503] ![![81250, 0, 0], ![4526, 1, 0]] where
    su := ![![7881250, 0, 0], ![-3250000, 81250, 0]]
    hsu := by decide
    w := ![![-647725000, -128212500, 40868750], ![-35993750, -7150000, 2275000]]
    hw := by decide
    g := ![![![-66189846352, 96843190337574336, 21397081385815], ![1188229124193, -1738512862597468830, 0]], ![![520953404871329318, -762213438699906146418505, -168407741673665164319], ![-9352068967254862370, 13683129010985294600918779, 0]]]
    h := ![![![-88276, 2396, 0], ![-213870, 503, 0]], ![![-4899, 133, 0], ![-11869, 28, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {81250} * I97N1 =  Ideal.span {B.equivFun.symm ![-7972, -1578, 503]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E97RS1 


noncomputable def E97RS2 : RelationCertificate Table 3125 ![![97, 0, 0], ![-15, 1, 0]]
  ![-5224477, -935823, -167627] ![![3125, 0, 0], ![1401, 1, 0]] where
    su := ![![303125, 0, 0], ![-46875, 3125, 0]]
    hsu := by decide
    w := ![![-16326490625, -2924446875, -523834375], ![-7348659375, -1316312500, -235781250]]
    hw := by decide
    g := ![![![11737208069, -98257666401811, -70133957730], ![-26180424832, 219168617905840, 0]], ![![-1796979648, 15043356169561, 10737585619], ![4008252245, -33554955059336, 0]]]
    h := ![![![-13295296, 889703, -2834], ![-85627949, 107271, 0]], ![![-5984298, 400467, -1276], ![-38541689, 48322, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N2 : Ideal.span {3125} * I97N2 =  Ideal.span {B.equivFun.symm ![-5224477, -935823, -167627]} * (J0 ^ 5*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_0 E97RS2 


noncomputable def E107RS1 : RelationCertificate Table 125 ![![107, 0, 0], ![53, 1, 0]]
  ![-107, 57, -7] ![![125, 0, 0], ![26, 1, 0]] where
    su := ![![13375, 0, 0], ![6625, 125, 0]]
    hsu := by decide
    w := ![![-13375, 7125, -875], ![-4000, 1375, -125]]
    hw := by decide
    g := ![![![41, -45027, -1732], ![-222, 216480, 0]], ![![29, -22591, -869], ![-153, 108614, 0]]]
    h := ![![![-152800, -5529, -50], ![308481, 5343, 0]], ![![-46036, -1663, -15], ![92940, 1604, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {125} * I107N1 =  Ideal.span {B.equivFun.symm ![-107, 57, -7]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E107RS1 


noncomputable def E113RS1 : RelationCertificate Table 130 ![![113, 0, 0], ![-26, 1, 0]]
  ![56, 24, 1] ![![130, 0, 0], ![-24, 1, 0]] where
    su := ![![14690, 0, 0], ![-3380, 130, 0]]
    hsu := by decide
    w := ![![7280, 3120, 130], ![-1170, -520, 0]]
    hw := by decide
    g := ![![![16, 5424, -226], ![87, 29384, 0]], ![![44, 26734, -1114], ![238, 144819, 0]]]
    h := ![![![198340, -7992, 14], ![862014, -1581, 0]], ![![-31851, 1303, -3], ![-138429, 339, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {130} * I113N1 =  Ideal.span {B.equivFun.symm ![56, 24, 1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E113RS1 


noncomputable def E127RS0 : RelationCertificate Table 26 ![![127, 0, 0], ![-49, 1, 0]]
  ![46, -36, 5] ![![26, 0, 0], ![2, 1, 0]] where
    su := ![![3302, 0, 0], ![-1274, 26, 0]]
    hsu := by decide
    w := ![![1196, -936, 130], ![962, -26, -26]]
    hw := by decide
    g := ![![![234215416, -79633224923, -39875166306], ![-3044799765, 1036754323997, 0]], ![![-92210563, 31351585117, 15698845196], ![1198737099, -408169975110, 0]]]
    h := ![![![75198, -1680, 3], ![194900, -376, 0]], ![![60300, -1329, 2], ![156287, -255, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N0 : Ideal.span {26} * I127N0 =  Ideal.span {B.equivFun.symm ![46, -36, 5]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E127RS0 


noncomputable def E127RS1 : RelationCertificate Table 650 ![![127, 0, 0], ![-42, 1, 0]]
  ![1174, 76, -51] ![![650, 0, 0], ![-24, 1, 0]] where
    su := ![![82550, 0, 0], ![-27300, 650, 0]]
    hsu := by decide
    w := ![![763100, 49400, -33150], ![-37050, -650, 1300]]
    hw := by decide
    g := ![![![-148615703669, -2619822393751833, 109159524419701], ![-4025008641167, -70953690872805549, 0]], ![![50318683959, 887026147027599, -36959510151643], ![1362797690594, 24023681598567921, 0]]]
    h := ![![![32490694, -848784, 1790], ![98245642, -227381, 0]], ![![-1577829, 41222, -87], ![-4771053, 11051, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N1 : Ideal.span {650} * I127N1 =  Ideal.span {B.equivFun.symm ![1174, 76, -51]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E127RS1 


noncomputable def E127RS2 : RelationCertificate Table 625 ![![127, 0, 0], ![-36, 1, 0]]
  ![-163, 88, -13] ![![625, 0, 0], ![151, 1, 0]] where
    su := ![![79375, 0, 0], ![-22500, 625, 0]]
    hsu := by decide
    w := ![![-101875, 55000, -8125], ![-26875, 13125, -1875]]
    hw := by decide
    g := ![![![69301742, -189742960684, -1256578938], ![-286844961, 785361836241, 0]], ![![-18136541, 49656060015, 328848875], ![75068465, -205530546873, 0]]]
    h := ![![![-3493, 130, -1], ![-12318, 114, 0]], ![![-925, 61, -1], ![-3262, 124, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N2 : Ideal.span {625} * I127N2 =  Ideal.span {B.equivFun.symm ![-163, 88, -13]} * (J0 ^ 4*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_0 E127RS2 


noncomputable def E131RS1 : RelationCertificate Table 130 ![![131, 0, 0], ![-33, 1, 0]]
  ![15182, 2718, 487] ![![130, 0, 0], ![-24, 1, 0]] where
    su := ![![17030, 0, 0], ![-4290, 130, 0]]
    hsu := by decide
    w := ![![1973660, 353340, 63310], ![-279630, -50050, -8970]]
    hw := by decide
    g := ![![![96140566, 70006343351, -2917097884], ![520761343, 379222724873, 0]], ![![-24952509, -18169585358, 757109377], ![-135159407, -98424218998, 0]]]
    h := ![![![22438, -665, 4], ![88612, -37, 0]], ![![-3129, 107, -1], ![-12356, 62, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {130} * I131N1 =  Ideal.span {B.equivFun.symm ![15182, 2718, 487]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E131RS1 


noncomputable def E137RS1 : RelationCertificate Table 3125 ![![137, 0, 0], ![37, 1, 0]]
  ![-2107, 432, -7] ![![3125, 0, 0], ![1401, 1, 0]] where
    su := ![![428125, 0, 0], ![115625, 3125, 0]]
    hsu := by decide
    w := ![![-6584375, 1350000, -21875], ![-2953125, 603125, -9375]]
    hw := by decide
    g := ![![![26008, -228022563, -162757], ![-58011, 508615680, 0]], ![![6434, -61715454, -44051], ![-14351, 137659392, 0]]]
    h := ![![![-153907141, -4607236, -12097], ![569872330, 1657282, 0]], ![![-69028473, -2066394, -5426], ![255591888, 743359, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {3125} * I137N1 =  Ideal.span {B.equivFun.symm ![-2107, 432, -7]} * (J0 ^ 5*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_0 E137RS1 
