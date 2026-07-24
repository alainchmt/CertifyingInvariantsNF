import IdealArithmetic.Examples.NF3_1_933107_3.PrimesBelow3_1_933107_3F4
import IdealArithmetic.Examples.NF3_1_933107_3.ClassGroupData3_1_933107_3

set_option linter.all false

noncomputable section


noncomputable def E197RS1 : RelationCertificate Table 20 ![![197, 0, 0], ![48, 1, 0]]
  ![103, 1, 4] ![![20, 0, 0], ![2, 1, 0]] where
    su := ![![3940, 0, 0], ![960, 20, 0]]
    hsu := by decide
    w := ![![2060, 20, 80], ![300, -20, 20]]
    hw := by decide
    g := ![![![648492711312408, 324250609702209, 2626404474368979], ![81061801616355, -6566011936636448, 2001904003]], ![![154726563048364, 77364296514645, 626644726155124], ![19340871130573, -1566611994503774, 477642571]]]
    h := ![![![-3515, -90069, -15332], ![-1303, 377551, 0]], ![![-527, -13130, -2235], ![-130, 55037, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R197N1 : Ideal.span {20} * I197N1 =  Ideal.span {B.equivFun.symm ![103, 1, 4]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E197RS1 


noncomputable def E227RS0 : RelationCertificate Table 4 ![![227, 0, 0], ![10, 1, 0]]
  ![13, -17, 4] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![908, 0, 0], ![40, 4, 0]]
    hsu := by decide
    w := ![![52, -68, 16], ![84, -128, -124]]
    hw := by decide
    g := ![![![3235043, -4750614, 449500], ![429870, 0, -599115]], ![![176427, -259121, 24517], ![23434, 0, -32679]]]
    h := ![![![15957, 72044, 64044], ![1227, -1817248, 0]], ![![25825, 116537, 103595], ![1677, -2939512, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R227N0 : Ideal.span {4} * I227N0 =  Ideal.span {B.equivFun.symm ![13, -17, 4]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E227RS0 


noncomputable def E227RS1 : RelationCertificate Table 10 ![![227, 0, 0], ![14, 1, 0]]
  ![-1, 3, 12] ![![10, 0, 0], ![2, 1, 0]] where
    su := ![![2270, 0, 0], ![140, 10, 0]]
    hsu := by decide
    w := ![![-10, 30, 120], ![280, -370, 60]]
    hw := by decide
    g := ![![![-14043042245466, -7021525598903, -58980787166841], ![-3510761008975, 73725984353502, -1053048]], ![![-968485677921, -484243147659, -4067640518685], ![-242121450349, 5084550675594, -72624]]]
    h := ![![![-69, -410, -252], ![97, 7152, 0]], ![![1730, 11338, 6978], ![237, -198000, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R227N1 : Ideal.span {10} * I227N1 =  Ideal.span {B.equivFun.symm ![-1, 3, 12]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E227RS1 


noncomputable def E227RS2 : RelationCertificate Table 25 ![![227, 0, 0], ![-24, 1, 0]]
  ![-268, -1, -9] ![![25, 0, 0], ![12, 1, 0]] where
    su := ![![5675, 0, 0], ![-600, 25, 0]]
    hsu := by decide
    w := ![![-6700, -25, -225], ![-3425, 0, -125]]
    hw := by decide
    g := ![![![2393620, 18027045, 13164979], ![1870049, -41140560, 0]], ![![-189849, -1429732, -1044119], ![-148293, 3262872, 0]]]
    h := ![![![-1360934, 17301764, -5536875], ![220246, 157108827, 0]], ![![-695731, 8844876, -2830519], ![112548, 80315976, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R227N2 : Ideal.span {25} * I227N2 =  Ideal.span {B.equivFun.symm ![-268, -1, -9]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E227RS2 


noncomputable def E229RS0 : RelationCertificate Table 2 ![![229, 0, 0], ![64, 1, 0]]
  ![-991, 1, -32] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![458, 0, 0], ![128, 2, 0]]
    hsu := by decide
    w := ![![-1982, 2, -64], ![-734, 0, -24]]
    hw := by decide
    g := ![![![210444, -226914, 9156], ![-113455, 0, -18300]], ![![63134, -68075, 2747], ![-34037, 0, -5490]]]
    h := ![![![204167, 7211413, 915784], ![88647, -26214321, 0]], ![![75573, 2670584, 339140], ![32956, -9707884, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R229N0 : Ideal.span {2} * I229N0 =  Ideal.span {B.equivFun.symm ![-991, 1, -32]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E229RS0 


noncomputable def E229RS1 : RelationCertificate Table 5 ![![229, 0, 0], ![-56, 1, 0]]
  ![3, -4, 4] ![![5, 0, 0], ![2, 1, 0]] where
    su := ![![1145, 0, 0], ![-280, 5, 0]]
    hsu := by decide
    w := ![![15, -20, 20], ![90, -125, -20]]
    hw := by decide
    g := ![![![-1530841, -765060, -7345060], ![-765344, 4590648, 0]], ![![374118, 186972, 1795052], ![187043, -1121904, 0]]]
    h := ![![![4607, -143091, 20084], ![-1693, -574904, 0]], ![![27574, -858802, 120540], ![-10473, -3450458, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R229N1 : Ideal.span {5} * I229N1 =  Ideal.span {B.equivFun.symm ![3, -4, 4]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E229RS1 


noncomputable def E229RS2 : RelationCertificate Table 100 ![![229, 0, 0], ![-8, 1, 0]]
  ![18683, -19, 604] ![![100, 0, 0], ![-38, 1, 0]] where
    su := ![![22900, 0, 0], ![-800, 100, 0]]
    hsu := by decide
    w := ![![1868300, -1900, 60400], ![-696100, 700, -22500]]
    hw := by decide
    g := ![![![-189934120841829530095, 4576468809407509651383, -939004761574446408522], ![117939654013970318045, 11737559504959838248556, -3182863104427]], ![![7464650581483491380, -179860998160164844355, 36904071835200126756], ![-4635177202565375123, -461300897361457856852, 125090535697]]]
    h := ![![![531945959, -2398197270, 2131843692], ![-29055661, -61024025608, 0]], ![![-198194905, 893531545, -794292285], ![10825872, 22736616630, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R229N2 : Ideal.span {100} * I229N2 =  Ideal.span {B.equivFun.symm ![18683, -19, 604]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E229RS2 


noncomputable def E239RS1 : RelationCertificate Table 20 ![![239, 0, 0], ![-102, 1, 0]]
  ![143, 1, 4] ![![20, 0, 0], ![2, 1, 0]] where
    su := ![![4780, 0, 0], ![-2040, 20, 0]]
    hsu := by decide
    w := ![![2860, 20, 80], ![380, 20, 20]]
    hw := by decide
    g := ![![![117149408, 58573179, 474451881], ![14643619, -1186129434, -717]], ![![-50156650, -25077672, -203133046], ![-6269539, 507832500, 307]]]
    h := ![![![351899, -23591572, 1832436], ![-248866, -54744025, 0]], ![![46751, -3132800, 243335], ![-32998, -7269633, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R239N1 : Ideal.span {20} * I239N1 =  Ideal.span {B.equivFun.symm ![143, 1, 4]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E239RS1 


noncomputable def E257RS0 : RelationCertificate Table 5 ![![257, 0, 0], ![33, 1, 0]]
  ![-4, 7, 13] ![![5, 0, 0], ![2, 1, 0]] where
    su := ![![1285, 0, 0], ![165, 5, 0]]
    hsu := by decide
    w := ![![-20, 35, 65], ![305, -400, 95]]
    hw := by decide
    g := ![![![-120048, -63661, -606191], ![-60749, 379016, 0]], ![![-24871, -12913, -123310], ![-12528, 77088, 0]]]
    h := ![![![-507, -8204, -2051], ![-45, 65890, 0]], ![![7586, 124741, 31187], ![1643, -1001880, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R257N0 : Ideal.span {5} * I257N0 =  Ideal.span {B.equivFun.symm ![-4, 7, 13]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E257RS0 


noncomputable def E257RS1 : RelationCertificate Table 5 ![![257, 0, 0], ![74, 1, 0]]
  ![22, -1, 1] ![![5, 0, 0], ![2, 1, 0]] where
    su := ![![1285, 0, 0], ![370, 5, 0]]
    hsu := by decide
    w := ![![110, -5, 5], ![65, -10, -5]]
    hw := by decide
    g := ![![![177712, 88851, 852975], ![88858, -533109, 0]], ![![55667, 27832, 267197], ![27839, -166998, 0]]]
    h := ![![![-622, -25175, -2759], ![-235, 88633, 0]], ![![-401, -14901, -1633], ![-25, 52460, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R257N1 : Ideal.span {5} * I257N1 =  Ideal.span {B.equivFun.symm ![22, -1, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E257RS1 


noncomputable def E257RS2 : RelationCertificate Table 5 ![![257, 0, 0], ![-107, 1, 0]]
  ![12, -1, 1] ![![5, 0, 0], ![2, 1, 0]] where
    su := ![![1285, 0, 0], ![-535, 5, 0]]
    hsu := by decide
    w := ![![60, -5, 5], ![45, -20, -5]]
    hw := by decide
    g := ![![![502, 240, 2321], ![252, -1450, 0]], ![![-207, -99, -954], ![-102, 596, 0]]]
    h := ![![![17, 2254, -167], ![141, 5365, 0]], ![![14, 1741, -129], ![111, 4144, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R257N2 : Ideal.span {5} * I257N2 =  Ideal.span {B.equivFun.symm ![12, -1, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E257RS2 
