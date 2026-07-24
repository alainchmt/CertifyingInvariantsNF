import IdealArithmetic.Examples.NF3_1_936091_2.PrimesBelow3_1_936091_2F0
import IdealArithmetic.Examples.NF3_1_936091_2.ClassGroupData3_1_936091_2

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 4 ![![2, 0, 0], ![21, 1, 1]]
  ![1317, 31, 39] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![8, 0, 0], ![84, 4, 4]]
    hsu := by decide
    w := ![![5268, 124, 156], ![3916, 92, 116]]
    hw := by decide
    g := ![![![-77, 72, 194], ![21, -155, 0]], ![![-822, 773, 2052], ![197, -1643, 0]]]
    h := ![![![-3, -16, -12], ![63, 0, 0]], ![![-4, -12, -9], ![47, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {4} * I2N0 =  Ideal.span {B.equivFun.symm ![1317, 31, 39]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 1 ![![2, 0, 0], ![0, 1, 0]]
  ![1, 0, 0] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![2, 0, 0], ![0, 1, 0]]
    hsu := by decide
    w := ![![2, 0, 0], ![0, 1, 0]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {1} * I2N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS1 


noncomputable def E3RS0 : RelationCertificate Table 9 ![![3, 0, 0], ![21, 0, 1]]
  ![1149, 27, 34] ![![9, 0, 0], ![1, 1, 0]] where
    su := ![![27, 0, 0], ![189, 0, 9]]
    hsu := by decide
    w := ![![10341, 243, 306], ![4563, 108, 135]]
    hw := by decide
    g := ![![![-5, 6, 11], ![6, -20, 0]], ![![-28, 44, 76], ![3, -136, 0]]]
    h := ![![![-2, 9, -7], ![55, 0, 0]], ![![1, 4, -3], ![24, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {9} * I3N0 =  Ideal.span {B.equivFun.symm ![1149, 27, 34]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 1 ![![3, 0, 0], ![1, 1, 0]]
  ![1, 0, 0] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![3, 0, 0], ![1, 1, 0]]
    hsu := by decide
    w := ![![3, 0, 0], ![1, 1, 0]]
    hw := by decide
    g := ![![![3, -3, -5], ![0, 3, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![3, -3, -5], ![0, 3, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {1} * I3N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E3RS1 


noncomputable def E5RS0 : RelationCertificate Table 18 ![![5, 0, 0], ![21, 1, 1]]
  ![93, -27, -13] ![![18, 0, 0], ![-8, 1, 0]] where
    su := ![![90, 0, 0], ![378, 18, 18]]
    hsu := by decide
    w := ![![1674, -486, -234], ![-2016, 684, -18]]
    hw := by decide
    g := ![![![6685, 19737, -16313], ![-1866, 58831, 0]], ![![27511, 78885, -65135], ![-7828, 235006, 0]]]
    h := ![![![11383, -27317, -899], ![42218, -9434, 0]], ![![-11933, 28607, 938], ![-44207, 9879, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {18} * I5N0 =  Ideal.span {B.equivFun.symm ![93, -27, -13]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 12 ![![5, 0, 0], ![23, 1, 1]]
  ![51, -3, -43] ![![12, 0, 0], ![4, 1, 0]] where
    su := ![![60, 0, 0], ![276, 12, 12]]
    hsu := by decide
    w := ![![612, -36, -516], ![-4176, 1452, -144]]
    hw := by decide
    g := ![![![192495, -552539, -459043], ![18125, 1102751, 0]], ![![896225, -2542486, -2111910], ![86880, 5074232, 0]]]
    h := ![![![6111, -14775, -167], ![25152, -6090, 0]], ![![-47611, 114980, 1227], ![-195691, 47386, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {12} * I5N1 =  Ideal.span {B.equivFun.symm ![51, -3, -43]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E5RS1 


noncomputable def E7RS0 : RelationCertificate Table 36 ![![7, 0, 0], ![20, -1, 1]]
  ![33, -9, -5] ![![36, 0, 0], ![-8, 1, 0]] where
    su := ![![252, 0, 0], ![720, -36, 36]]
    hsu := by decide
    w := ![![1188, -324, -180], ![-756, 252, 0]]
    hw := by decide
    g := ![![![101623, 314448, -261720], ![-13814, 1884385, 0]], ![![292150, 904036, -752442], ![-39776, 5417585, 0]]]
    h := ![![![-1, -1, -1], ![2, 0, 0]], ![![-3, 1, 0], ![0, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {36} * I7N0 =  Ideal.span {B.equivFun.symm ![33, -9, -5]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 6 ![![7, 0, 0], ![-1, 1, 0]]
  ![8627541, 202989, 255455] ![![6, 0, 0], ![-2, 1, 0]] where
    su := ![![42, 0, 0], ![-6, 6, 0]]
    hsu := by decide
    w := ![![51765246, 1217934, 1532730], ![8395350, 197526, 248580]]
    hw := by decide
    g := ![![![51, -32, 65], ![-16, -35, 0]], ![![466, -135, -40], ![-175, 6, 0]]]
    h := ![![![15507685, -6880144, -36793690], ![-3198260, 51562257, 0]], ![![2515056, -1115831, -5967245], ![-518691, 8362429, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {6} * I7N1 =  Ideal.span {B.equivFun.symm ![8627541, 202989, 255455]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E7RS1 


noncomputable def E13RS0 : RelationCertificate Table 18 ![![13, 0, 0], ![4, 1, 0]]
  ![-174810891, -4112955, -5176019] ![![18, 0, 0], ![-8, 1, 0]] where
    su := ![![234, 0, 0], ![72, 18, 0]]
    hsu := by decide
    w := ![![-3146596038, -74033190, -93168342], ![878759100, 20675466, 26019396]]
    hw := by decide
    g := ![![![-1008394221477, -3386355379636, 2809923725929], ![260044355141, -10115725413063, 0]], ![![-309594716614, -1039670511484, 862695880764], ![79838178971, -3105705170680, 0]]]
    h := ![![![-190716973, 548020299, 455489672], ![-16526736, -1185308351, 0]], ![![53262086, -153047236, -127205936], ![4615477, 331024538, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {18} * I13N0 =  Ideal.span {B.equivFun.symm ![-174810891, -4112955, -5176019]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E13RS0 


noncomputable def E17RS1 : RelationCertificate Table 4 ![![17, 0, 0], ![2, 1, 0]]
  ![4521459, 106381, 133877] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![68, 0, 0], ![8, 4, 0]]
    hsu := by decide
    w := ![![18085836, 425524, 535508], ![13442692, 316280, 398028]]
    hw := by decide
    g := ![![![280, -53, 18], ![-13, -59, 0]], ![![-293, 104, -16], ![29, -10, 0]]]
    h := ![![![291531923, -582534809, -728166169], ![31134, 2475791750, 0]], ![![216687459, -432981700, -541225384], ![23142, 1840186207, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {4} * I17N1 =  Ideal.span {B.equivFun.symm ![4521459, 106381, 133877]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E17RS1 


noncomputable def E29RS0 : RelationCertificate Table 36 ![![29, 0, 0], ![-14, 1, 0]]
  ![-16449, -387, -487] ![![36, 0, 0], ![-8, 1, 0]] where
    su := ![![1044, 0, 0], ![-504, 36, 0]]
    hsu := by decide
    w := ![![-592164, -13932, -17532], ![82692, 1944, 2448]]
    hw := by decide
    g := ![![![-222878, -689718, 574063], ![30373, -4133250, 0]], ![![-52388078, -162121491, 134936000], ![7138436, -971539201, 0]]]
    h := ![![![-22451, -148193, 61642], ![5758, -357621, 0]], ![![3141, 20694, -8608], ![-792, 49940, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N0 : Ideal.span {36} * I29N0 =  Ideal.span {B.equivFun.symm ![-16449, -387, -487]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E29RS0 


noncomputable def E29RS1 : RelationCertificate Table 36 ![![29, 0, 0], ![-2, 1, 0]]
  ![-269679, -6345, -7985] ![![36, 0, 0], ![-8, 1, 0]] where
    su := ![![1044, 0, 0], ![-72, 36, 0]]
    hsu := by decide
    w := ![![-9708444, -228420, -287460], ![1355652, 31896, 40140]]
    hw := by decide
    g := ![![![-178246490, -551606162, 459109575], ![24287955, -3305588947, 0]], ![![18439295, 57062707, -47494095], ![-2512523, 341957478, 0]]]
    h := ![![![269828505, 640704, -677799400], ![-18586761, 3931234923, 0]], ![![-37677875, -89466, 94645455], ![2595400, -548943416, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {36} * I29N1 =  Ideal.span {B.equivFun.symm ![-269679, -6345, -7985]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E29RS1 
