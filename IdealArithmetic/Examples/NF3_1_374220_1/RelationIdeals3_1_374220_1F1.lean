import IdealArithmetic.Examples.NF3_1_374220_1.PrimesBelow3_1_374220_1F1
import IdealArithmetic.Examples.NF3_1_374220_1.ClassGroupData3_1_374220_1

set_option linter.all false

noncomputable section


noncomputable def E37RS1 : RelationCertificate Table 5 ![![37, 0, 0], ![-9, 1, 0]]
  ![2377, 277, 76] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![185, 0, 0], ![-45, 5, 0]]
    hsu := by decide
    w := ![![11885, 1385, 380], ![3910, 455, 125]]
    hw := by decide
    g := ![![![-3273, -47111, 24369], ![-8110, -121836, 0]], ![![775, 11062, -5723], ![1906, 28613, 0]]]
    h := ![![![109756, -12828, 74], ![450955, -2662, 0]], ![![36116, -4218, 24], ![148390, -863, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {5} * I37N1 =  Ideal.span {B.equivFun.symm ![2377, 277, 76]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E37RS1 


noncomputable def E41RS1 : RelationCertificate Table 5 ![![41, 0, 0], ![-10, 1, 0]]
  ![107, -33, 1] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![205, 0, 0], ![-50, 5, 0]]
    hsu := by decide
    w := ![![535, -165, 5], ![-100, 155, -35]]
    hw := by decide
    g := ![![![1777, 10113, -5075], ![1314, 25575, 0]], ![![-224, -826, 403], ![-75, -2046, 0]]]
    h := ![![![5517, -572, 2], ![22609, -81, 0]], ![![-1040, 113, -1], ![-4262, 34, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {5} * I41N1 =  Ideal.span {B.equivFun.symm ![107, -33, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E41RS1 


noncomputable def E47RS1 : RelationCertificate Table 625 ![![47, 0, 0], ![5, 1, 0]]
  ![-121, -11, -3] ![![625, 0, 0], ![159, 121, 1]] where
    su := ![![29375, 0, 0], ![3125, 625, 0]]
    hsu := by decide
    w := ![![-75625, -6875, -1875], ![-61875, -10000, -1875]]
    hw := by decide
    g := ![![![-41, -33, -6], ![136, 30, 0]], ![![-74, -57, -2], ![285, 8, 0]]]
    h := ![![![-228, -50, -1], ![2119, 44, 0]], ![![-192, -43, -1], ![1785, 44, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {625} * I47N1 =  Ideal.span {B.equivFun.symm ![-121, -11, -3]} * (J0 ^ 7) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7 E47RS1 


noncomputable def E53RS0 : RelationCertificate Table 125 ![![53, 0, 0], ![7, 1, 0]]
  ![121, 15, 4] ![![125, 0, 0], ![34, -4, 1]] where
    su := ![![6625, 0, 0], ![875, 125, 0]]
    hsu := by decide
    w := ![![15125, 1875, 500], ![4000, 500, 125]]
    hw := by decide
    g := ![![![-11, 1, 0], ![29, 0, 0]], ![![-1, 0, 0], ![4, 0, 0]]]
    h := ![![![86041, 12550, 37], ![-651436, -1957, 0]], ![![22744, 3312, 9], ![-172200, -476, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N0 : Ideal.span {125} * I53N0 =  Ideal.span {B.equivFun.symm ![121, 15, 4]} * (J0 ^ 6) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6 E53RS0 


noncomputable def E53RS1 : RelationCertificate Table 625 ![![53, 0, 0], ![11, 1, 0]]
  ![161, -19, -7] ![![625, 0, 0], ![159, 121, 1]] where
    su := ![![33125, 0, 0], ![6875, 625, 0]]
    hsu := by decide
    w := ![![100625, -11875, -4375], ![-73125, 31250, -3125]]
    hw := by decide
    g := ![![![-47, -31, -24], ![6, 120, 0]], ![![-107, -80, -7], ![372, 32, 0]]]
    h := ![![![864316, 82722, 377], ![-4164417, -19988, 0]], ![![-626254, -59955, -275], ![3017395, 14570, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {625} * I53N1 =  Ideal.span {B.equivFun.symm ![161, -19, -7]} * (J0 ^ 7) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7 E53RS1 


noncomputable def E53RS2 : RelationCertificate Table 125 ![![53, 0, 0], ![-18, 1, 0]]
  ![-113, -13, -4] ![![125, 0, 0], ![-16, 21, 1]] where
    su := ![![6625, 0, 0], ![-2250, 125, 0]]
    hsu := by decide
    w := ![![-14125, -1625, -500], ![-9250, -875, -250]]
    hw := by decide
    g := ![![![-169, 36, -35], ![111, 203, 0]], ![![68, -27, 11], ![52, -68, 0]]]
    h := ![![![-175, 26, -1], ![-509, 49, 0]], ![![-106, 23, -1], ![-308, 51, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N2 : Ideal.span {125} * I53N2 =  Ideal.span {B.equivFun.symm ![-113, -13, -4]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E53RS2 


noncomputable def E61RS0 : RelationCertificate Table 5 ![![61, 0, 0], ![28, 1, 0]]
  ![91, 11, 3] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![305, 0, 0], ![140, 5, 0]]
    hsu := by decide
    w := ![![455, 55, 15], ![160, 15, 5]]
    hw := by decide
    g := ![![![-13, -108, 56], ![-11, -278, 0]], ![![-6, -50, 26], ![-7, -129, 0]]]
    h := ![![![679, 23, 0], ![-1476, 3, 0]], ![![208, 7, 0], ![-452, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N0 : Ideal.span {5} * I61N0 =  Ideal.span {B.equivFun.symm ![91, 11, 3]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E61RS0 


noncomputable def E61RS1 : RelationCertificate Table 25 ![![61, 0, 0], ![-16, 1, 0]]
  ![17, 2, 1] ![![25, 0, 0], ![24, 1, 1]] where
    su := ![![1525, 0, 0], ![-400, 25, 0]]
    hsu := by decide
    w := ![![425, 50, 25], ![750, 125, 25]]
    hw := by decide
    g := ![![![269, 18, -7], ![298, -122, 0]], ![![-98, -6, 1], ![-59, 34, 0]]]
    h := ![![![7749, -500, 1], ![29542, -60, 0]], ![![13654, -885, 2], ![52054, -121, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {25} * I61N1 =  Ideal.span {B.equivFun.symm ![17, 2, 1]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E61RS1 


noncomputable def E61RS2 : RelationCertificate Table 125 ![![61, 0, 0], ![-12, 1, 0]]
  ![-4663, -543, -149] ![![125, 0, 0], ![-16, 21, 1]] where
    su := ![![7625, 0, 0], ![-1500, 125, 0]]
    hsu := by decide
    w := ![![-582875, -67875, -18625], ![-344000, -40125, -11000]]
    hw := by decide
    g := ![![![-9524405, 2626909, -1806474], ![1646074, 10674440, 0]], ![![1768836, -487877, 335487], ![-305568, -1982396, 0]]]
    h := ![![![-7201891, 621845, -1811], ![-36609224, 110322, 0]], ![![-4250392, 367001, -1069], ![-21605930, 65121, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N2 : Ideal.span {125} * I61N2 =  Ideal.span {B.equivFun.symm ![-4663, -543, -149]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E61RS2 


noncomputable def E67RS1 : RelationCertificate Table 125 ![![67, 0, 0], ![9, 1, 0]]
  ![29, -16, 2] ![![125, 0, 0], ![-16, 21, 1]] where
    su := ![![8375, 0, 0], ![1125, 125, 0]]
    hsu := by decide
    w := ![![3625, -2000, 250], ![2500, 625, -375]]
    hw := by decide
    g := ![![![-37313, 10282, -7076], ![6478, 41808, 0]], ![![-4455, 1226, -845], ![783, 4992, 0]]]
    h := ![![![50, 5, 0], ![-369, 2, 0]], ![![32, -5, -1], ![-236, 64, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {125} * I67N1 =  Ideal.span {B.equivFun.symm ![29, -16, 2]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E67RS1 


noncomputable def E71RS1 : RelationCertificate Table 625 ![![71, 0, 0], ![-7, 1, 0]]
  ![65879, 7675, 2106] ![![625, 0, 0], ![-91, 246, 1]] where
    su := ![![44375, 0, 0], ![-4375, 625, 0]]
    hsu := by decide
    w := ![![41174375, 4796875, 1316250], ![53940625, 6284375, 1724375]]
    hw := by decide
    g := ![![![137, -233, -3], ![574, 0, 0]], ![![1, -24, 0], ![66, 0, 0]]]
    h := ![![![295988408, -42680020, 56630], ![3002158727, -4018624, 0]], ![![387760592, -55913106, 74189], ![3932987961, -5264660, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {625} * I71N1 =  Ideal.span {B.equivFun.symm ![65879, 7675, 2106]} * (J0 ^ 8) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8 E71RS1 


noncomputable def E73RS1 : RelationCertificate Table 125 ![![73, 0, 0], ![6, 1, 0]]
  ![5381, 627, 172] ![![125, 0, 0], ![34, -4, 1]] where
    su := ![![9125, 0, 0], ![750, 125, 0]]
    hsu := by decide
    w := ![![672625, 78375, 21500], ![176000, 20500, 5625]]
    hw := by decide
    g := ![![![-3, -7, 0], ![109, 0, 0]], ![![-28, 3, -1], ![116, 0, 0]]]
    h := ![![![3481751, 584792, 753], ![-42360407, -54797, 0]], ![![911032, 153016, 197], ![-11083988, -14336, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {125} * I73N1 =  Ideal.span {B.equivFun.symm ![5381, 627, 172]} * (J0 ^ 6) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6 E73RS1 


noncomputable def E79RS1 : RelationCertificate Table 25 ![![79, 0, 0], ![2, 1, 0]]
  ![583, -47, -31] ![![25, 0, 0], ![24, 1, 1]] where
    su := ![![1975, 0, 0], ![50, 25, 0]]
    hsu := by decide
    w := ![![14575, -1175, -775], ![5100, -2675, 350]]
    hw := by decide
    g := ![![![-3113, -796, -151], ![-2991, -750, 0]], ![![-310, -62, -10], ![-263, -24, 0]]]
    h := ![![![27845, 13927, 4], ![-1099586, -347, 0]], ![![9740, 4869, 1], ![-384628, -65, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {25} * I79N1 =  Ideal.span {B.equivFun.symm ![583, -47, -31]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E79RS1 
