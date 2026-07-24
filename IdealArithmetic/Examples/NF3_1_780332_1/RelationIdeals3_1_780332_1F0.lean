import IdealArithmetic.Examples.NF3_1_780332_1.PrimesBelow3_1_780332_1F0
import IdealArithmetic.Examples.NF3_1_780332_1.ClassGroupData3_1_780332_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 81 ![![2, 0, 0], ![0, 1, 0]]
  ![-5364, -335, 58] ![![81, 0, 0], ![-63, -4, 1]] where
    su := ![![162, 0, 0], ![0, 81, 0]]
    hsu := by decide
    w := ![![-434484, -27135, 4698], ![21546, 4617, -486]]
    hw := by decide
    g := ![![![-210, -100, -11], ![202, 0, 0]], ![![-23262, -3646, -29], ![18279, 5096, 0]]]
    h := ![![![-2682, -134, 0], ![-67, 58, 0]], ![![133, 22, 0], ![13, -6, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {81} * I2N0 =  Ideal.span {B.equivFun.symm ![-5364, -335, 58]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E2RS0 


noncomputable def E3RS0 : RelationCertificate Table 27 ![![3, 0, 0], ![0, 1, 0]]
  ![45, 13, 1] ![![27, 0, 0], ![654, 35, -8]] where
    su := ![![81, 0, 0], ![0, 27, 0]]
    hsu := by decide
    w := ![![1215, 351, 27], ![-9072, -2943, -243]]
    hw := by decide
    g := ![![![-61, 114, 24], ![221, 32, 0]], ![![-116, 53, 13], ![114, 16, 0]]]
    h := ![![![15, 3, 0], ![4, 1, 0]], ![![-112, -33, 0], ![-10, -9, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {27} * I3N0 =  Ideal.span {B.equivFun.symm ![45, 13, 1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 177147 ![![3, 0, 0], ![1, 1, 0]]
  ![71055, 1822, -566] ![![177147, 0, 0], ![-13545, 167, 1]] where
    su := ![![531441, 0, 0], ![177147, 177147, 0]]
    hsu := by decide
    w := ![![12587180085, 322761834, -100265202], ![-1014166575, -24623433, 7971615]]
    hw := by decide
    g := ![![![1797350744, -43557792079, 542000811], ![-178423599, -574931971544, 0]], ![![1172394083, -28412360311, 353542308], ![-116407864, -375023011088, 0]]]
    h := ![![![38756, 17793, 1926], ![-45213, -6344, 0]], ![![-3124, -1433, -156], ![3647, 513, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {177147} * I3N1 =  Ideal.span {B.equivFun.symm ![71055, 1822, -566]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E3RS1 


noncomputable def E3RS2 : RelationCertificate Table 1 ![![3, 0, 0], ![-1, 1, 0]]
  ![1, 0, 0] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![3, 0, 0], ![-1, 1, 0]]
    hsu := by decide
    w := ![![3, 0, 0], ![-1, 1, 0]]
    hw := by decide
    g := ![![![2, 1, -2], ![3, 6, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![2, 1, -2], ![3, 6, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N2 : Ideal.span {1} * I3N2 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E3RS2 


noncomputable def E5RS0 : RelationCertificate Table 2187 ![![5, 0, 0], ![-83, -6, 1]]
  ![-19539, -2083, 278] ![![2187, 0, 0], ![57717, 4720, -703]] where
    su := ![![10935, 0, 0], ![-181521, -13122, 2187]]
    hsu := by decide
    w := ![![-42731793, -4555521, 607986], ![421559559, 22786353, -4284333]]
    hw := by decide
    g := ![![![-9677, -1279, 129], ![3140, 408, 0]], ![![-45019, 4599, 366], ![-45176, -6898, 0]]]
    h := ![![![43, -131, 8], ![238, 0, 0]], ![![222, -687, 70], ![-2309, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {2187} * I5N0 =  Ideal.span {B.equivFun.symm ![-19539, -2083, 278]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 6561 ![![5, 0, 0], ![1, 1, 0]]
  ![-819, -272, -23] ![![6561, 0, 0], ![34461, 104, -422]] where
    su := ![![32805, 0, 0], ![6561, 6561, 0]]
    hsu := by decide
    w := ![![-5373459, -1784592, -150903], ![34491177, 9893988, 728271]]
    hw := by decide
    g := ![![![-89878, -168106, -26091], ![-421465, -64184, 0]], ![![-45754, -35970, -5245], ![-84923, -13703, 0]]]
    h := ![![![-152, -152, -114], ![-59, 547, 0]], ![![973, 973, 772], ![392, -3749, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {6561} * I5N1 =  Ideal.span {B.equivFun.symm ![-819, -272, -23]} * (J0 ^ 3*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_2 E5RS1 


noncomputable def E7RS0 : RelationCertificate Table 3 ![![7, 0, 0], ![-3, 1, 0]]
  ![-435, -31, 5] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![21, 0, 0], ![-9, 3, 0]]
    hsu := by decide
    w := ![![-1305, -93, 15], ![3225, 216, -36]]
    hw := by decide
    g := ![![![-161, -62, -5], ![34, 3, 0]], ![![-229, -89, -6], ![48, 1, 0]]]
    h := ![![![-4278, 1583, -60], ![-9837, 425, 0]], ![![10588, -3914, 147], ![24347, -1041, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {3} * I7N0 =  Ideal.span {B.equivFun.symm ![-435, -31, 5]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 3 ![![7, 0, 0], ![-2, 1, 0]]
  ![87, 26, 2] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![21, 0, 0], ![-6, 3, 0]]
    hsu := by decide
    w := ![![261, 78, 6], ![1029, 309, 24]]
    hw := by decide
    g := ![![![-63, -15, 7], ![16, -19, 0]], ![![67, 10, -2], ![-17, 4, 0]]]
    h := ![![![549, -280, 8], ![1878, -54, 0]], ![![2161, -1107, 34], ![7392, -230, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {3} * I7N1 =  Ideal.span {B.equivFun.symm ![87, 26, 2]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E7RS1 


noncomputable def E11RS0 : RelationCertificate Table 177147 ![![11, 0, 0], ![-86, -7, 1]]
  ![700551, 77549, -10189] ![![177147, 0, 0], ![-13545, 167, 1]] where
    su := ![![1948617, 0, 0], ![-15234642, -1240029, 177147]]
    hsu := by decide
    w := ![![124100507997, 13737572703, -1804950783], ![-10395163107, -1140472386, 150397803]]
    hw := by decide
    g := ![![![5808681684, -140770318692, 1751641287], ![-576717077, -1858068397104, 0]], ![![-47086651567, 1141122085428, -14199275667], ![4676139347, 15062002457564, 0]]]
    h := ![![![883, 1938, -196], ![-8033, 0, 0]], ![![-73, -157, 16], ![673, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {177147} * I11N0 =  Ideal.span {B.equivFun.symm ![700551, 77549, -10189]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 81 ![![11, 0, 0], ![-4, 1, 0]]
  ![-873, -260, -20] ![![81, 0, 0], ![-1833, -172, 22]] where
    su := ![![891, 0, 0], ![-324, 81, 0]]
    hsu := by decide
    w := ![![-70713, -21060, -1620], ![327969, 98496, 7614]]
    hw := by decide
    g := ![![![3579567, -19116394, -1910136], ![-40914182, -6132750, 0]], ![![-1234952, 6597063, 659180], ![14119420, 2116400, 0]]]
    h := ![![![-1439, 349, -10], ![-3739, 90, 0]], ![![6679, -1605, 43], ![17355, -379, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {81} * I11N1 =  Ideal.span {B.equivFun.symm ![-873, -260, -20]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E11RS1 


noncomputable def E13RS0 : RelationCertificate Table 243 ![![13, 0, 0], ![-86, -8, 1]]
  ![-295641, -88564, -6850] ![![243, 0, 0], ![-144, -4, 1]] where
    su := ![![3159, 0, 0], ![-20898, -1944, 243]]
    hsu := by decide
    w := ![![-71840763, -21521052, -1664550], ![8442792, 2529144, 195615]]
    hw := by decide
    g := ![![![3963, -216, -29], ![-2123, -2256, 0]], ![![-25458, 1496, 184], ![15121, 15048, 0]]]
    h := ![![![-31, -4700, -791], ![3433, 0, 0]], ![![86, 560, 92], ![-391, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {243} * I13N0 =  Ideal.span {B.equivFun.symm ![-295641, -88564, -6850]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 59049 ![![13, 0, 0], ![-5, 1, 0]]
  ![131049, 39265, 3037] ![![59049, 0, 0], ![-504, 5, 1]] where
    su := ![![767637, 0, 0], ![-295245, 59049, 0]]
    hsu := by decide
    w := ![![7738312401, 2318558985, 179331813], ![-35665596, -10687869, -826686]]
    hw := by decide
    g := ![![![-6604433177, 4497968022, -59184815], ![56802299, 698949467740, 0]], ![![-1152735239, 785073681, -10330096], ![9925385, 121994382680, 0]]]
    h := ![![![48017667923, -10595613800, 198417284], ![124845910390, -2579421655, 0]], ![![-221311208, 48834703, -914498], ![-575409020, 11888460, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {59049} * I13N1 =  Ideal.span {B.equivFun.symm ![131049, 39265, 3037]} * (J0 ^ 4*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_2 E13RS1 


noncomputable def E19RS0 : RelationCertificate Table 19683 ![![19, 0, 0], ![9, 1, 0]]
  ![223461, 11354, -2215] ![![19683, 0, 0], ![-504, 5, 1]] where
    su := ![![373977, 0, 0], ![177147, 19683, 0]]
    hsu := by decide
    w := ![![4398382863, 223480782, -43597845], ![-112468662, -5806485, 1121931]]
    hw := by decide
    g := ![![![6691347867, -4559796009, 60006652], ![-172489013, -236187701224, 0]], ![![3609568907, -2459728385, 32369881], ![-93045618, -127408679152, 0]]]
    h := ![![![12323666034, 2173510097, 89357059], ![-26016603465, -1697786336, 0]], ![![-315155420, -55581387, -2284901], ![665327474, 43413176, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N0 : Ideal.span {19683} * I19N0 =  Ideal.span {B.equivFun.symm ![223461, 11354, -2215]} * (J0 ^ 4*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_1 E19RS0 


noncomputable def E19RS1 : RelationCertificate Table 2187 ![![19, 0, 0], ![-7, 1, 0]]
  ![-657, -2, 4] ![![2187, 0, 0], ![57717, 4720, -703]] where
    su := ![![41553, 0, 0], ![-15309, 2187, 0]]
    hsu := by decide
    w := ![![-1436859, -4374, 8748], ![-26600481, -2270106, 334611]]
    hw := by decide
    g := ![![![-35006, 37873, -473], ![-229381, -33945, 0]], ![![-41701, -16096, 788], ![73426, 10571, 0]]]
    h := ![![![-12795402, 1999187, -24468], ![-34730283, 464896, 0]], ![![-236358596, 36936116, -452956], ![-641543023, 8606317, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {2187} * I19N1 =  Ideal.span {B.equivFun.symm ![-657, -2, 4]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E19RS1 


noncomputable def E19RS2 : RelationCertificate Table 177147 ![![19, 0, 0], ![-2, 1, 0]]
  ![-45, 161, 2] ![![177147, 0, 0], ![-13545, 167, 1]] where
    su := ![![3365793, 0, 0], ![-354294, 177147, 0]]
    hsu := by decide
    w := ![![-7971615, 28520667, 354294], ![885735, -2125764, 0]]
    hw := by decide
    g := ![![![98628754971, -2390219280717, 29742113397], ![-9794421160, -31549199805492, 0]], ![![-5423121291, 131426740630, -1635376744], ![538585259, 1734739793318, 0]]]
    h := ![![![-18134771, 9154515, -43561], ![-172280302, 827661, 0]], ![![1992175, -1005768, 4840], ![18925660, -91960, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N2 : Ideal.span {177147} * I19N2 =  Ideal.span {B.equivFun.symm ![-45, 161, 2]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E19RS2 


noncomputable def E29RS0 : RelationCertificate Table 6561 ![![29, 0, 0], ![1, 1, 0]]
  ![27117, 2570, -361] ![![6561, 0, 0], ![-504, 5, 1]] where
    su := ![![190269, 0, 0], ![6561, 6561, 0]]
    hsu := by decide
    w := ![![177914637, 16861770, -2368521], ![-13240098, -1266273, 177147]]
    hw := by decide
    g := ![![![3081, -2087, 28], ![-145, -36134, 0]], ![![605, -124, 1], ![5413, -2117, 0]]]
    h := ![![![932, 932, 834], ![89, -24547, 0]], ![![-70, -70, -62], ![12, 1825, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N0 : Ideal.span {6561} * I29N0 =  Ideal.span {B.equivFun.symm ![27117, 2570, -361]} * (J0 ^ 4*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_0 E29RS0 


noncomputable def E29RS1 : RelationCertificate Table 6561 ![![29, 0, 0], ![14, 1, 0]]
  ![18747, 5615, 434] ![![6561, 0, 0], ![-504, 5, 1]] where
    su := ![![190269, 0, 0], ![91854, 6561, 0]]
    hsu := by decide
    w := ![![122999067, 36840015, 2847474], ![-5104458, -1528713, -118098]]
    hw := by decide
    g := ![![![-145935703, 99964713, -1317159], ![11289442, 1726118240, 0]], ![![-164177624, 112460302, -1481804], ![12701089, 1941883020, 0]]]
    h := ![![![481730957, 57634466, 1658941], ![-997869929, -48108855, 0]], ![![-19991770, -2391839, -68847], ![41411468, 1996545, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {6561} * I29N1 =  Ideal.span {B.equivFun.symm ![18747, 5615, 434]} * (J0 ^ 4*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_0 E29RS1 


noncomputable def E31RS0 : RelationCertificate Table 243 ![![31, 0, 0], ![0, 1, 0]]
  ![279, 29, -4] ![![243, 0, 0], ![-144, -4, 1]] where
    su := ![![7533, 0, 0], ![0, 243, 0]]
    hsu := by decide
    w := ![![67797, 7047, -972], ![-15066, -1944, 243]]
    hw := by decide
    g := ![![![234033, -13597, -1696], ![-138155, -137571, 0]], ![![278460, -16191, -2018], ![-164727, -163775, 0]]]
    h := ![![![9, 0, 0], ![29, -4, 0]], ![![-2, 0, 0], ![-8, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N0 : Ideal.span {243} * I31N0 =  Ideal.span {B.equivFun.symm ![279, 29, -4]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E31RS0 
