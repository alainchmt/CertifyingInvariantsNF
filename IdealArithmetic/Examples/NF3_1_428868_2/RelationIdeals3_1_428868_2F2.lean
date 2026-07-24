import IdealArithmetic.Examples.NF3_1_428868_2.PrimesBelow3_1_428868_2F2
import IdealArithmetic.Examples.NF3_1_428868_2.ClassGroupData3_1_428868_2

set_option linter.all false

noncomputable section


noncomputable def E83RS1 : RelationCertificate Table 50 ![![83, 0, 0], ![28, 1, 0]]
  ![-2173, 656, 97] ![![50, 0, 0], ![40, 1, 1]] where
    su := ![![4150, 0, 0], ![1400, 50, 0]]
    hsu := by decide
    w := ![![-108650, 32800, 4850], ![-24600, 8900, -450]]
    hw := by decide
    g := ![![![-44447, -7444, -374], ![-35671, 30030, 0]], ![![-36577567, -7003120, -44690], ![-29403006, 31628443, 0]]]
    h := ![![![73293, 2595, -1], ![-217339, 90, 0]], ![![16900, 593, -1], ![-50114, 37, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {50} * I83N1 =  Ideal.span {B.equivFun.symm ![-2173, 656, 97]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E83RS1 


noncomputable def E89RS1 : RelationCertificate Table 2 ![![89, 0, 0], ![-26, 1, 0]]
  ![155728, 9291, 4760] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![178, 0, 0], ![-52, 2, 0]]
    hsu := by decide
    w := ![![311456, 18582, 9520], ![607928, 36270, 18582]]
    hw := by decide
    g := ![![![-23, -47, 81], ![-33, 0, 0]], ![![83, -24, -26], ![30, 0, 0]]]
    h := ![![![3601708, -141412, 298], ![12322934, -10881, 0]], ![![7030128, -276037, 583], ![24052978, -21298, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {2} * I89N1 =  Ideal.span {B.equivFun.symm ![155728, 9291, 4760]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E89RS1 


noncomputable def E97RS0 : RelationCertificate Table 2 ![![97, 0, 0], ![3, 1, 0]]
  ![97, 6, 3] ![![2, 0, 0], ![20, 1, 1]] where
    su := ![![194, 0, 0], ![6, 2, 0]]
    hsu := by decide
    w := ![![194, 12, 6], ![2510, 148, 76]]
    hw := by decide
    g := ![![![-9, -2, 1], ![1, 0, 0]], ![![-6, -20, -6], ![15, -3, 0]]]
    h := ![![![457, 150, -1], ![-14744, 50, 0]], ![![5935, 1978, 2], ![-191480, -78, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N0 : Ideal.span {2} * I97N0 =  Ideal.span {B.equivFun.symm ![97, 6, 3]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E97RS0 


noncomputable def E97RS1 : RelationCertificate Table 5 ![![97, 0, 0], ![44, 1, 0]]
  ![281, -112, 16] ![![5, 0, 0], ![0, 1, 0]] where
    su := ![![485, 0, 0], ![220, 5, 0]]
    hsu := by decide
    w := ![![1405, -560, 80], ![1520, -295, -240]]
    hw := by decide
    g := ![![![41353, -72182, -153808], ![-14434, 387680, 0]], ![![19996, -34266, -73048], ![-6853, 184148, 0]]]
    h := ![![![20457, 685, 10], ![-45092, -477, 0]], ![![22200, 740, 10], ![-48934, -509, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {5} * I97N1 =  Ideal.span {B.equivFun.symm ![281, -112, 16]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E97RS1 


noncomputable def E97RS2 : RelationCertificate Table 50 ![![97, 0, 0], ![-47, 1, 0]]
  ![-622, 159, 58] ![![50, 0, 0], ![5, 1, 0]] where
    su := ![![4850, 0, 0], ![-2350, 50, 0]]
    hsu := by decide
    w := ![![-31100, 7950, 2900], ![2400, -1350, 550]]
    hw := by decide
    g := ![![![4288, 3172, 1107], ![501, -24360, 0]], ![![-1953, -1502, -523], ![-191, 11568, 0]]]
    h := ![![![-740, -186361, 8104], ![-1514, -393015, 0]], ![![63, 14514, -631], ![129, 30609, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N2 : Ideal.span {50} * I97N2 =  Ideal.span {B.equivFun.symm ![-622, 159, 58]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E97RS2 


noncomputable def E101RS0 : RelationCertificate Table 2 ![![101, 0, 0], ![27, 1, 0]]
  ![108, -41, 4] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![202, 0, 0], ![54, 2, 0]]
    hsu := by decide
    w := ![![216, -82, 8], ![488, -90, -82]]
    hw := by decide
    g := ![![![50131, -7121, 1861], ![21507, 0, 0]], ![![14842, -2109, 551], ![6369, 0, 0]]]
    h := ![![![0, -1, 0], ![4, 2, 0]], ![![-4, -9, -1], ![24, 30, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N0 : Ideal.span {2} * I101N0 =  Ideal.span {B.equivFun.symm ![108, -41, 4]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E101RS0 


noncomputable def E101RS1 : RelationCertificate Table 25 ![![101, 0, 0], ![-15, 1, 0]]
  ![1675581, 99968, 51216] ![![25, 0, 0], ![5, 1, 0]] where
    su := ![![2525, 0, 0], ![-375, 25, 0]]
    hsu := by decide
    w := ![![41889525, 2499200, 1280400], ![13243425, 790125, 404800]]
    hw := by decide
    g := ![![![-199, 2810, 926], ![80, -11487, 0]], ![![32, -390, -126], ![9, 1575, 0]]]
    h := ![![![129716466, -8654117, 1714], ![873312499, -60949, 0]], ![![41010012, -2736010, 542], ![276098765, -19275, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {25} * I101N1 =  Ideal.span {B.equivFun.symm ![1675581, 99968, 51216]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E101RS1 


noncomputable def E101RS2 : RelationCertificate Table 10 ![![101, 0, 0], ![-12, 1, 0]]
  ![100667, 6006, 3077] ![![10, 0, 0], ![20, 1, 1]] where
    su := ![![1010, 0, 0], ![-120, 10, 0]]
    hsu := by decide
    w := ![![1006670, 60060, 30770], ![2583910, 154160, 78980]]
    hw := by decide
    g := ![![![2586, -1580, -360], ![4989, -1316, 0]], ![![364289172, -218981158, -51548960], ![701525364, -186035779, 0]]]
    h := ![![![11627743, -980136, 2085], ![97858448, -103754, 0]], ![![29845955, -2515814, 5354], ![251181922, -266428, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N2 : Ideal.span {10} * I101N2 =  Ideal.span {B.equivFun.symm ![100667, 6006, 3077]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E101RS2 


noncomputable def E103RS1 : RelationCertificate Table 10 ![![103, 0, 0], ![-32, 1, 0]]
  ![619, 37, 19] ![![10, 0, 0], ![5, 1, 0]] where
    su := ![![1030, 0, 0], ![-320, 10, 0]]
    hsu := by decide
    w := ![![6190, 370, 190], ![4900, 290, 150]]
    hw := by decide
    g := ![![![-13, 87, 29], ![5, -141, 0]], ![![2, -25, -8], ![4, 39, 0]]]
    h := ![![![6397, -212, 1], ![20571, -42, 0]], ![![5062, -140, -1], ![16278, 59, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {10} * I103N1 =  Ideal.span {B.equivFun.symm ![619, 37, 19]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E103RS1 


noncomputable def E107RS1 : RelationCertificate Table 10 ![![107, 0, 0], ![19, 1, 0]]
  ![-12956, -773, -396] ![![10, 0, 0], ![5, 1, 0]] where
    su := ![![1070, 0, 0], ![190, 10, 0]]
    hsu := by decide
    w := ![![-129560, -7730, -3960], ![-102400, -6110, -3130]]
    hw := by decide
    g := ![![![-47, -141, -53], ![-27, 272, 0]], ![![-9, -29, -10], ![-1, 53, 0]]]
    h := ![![![-1849596, -101551, -424], ![10415464, 22486, 0]], ![![-1461852, -80261, -335], ![8231996, 17766, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {10} * I107N1 =  Ideal.span {B.equivFun.symm ![-12956, -773, -396]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E107RS1 


noncomputable def E109RS1 : RelationCertificate Table 5 ![![109, 0, 0], ![-41, 1, 0]]
  ![1408, 84, 43] ![![5, 0, 0], ![0, 1, 0]] where
    su := ![![545, 0, 0], ![-205, 5, 0]]
    hsu := by decide
    w := ![![7040, 420, 215], ![4085, 245, 125]]
    hw := by decide
    g := ![![![26, 101, 225], ![23, -566, 0]], ![![-11, -37, -82], ![-4, 206, 0]]]
    h := ![![![13734, -346, 1], ![36478, -33, 0]], ![![7963, -169, -1], ![21150, 67, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {5} * I109N1 =  Ideal.span {B.equivFun.symm ![1408, 84, 43]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E109RS1 


noncomputable def E113RS1 : RelationCertificate Table 10 ![![113, 0, 0], ![16, 1, 0]]
  ![-97232, -5801, -2972] ![![10, 0, 0], ![5, 1, 0]] where
    su := ![![1130, 0, 0], ![160, 10, 0]]
    hsu := by decide
    w := ![![-972320, -58010, -29720], ![-768500, -45850, -23490]]
    hw := by decide
    g := ![![![401, -9904, -3308], ![-787, 16611, 0]], ![![62, -1378, -459], ![-98, 2303, 0]]]
    h := ![![![-15385456, -982972, -2542], ![108653706, 142137, 0]], ![![-12160306, -776917, -2009], ![85877358, 112334, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {10} * I113N1 =  Ideal.span {B.equivFun.symm ![-97232, -5801, -2972]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E113RS1 


noncomputable def E131RS1 : RelationCertificate Table 50 ![![131, 0, 0], ![-59, 1, 0]]
  ![4353, 259, 133] ![![50, 0, 0], ![5, 1, 0]] where
    su := ![![6550, 0, 0], ![-2950, 50, 0]]
    hsu := by decide
    w := ![![217650, 12950, 6650], ![34400, 2050, 1050]]
    hw := by decide
    g := ![![![-9, 1922, 640], ![61, -16014, 0]], ![![-2, -863, -287], ![29, 7182, 0]]]
    h := ![![![113869, -1985, 3], ![252754, -130, 0]], ![![17998, -271, -1], ![39950, 76, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {50} * I131N1 =  Ideal.span {B.equivFun.symm ![4353, 259, 133]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E131RS1 


noncomputable def E137RS1 : RelationCertificate Table 10 ![![137, 0, 0], ![-47, 1, 0]]
  ![-31, 12, -1] ![![10, 0, 0], ![20, 1, 1]] where
    su := ![![1370, 0, 0], ![-470, 10, 0]]
    hsu := by decide
    w := ![![-310, 120, -10], ![520, -160, -10]]
    hw := by decide
    g := ![![![1716679, -1031922, -242920], ![3305903, -876672, 0]], ![![58339995, -35069291, -8255438], ![112347539, -29793169, 0]]]
    h := ![![![-380, 31, -1], ![-1107, 68, 0]], ![![692, 8, -1], ![2016, 68, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {10} * I137N1 =  Ideal.span {B.equivFun.symm ![-31, 12, -1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E137RS1 
