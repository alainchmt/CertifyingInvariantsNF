import IdealArithmetic.Examples.NF3_1_297332_1.PrimesBelow3_1_297332_1F0
import IdealArithmetic.Examples.NF3_1_297332_1.ClassGroupData3_1_297332_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 2 ![![2, 0, 0], ![-23, -2, 1]]
  ![15, 5, 1] ![![2, 0, 0], ![-22, -2, 1]] where
    su := ![![4, 0, 0], ![-46, -4, 2]]
    hsu := by decide
    w := ![![30, 10, 2], ![132, 42, 8]]
    hw := by decide
    g := ![![![6, -2, 10], ![-48, -7, 0]], ![![-69, 42, -143], ![671, 98, 0]]]
    h := ![![![-37, 252, -8], ![197, 0, -15]], ![![-147, 1059, -34], ![828, 0, -63]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {2} * I2N0 =  Ideal.span {B.equivFun.symm ![15, 5, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 1 ![![2, 0, 0], ![-22, -2, 1]]
  ![1, 0, 0] ![![2, 0, 0], ![-22, -2, 1]] where
    su := ![![2, 0, 0], ![-22, -2, 1]]
    hsu := by decide
    w := ![![2, 0, 0], ![-22, -2, 1]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, -3], ![15, 2, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, -3], ![15, 2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {1} * I2N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS1 


noncomputable def E5RS0 : RelationCertificate Table 25 ![![5, 0, 0], ![-23, -4, 1]]
  ![61, 3, -2] ![![25, 0, 0], ![3, 1, 0]] where
    su := ![![125, 0, 0], ![-575, -100, 25]]
    hsu := by decide
    w := ![![1525, 75, -50], ![-125, 0, 0]]
    hw := by decide
    g := ![![![-3, 98, 66], ![24, -825, 0]], ![![1, -472, -315], ![-14, 3938, 0]]]
    h := ![![![3, -1, 0], ![-2, 0, 0]], ![![22, 4, -1], ![5, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {25} * I5N0 =  Ideal.span {B.equivFun.symm ![61, 3, -2]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 1 ![![5, 0, 0], ![-2, 1, 0]]
  ![1, 0, 0] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![5, 0, 0], ![-2, 1, 0]]
    hsu := by decide
    w := ![![5, 0, 0], ![-2, 1, 0]]
    hw := by decide
    g := ![![![11, -5, 0], ![25, 0, 0]], ![![-2, 3, -2], ![-4, 5, 0]]]
    h := ![![![11, -5, 0], ![25, 0, 0]], ![![-2, 3, -2], ![-4, 5, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {1} * I5N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E5RS1 


noncomputable def E7RS0 : RelationCertificate Table 25 ![![7, 0, 0], ![0, 1, 0]]
  ![-63, -74, 16] ![![25, 0, 0], ![3, 1, 0]] where
    su := ![![175, 0, 0], ![0, 25, 0]]
    hsu := by decide
    w := ![![-1575, -1850, 400], ![2275, 275, -100]]
    hw := by decide
    g := ![![![-71, -766, -500], ![-22, 6190, 0]], ![![-102, -479, -304], ![-30, 3714, 0]]]
    h := ![![![-9, -22, 2], ![80, 1, 0]], ![![13, 2, -2], ![-3, 5, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {25} * I7N0 =  Ideal.span {B.equivFun.symm ![-63, -74, 16]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E7RS0 


noncomputable def E11RS0 : RelationCertificate Table 10 ![![11, 0, 0], ![0, 1, 0]]
  ![1331, 53, -37] ![![10, 0, 0], ![-18, -2, 1]] where
    su := ![![110, 0, 0], ![0, 10, 0]]
    hsu := by decide
    w := ![![13310, 530, -370], ![-4400, -2020, 490]]
    hw := by decide
    g := ![![![-13916017, -1503159, -982991], ![25251177, 3855143, 0]], ![![13917196, 1503728, 983261], ![-25253332, -3855339, 0]]]
    h := ![![![121, 8, -5], ![-35, 9, 0]], ![![-40, -38, 3], ![216, 8, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {10} * I11N0 =  Ideal.span {B.equivFun.symm ![1331, 53, -37]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 4 ![![11, 0, 0], ![2, 1, 0]]
  ![-41, -21, 5] ![![4, 0, 0], ![-22, -2, 1]] where
    su := ![![44, 0, 0], ![8, 4, 0]]
    hsu := by decide
    w := ![![-164, -84, 20], ![-3872, -156, 108]]
    hw := by decide
    g := ![![![33, 47, 33], ![-143, -16, 0]], ![![30, 54, 27], ![-70, -5, 0]]]
    h := ![![![-245, -128, -5], ![1327, 30, 0]], ![![-5648, -2891, -105], ![30580, 591, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {4} * I11N1 =  Ideal.span {B.equivFun.symm ![-41, -21, 5]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E11RS1 


noncomputable def E11RS2 : RelationCertificate Table 25 ![![11, 0, 0], ![-2, 1, 0]]
  ![-53, -19, -4] ![![25, 0, 0], ![3, 1, 0]] where
    su := ![![275, 0, 0], ![-50, 25, 0]]
    hsu := by decide
    w := ![![-1325, -475, -100], ![-775, -250, -50]]
    hw := by decide
    g := ![![![-2, -238, -158], ![13, 1976, 0]], ![![0, 21, 14], ![10, -176, 0]]]
    h := ![![![-2987, 1531, -42], ![-16402, 229, 0]], ![![-1749, 896, -24], ![-9604, 131, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N2 : Ideal.span {25} * I11N2 =  Ideal.span {B.equivFun.symm ![-53, -19, -4]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E11RS2 


noncomputable def E13RS1 : RelationCertificate Table 50 ![![13, 0, 0], ![-5, 1, 0]]
  ![269, 87, 17] ![![50, 0, 0], ![2, -2, 1]] where
    su := ![![650, 0, 0], ![-250, 50, 0]]
    hsu := by decide
    w := ![![13450, 4350, 850], ![8700, 2800, 550]]
    hw := by decide
    g := ![![![551821861, 133396345, -14678989], ![16443479, -179376495, 0]], ![![-254686663, -61567458, 6774908], ![-7589255, 82789038, 0]]]
    h := ![![![82758, -18225, 675], ![215117, -4379, 0]], ![![53538, -11791, 437], ![139164, -2835, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {50} * I13N1 =  Ideal.span {B.equivFun.symm ![269, 87, 17]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E13RS1 


noncomputable def E13RS2 : RelationCertificate Table 20 ![![13, 0, 0], ![-1, 1, 0]]
  ![79, 7, -3] ![![20, 0, 0], ![-18, -2, 1]] where
    su := ![![260, 0, 0], ![-20, 20, 0]]
    hsu := by decide
    w := ![![1580, 140, -60], ![580, -60, 0]]
    hw := by decide
    g := ![![![-279566, -30696, 480], ![254715, 66079, 0]], ![![23162, 2543, -40], ![-21097, -5474, 0]]]
    h := ![![![14, -7, -1], ![103, 5, 0]], ![![6, -4, 0], ![49, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N2 : Ideal.span {20} * I13N2 =  Ideal.span {B.equivFun.symm ![79, 7, -3]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E13RS2 


noncomputable def E19RS1 : RelationCertificate Table 2 ![![19, 0, 0], ![-9, 1, 0]]
  ![141, 1, -3] ![![2, 0, 0], ![-22, -2, 1]] where
    su := ![![38, 0, 0], ![-18, 2, 0]]
    hsu := by decide
    w := ![![282, 2, -6], ![-2024, -290, 98]]
    hw := by decide
    g := ![![![1679, -1072, 3252], ![-15559, -2250, 0]], ![![-705, 418, -1433], ![6763, 975, 0]]]
    h := ![![![2607, -330, 9], ![5488, -87, 0]], ![![-18580, 2409, -77], ![-39112, 756, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {2} * I19N1 =  Ideal.span {B.equivFun.symm ![141, 1, -3]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E19RS1 


noncomputable def E23RS0 : RelationCertificate Table 2 ![![23, 0, 0], ![4, 1, 0]]
  ![107, 35, 7] ![![2, 0, 0], ![-22, -2, 1]] where
    su := ![![46, 0, 0], ![8, 2, 0]]
    hsu := by decide
    w := ![![214, 70, 14], ![880, 290, 58]]
    hw := by decide
    g := ![![![1349, -790, 2670], ![-12627, -1820, 0]], ![![336, -196, 667], ![-3154, -455, 0]]]
    h := ![![![101, 23, -1], ![-554, 15, 0]], ![![432, 109, 1], ![-2374, 3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N0 : Ideal.span {2} * I23N0 =  Ideal.span {B.equivFun.symm ![107, 35, 7]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E23RS0 


noncomputable def E23RS1 : RelationCertificate Table 5 ![![23, 0, 0], ![7, 1, 0]]
  ![1719, 562, 112] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![115, 0, 0], ![35, 5, 0]]
    hsu := by decide
    w := ![![8595, 2810, 560], ![13810, 4515, 900]]
    hw := by decide
    g := ![![![-251, -1572, 1612], ![-214, -4018, 0]], ![![-123, -1557, 1608], ![-262, -4018, 0]]]
    h := ![![![4069, 655, 22], ![-13124, -197, 0]], ![![6526, 1046, 34], ![-21048, -301, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {5} * I23N1 =  Ideal.span {B.equivFun.symm ![1719, 562, 112]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E23RS1 


noncomputable def E23RS2 : RelationCertificate Table 100 ![![23, 0, 0], ![-11, 1, 0]]
  ![521, -67, 3] ![![100, 0, 0], ![2, -2, 1]] where
    su := ![![2300, 0, 0], ![-1100, 100, 0]]
    hsu := by decide
    w := ![![52100, -6700, 300], ![-10200, -3500, 900]]
    hw := by decide
    g := ![![![57509, 13838, -1504], ![881, -37362, 0]], ![![-23477, -5648, 613], ![-301, 15249, 0]]]
    h := ![![![613815, -65432, 1751], ![1283384, -20135, 0]], ![![-118374, 12648, -343], ![-247500, 3949, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N2 : Ideal.span {100} * I23N2 =  Ideal.span {B.equivFun.symm ![521, -67, 3]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E23RS2 


noncomputable def E29RS0 : RelationCertificate Table 50 ![![29, 0, 0], ![13, 1, 0]]
  ![647, 81, -29] ![![50, 0, 0], ![2, -2, 1]] where
    su := ![![1450, 0, 0], ![650, 50, 0]]
    hsu := by decide
    w := ![![32350, 4050, -1450], ![22700, 1500, -750]]
    hw := by decide
    g := ![![![-814548737, -196907426, 21667772], ![-24272269, 264779095, 0]], ![![-337054903, -81478997, 8965981], ![-10043713, 109563844, 0]]]
    h := ![![![2014, 182, 3], ![-4443, -58, 0]], ![![1408, 131, 3], ![-3106, -51, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N0 : Ideal.span {50} * I29N0 =  Ideal.span {B.equivFun.symm ![647, 81, -29]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E29RS0 


noncomputable def E29RS1 : RelationCertificate Table 50 ![![29, 0, 0], ![-12, 1, 0]]
  ![57, 11, 1] ![![50, 0, 0], ![2, -2, 1]] where
    su := ![![1450, 0, 0], ![-600, 50, 0]]
    hsu := by decide
    w := ![![2850, 550, 50], ![1500, 300, 50]]
    hw := by decide
    g := ![![![515826305, 124694849, -13721473], ![15370873, -167675695, 0]], ![![-231231068, -55897348, 6150967], ![-6890324, 75164507, 0]]]
    h := ![![![43677, -4041, 67], ![105548, -971, 0]], ![![22998, -2126, 35], ![55576, -507, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {50} * I29N1 =  Ideal.span {B.equivFun.symm ![57, 11, 1]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E29RS1 


noncomputable def E29RS2 : RelationCertificate Table 50 ![![29, 0, 0], ![-1, 1, 0]]
  ![85037, 27801, 5541] ![![50, 0, 0], ![2, -2, 1]] where
    su := ![![1450, 0, 0], ![-50, 50, 0]]
    hsu := by decide
    w := ![![4251850, 1390050, 277050], ![2744800, 897350, 178850]]
    hw := by decide
    g := ![![![245279925, 59293519, -6524681], ![7308997, -79731300, 0]], ![![-4682601, -1131966, 124561], ![-139493, 1522143, 0]]]
    h := ![![![6054, -2167, 199], ![90529, -115, 0]], ![![3908, -1398, 127], ![58436, -53, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N2 : Ideal.span {50} * I29N2 =  Ideal.span {B.equivFun.symm ![85037, 27801, 5541]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E29RS2 
