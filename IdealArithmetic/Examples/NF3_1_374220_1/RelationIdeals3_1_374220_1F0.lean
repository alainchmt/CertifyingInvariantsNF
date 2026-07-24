import IdealArithmetic.Examples.NF3_1_374220_1.PrimesBelow3_1_374220_1F0
import IdealArithmetic.Examples.NF3_1_374220_1.ClassGroupData3_1_374220_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 125 ![![2, 0, 0], ![0, 1, 0]]
  ![4, 1, 0] ![![125, 0, 0], ![34, -4, 1]] where
    su := ![![250, 0, 0], ![0, 125, 0]]
    hsu := by decide
    w := ![![500, 125, 0], ![250, 0, 0]]
    hw := by decide
    g := ![![![0, 0, 0], ![1, 0, 0]], ![![-33, 4, -1], ![123, 0, 0]]]
    h := ![![![2, 0, 0], ![1, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {125} * I2N0 =  Ideal.span {B.equivFun.symm ![4, 1, 0]} * (J0 ^ 6) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6 E2RS0 


noncomputable def E3RS0 : RelationCertificate Table 125 ![![3, 0, 0], ![0, 1, 0]]
  ![-45, 16, -1] ![![125, 0, 0], ![34, -4, 1]] where
    su := ![![375, 0, 0], ![0, 125, 0]]
    hsu := by decide
    w := ![![-5625, 2000, -125], ![750, 250, -125]]
    hw := by decide
    g := ![![![29, 10, 1], ![104, 0, 0]], ![![62, 9, 2], ![28, 0, 0]]]
    h := ![![![-15, 4, 0], ![4, -1, 0]], ![![2, 0, 0], ![2, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {125} * I3N0 =  Ideal.span {B.equivFun.symm ![-45, 16, -1]} * (J0 ^ 6) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6 E3RS0 


noncomputable def E5RS0 : RelationCertificate Table 1 ![![5, 0, 0], ![-2, 1, 0]]
  ![1, 0, 0] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![5, 0, 0], ![-2, 1, 0]]
    hsu := by decide
    w := ![![5, 0, 0], ![-2, 1, 0]]
    hw := by decide
    g := ![![![11, -5, 0], ![25, 0, 0]], ![![-2, 3, -1], ![-4, 5, 0]]]
    h := ![![![11, -5, 0], ![25, 0, 0]], ![![-2, 3, -1], ![-4, 5, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {1} * I5N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 625 ![![5, 0, 0], ![-1, 1, 0]]
  ![-767, 123, 24] ![![625, 0, 0], ![159, 121, 1]] where
    su := ![![3125, 0, 0], ![-625, 625, 0]]
    hsu := by decide
    w := ![![-479375, 76875, 15000], ![223125, -125000, 17500]]
    hw := by decide
    g := ![![![10364, 13028, 12104], ![5797, -62496, 0]], ![![164, -25, 7], ![269, 0, 0]]]
    h := ![![![-340, 217, -1], ![-933, 29, 0]], ![![160, -129, 6], ![443, -2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {625} * I5N1 =  Ideal.span {B.equivFun.symm ![-767, 123, 24]} * (J0 ^ 7) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7 E5RS1 


noncomputable def E7RS0 : RelationCertificate Table 625 ![![7, 0, 0], ![1, 1, 0]]
  ![1315, 153, 42] ![![625, 0, 0], ![-91, 246, 1]] where
    su := ![![4375, 0, 0], ![625, 625, 0]]
    hsu := by decide
    w := ![![821875, 95625, 26250], ![1075625, 125625, 34375]]
    hw := by decide
    g := ![![![83, -219, -1], ![556, 0, 0]], ![![86, -236, -1], ![601, 0, 0]]]
    h := ![![![180, 180, 172], ![55, -1162, 0]], ![![236, 236, 225], ![69, -1520, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {625} * I7N0 =  Ideal.span {B.equivFun.symm ![1315, 153, 42]} * (J0 ^ 8) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 5 ![![7, 0, 0], ![-2, 1, 0]]
  ![4223, 492, 135] ![![5, 0, 0], ![14, 1, 1]] where
    su := ![![35, 0, 0], ![-10, 5, 0]]
    hsu := by decide
    w := ![![21115, 2460, 675], ![130600, 15215, 4175]]
    hw := by decide
    g := ![![![-1, -15, 0], ![9, 0, 0]], ![![0, 1, -4], ![8, 0, 0]]]
    h := ![![![47377, -24750, 736], ![163708, -5017, 0]], ![![293032, -153087, 4555], ![1012552, -31050, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {5} * I7N1 =  Ideal.span {B.equivFun.symm ![4223, 492, 135]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E7RS1 


noncomputable def E11RS0 : RelationCertificate Table 25 ![![11, 0, 0], ![-4, 1, 0]]
  ![4567, 532, 146] ![![25, 0, 0], ![24, 1, 1]] where
    su := ![![275, 0, 0], ![-100, 25, 0]]
    hsu := by decide
    w := ![![114175, 13300, 3650], ![186900, 21775, 5975]]
    hw := by decide
    g := ![![![41, 6, -2], ![58, -22, 0]], ![![-28, -2, 1], ![-23, 10, 0]]]
    h := ![![![7585, -1891, 50], ![19717, -404, 0]], ![![12412, -3095, 82], ![32264, -663, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {25} * I11N0 =  Ideal.span {B.equivFun.symm ![4567, 532, 146]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 25 ![![11, 0, 0], ![-3, 1, 0]]
  ![-41, 4, 2] ![![25, 0, 0], ![24, 1, 1]] where
    su := ![![275, 0, 0], ![-75, 25, 0]]
    hsu := by decide
    w := ![![-1025, 100, 50], ![-300, 175, -25]]
    hw := by decide
    g := ![![![-67, -1, 1], ![-19, 28, 0]], ![![-9, 0, -1], ![31, -4, 0]]]
    h := ![![![-61, 23, -1], ![-210, 13, 0]], ![![-18, 9, -1], ![-62, 10, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {25} * I11N1 =  Ideal.span {B.equivFun.symm ![-41, 4, 2]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E11RS1 


noncomputable def E13RS0 : RelationCertificate Table 625 ![![13, 0, 0], ![14, -3, 1]]
  ![317, 37, -34] ![![625, 0, 0], ![159, 121, 1]] where
    su := ![![8125, 0, 0], ![8750, -1875, 625]]
    hsu := by decide
    w := ![![198125, 23125, -21250], ![-414375, 113750, 0]]
    hw := by decide
    g := ![![![236117, 306601, 282941], ![120526, -1462464, 0]], ![![255868, 332205, 306520], ![130294, -1584336, 0]]]
    h := ![![![5, 7, -4], ![18, 0, 0]], ![![-23, 8, 2], ![-26, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {625} * I13N0 =  Ideal.span {B.equivFun.symm ![317, 37, -34]} * (J0 ^ 7) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 5 ![![13, 0, 0], ![3, 1, 0]]
  ![-7, 2, 0] ![![5, 0, 0], ![14, 1, 1]] where
    su := ![![65, 0, 0], ![15, 5, 0]]
    hsu := by decide
    w := ![![-35, 10, 0], ![130, -15, -5]]
    hw := by decide
    g := ![![![-1, 1, -1], ![9, 0, 0]], ![![-7, 0, -1], ![7, 0, 0]]]
    h := ![![![-70, -26, -1], ![301, 13, 0]], ![![254, 87, 1], ![-1092, -14, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {5} * I13N1 =  Ideal.span {B.equivFun.symm ![-7, 2, 0]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E13RS1 


noncomputable def E19RS0 : RelationCertificate Table 125 ![![19, 0, 0], ![0, 1, 0]]
  ![2033, 237, 65] ![![125, 0, 0], ![34, -4, 1]] where
    su := ![![2375, 0, 0], ![0, 125, 0]]
    hsu := by decide
    w := ![![254125, 29625, 8125], ![66500, 7750, 2125]]
    hw := by decide
    g := ![![![-23, 1, 0], ![74, 0, 0]], ![![-28, 3, -1], ![116, 0, 0]]]
    h := ![![![107, 12, 0], ![9, 65, 0]], ![![28, 3, 0], ![5, 17, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N0 : Ideal.span {125} * I19N0 =  Ideal.span {B.equivFun.symm ![2033, 237, 65]} * (J0 ^ 6) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6 E19RS0 


noncomputable def E19RS1 : RelationCertificate Table 5 ![![19, 0, 0], ![1, 1, 0]]
  ![187, 22, 6] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![95, 0, 0], ![5, 5, 0]]
    hsu := by decide
    w := ![![935, 110, 30], ![310, 35, 10]]
    hw := by decide
    g := ![![![-3, -16, 8], ![2, -38, 0]], ![![3, -1, 0], ![2, 0, 0]]]
    h := ![![![18, 9, 0], ![-155, 6, 0]], ![![6, 3, 0], ![-52, 2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {5} * I19N1 =  Ideal.span {B.equivFun.symm ![187, 22, 6]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E19RS1 


noncomputable def E19RS2 : RelationCertificate Table 5 ![![19, 0, 0], ![-1, 1, 0]]
  ![-1, 1, 0] ![![5, 0, 0], ![14, 1, 1]] where
    su := ![![95, 0, 0], ![-5, 5, 0]]
    hsu := by decide
    w := ![![-5, 5, 0], ![100, -5, 0]]
    hw := by decide
    g := ![![![-13, -1, -1], ![6, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    h := ![![![0, 0, 0], ![1, 0, 0]], ![![4, -3, 0], ![56, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N2 : Ideal.span {5} * I19N2 =  Ideal.span {B.equivFun.symm ![-1, 1, 0]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E19RS2 


noncomputable def E31RS1 : RelationCertificate Table 5 ![![31, 0, 0], ![11, 1, 0]]
  ![17, -1, -1] ![![5, 0, 0], ![14, 1, 1]] where
    su := ![![155, 0, 0], ![55, 5, 0]]
    hsu := by decide
    w := ![![85, -5, -5], ![10, -75, 20]]
    hw := by decide
    g := ![![![13, 11, -8], ![76, 0, 0]], ![![3, 5, -4], ![37, 0, 0]]]
    h := ![![![536, 49, 0], ![-1509, -1, 0]], ![![32, 1, 0], ![-90, 4, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {5} * I31N1 =  Ideal.span {B.equivFun.symm ![17, -1, -1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E31RS1 
