import IdealArithmetic.Examples.NF4_4_54381317_1.PrimesBelow4_4_54381317_1F12
import IdealArithmetic.Examples.NF4_4_54381317_1.ClassGroupData4_4_54381317_1

    set_option linter.all false

    noncomputable section

noncomputable def R661RS1 : IdealMulPrincipalCertificate timesTableO (J0 ^ 1*J1^ 1) ![266, 170, 16, -3] ![![3, 0, 0, 0], ![-131, -67, -4, 1]]
  ![![798, 510, 48, -9], ![390, 27, -39, 3]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

noncomputable def E661RS1 : IdealEqCertificateO timesTableO (Ideal.span {3} * I661N1) (Ideal.span {B.equivFun.symm ![266, 170, 16, -3]} * (J0 ^ 1*J1^ 1)) 
      ![![1983, 0, 0, 0], ![42, 3, 0, 0]] ![![798, 510, 48, -9], ![390, 27, -39, 3]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 3 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R661RS1]  
      rfl
    g := ![![![-605, 1519, 439, -24], ![-3079, -1051, 0, 0]], ![![41, 64, 12, -1], ![-72, -25, 0, 0]]]
    h := ![![![19264, -4175861, -298514, -10], ![-909517, 197225272, 6607, 0]], ![![9386, -2043497, -146082, -5], ![-443144, 96513905, 3306, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R661N1 : Ideal.span {3} * I661N1 =  Ideal.span {B.equivFun.symm ![266, 170, 16, -3]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E661RS1
                    

noncomputable def R661RS2 : IdealMulPrincipalCertificate timesTableO (J0 ^ 1*J1^ 1) ![-29, -11, -1, 0] ![![3, 0, 0, 0], ![-131, -67, -4, 1]]
  ![![-87, -33, -3, 0], ![735, 345, 12, -6]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

noncomputable def E661RS2 : IdealEqCertificateO timesTableO (Ideal.span {3} * I661N2) (Ideal.span {B.equivFun.symm ![-29, -11, -1, 0]} * (J0 ^ 1*J1^ 1)) 
      ![![1983, 0, 0, 0], ![189, 3, 0, 0]] ![![-87, -33, -3, 0], ![735, 345, 12, -6]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 3 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R661RS2]  
      rfl
    g := ![![![26904, -56909, -17221, 845], ![122294, 41636, 0, 0]], ![![7715, -16307, -4934, 243], ![34952, 11896, 0, 0]]]
    h := ![![![-131, 1195, 19, 0], ![1374, -12560, 0, 0]], ![![833, -10205, -225, -1], ![-8736, 107212, 659, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R661N2 : Ideal.span {3} * I661N2 =  Ideal.span {B.equivFun.symm ![-29, -11, -1, 0]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E661RS2
                    

noncomputable def R673RS0 : IdealMulPrincipalCertificate timesTableO (J0 ^ 0*J1^ 2) ![-310, -138, -7, 2] ![![9, 0, 0, 0], ![-2, 1, 0, 0]]
  ![![-2790, -1242, -63, 18], ![1386, 630, 36, -9]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_2
    hmul := by decide

noncomputable def E673RS0 : IdealEqCertificateO timesTableO (Ideal.span {9} * I673N0) (Ideal.span {B.equivFun.symm ![-310, -138, -7, 2]} * (J0 ^ 0*J1^ 2)) 
      ![![6057, 0, 0, 0], ![243, 9, 0, 0]] ![![-2790, -1242, -63, 18], ![1386, 630, 36, -9]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R673RS0]  
      rfl
    g := ![![![259746815218, 11039239631022, -5584587311757, 15396326], ![1168860666737, 50261008672000, -138566962, 0]], ![![10524752936, 447301999191, -226283435518, 623848], ![47361388150, 2036539690400, -5614633, 0]]]
    h := ![![![-68344, -1827, -11931301, -441901], ![1703526, -17559, 297399375, 0]], ![![33916, 877, 6043045, 223817], ![-845382, 9453, -150628842, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R673N0 : Ideal.span {9} * I673N0 =  Ideal.span {B.equivFun.symm ![-310, -138, -7, 2]} * (J0 ^ 0*J1^ 2) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E673RS0
                    

noncomputable def R673RS1 : IdealMulPrincipalCertificate timesTableO (J0 ^ 2*J1^ 0) ![626, 331, 21, -5] ![![9, 0, 0, 0], ![-4, 1, 0, 0]]
  ![![5634, 2979, 189, -45], ![-4419, -2358, -153, 36]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_2J1_0
    hmul := by decide

noncomputable def E673RS1 : IdealEqCertificateO timesTableO (Ideal.span {9} * I673N1) (Ideal.span {B.equivFun.symm ![626, 331, 21, -5]} * (J0 ^ 2*J1^ 0)) 
      ![![6057, 0, 0, 0], ![279, 9, 0, 0]] ![![5634, 2979, 189, -45], ![-4419, -2358, -153, 36]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R673RS1]  
      rfl
    g := ![![![-33342004956767, -808543620209313, 204219913073452, -33177814], ![-75019511153576, -1837978023259765, 298600302, 0]], ![![-1576410968161, -38227965978232, 9655523454663, -1568648], ![-3546924678398, -86899654620639, 14117831, 0]]]
    h := ![![![8545, -663938, -21488, -2], ![-185489, 14419874, 1341, 0]], ![![-6793, 520680, 16834, 1], ![147458, -11308560, -669, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R673N1 : Ideal.span {9} * I673N1 =  Ideal.span {B.equivFun.symm ![626, 331, 21, -5]} * (J0 ^ 2*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E673RS1
                    

noncomputable def R673RS2 : IdealMulPrincipalCertificate timesTableO (J0 ^ 1*J1^ 0) ![-139, -65, -3, 1] ![![3, 0, 0, 0], ![-1, 1, 0, 0]]
  ![![-417, -195, -9, 3], ![522, 258, 18, -3]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

noncomputable def E673RS2 : IdealEqCertificateO timesTableO (Ideal.span {3} * I673N2) (Ideal.span {B.equivFun.symm ![-139, -65, -3, 1]} * (J0 ^ 1*J1^ 0)) 
      ![![2019, 0, 0, 0], ![111, 3, 0, 0]] ![![-417, -195, -9, 3], ![522, 258, 18, -3]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 3 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R673RS2]  
      rfl
    g := ![![![317582, 3197273, -3518623, 20], ![959897, 10555608, 0, 0]], ![![17687, 177939, -195815, 1], ![53420, 587432, 0, 0]]]
    h := ![![![-12399, -37, -3903603, -105503], ![225524, -5424, 71003520, 0]], ![![15438, -29, 5054447, 136607], ![-280800, 8119, -91936512, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R673N2 : Ideal.span {3} * I673N2 =  Ideal.span {B.equivFun.symm ![-139, -65, -3, 1]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E673RS2
                    

noncomputable def R673RS3 : IdealMulPrincipalCertificate timesTableO (J0 ^ 0*J1^ 1) ![107, 63, 5, -1] ![![3, 0, 0, 0], ![1, 1, 0, 0]]
  ![![321, 189, 15, -3], ![-276, -162, -12, 3]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

noncomputable def E673RS3 : IdealEqCertificateO timesTableO (Ideal.span {3} * I673N3) (Ideal.span {B.equivFun.symm ![107, 63, 5, -1]} * (J0 ^ 0*J1^ 1)) 
      ![![2019, 0, 0, 0], ![-288, 3, 0, 0]] ![![321, 189, 15, -3], ![-276, -162, -12, 3]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 3 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R673RS3]  
      rfl
    g := ![![![-2395, -717, 64, 16], ![-1036, -343, 0, 0]], ![![69, 2902, 3066, -5], ![993, -9184, 8, 0]]]
    h := ![![![61739, -189488, 2063, -1], ![432815, -1323882, 672, 0]], ![![-52796, 163187, -1694, 0], ![-370121, 1140154, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R673N3 : Ideal.span {3} * I673N3 =  Ideal.span {B.equivFun.symm ![107, 63, 5, -1]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E673RS3
                    

noncomputable def R683RS1 : IdealMulPrincipalCertificate timesTableO (J0 ^ 0*J1^ 1) ![89, 60, 5, -1] ![![3, 0, 0, 0], ![1, 1, 0, 0]]
  ![![267, 180, 15, -3], ![-294, -183, -15, 3]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

noncomputable def E683RS1 : IdealEqCertificateO timesTableO (Ideal.span {3} * I683N1) (Ideal.span {B.equivFun.symm ![89, 60, 5, -1]} * (J0 ^ 0*J1^ 1)) 
      ![![2049, 0, 0, 0], ![27, 3, 0, 0]] ![![267, 180, 15, -3], ![-294, -183, -15, 3]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 3 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R683RS1]  
      rfl
    g := ![![![-1055681903, 10556818242, 11611496218, -1003847], ![3167045448, -34837500184, 3011540, 0]], ![![-19390075, 193900734, 213272370, -18438], ![58170221, -639872424, 55314, 0]]]
    h := ![![![154, -6715, -757, -1], ![-11677, 510898, 682, 0]], ![![-199, 7376, 822, 0], ![15091, -561440, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R683N1 : Ideal.span {3} * I683N1 =  Ideal.span {B.equivFun.symm ![89, 60, 5, -1]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E683RS1
                    

noncomputable def R683RS2 : IdealMulPrincipalCertificate timesTableO (J0 ^ 1*J1^ 0) ![-166, -74, -3, 1] ![![3, 0, 0, 0], ![-1, 1, 0, 0]]
  ![![-498, -222, -9, 3], ![549, 240, 9, -3]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

noncomputable def E683RS2 : IdealEqCertificateO timesTableO (Ideal.span {3} * I683N2) (Ideal.span {B.equivFun.symm ![-166, -74, -3, 1]} * (J0 ^ 1*J1^ 0)) 
      ![![2049, 0, 0, 0], ![-333, 3, 0, 0]] ![![-498, -222, -9, 3], ![549, 240, 9, -3]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 3 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R683RS2]  
      rfl
    g := ![![![-1497, -617, -357, 12], ![295, 933, 0, 0]], ![![250, 104, 58, -2], ![-48, -151, 0, 0]]]
    h := ![![![-5168, 1299874, -11932, 2], ![-31798, 7998038, -1365, 0]], ![![5946, -1432859, 13241, -3], ![36585, -8816272, 2048, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R683N2 : Ideal.span {3} * I683N2 =  Ideal.span {B.equivFun.symm ![-166, -74, -3, 1]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E683RS2
                    

noncomputable def R691RS1 : IdealMulPrincipalCertificate timesTableO (J0 ^ 2*J1^ 1) ![-1057, -611, -48, 10] ![![9, 0, 0, 0], ![-114, -104, -12, 2]]
  ![![-9513, -5499, -432, 90], ![12492, 10890, 1728, -252]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_2J1_1
    hmul := by decide

noncomputable def E691RS1 : IdealEqCertificateO timesTableO (Ideal.span {9} * I691N1) (Ideal.span {B.equivFun.symm ![-1057, -611, -48, 10]} * (J0 ^ 2*J1^ 1)) 
      ![![6219, 0, 0, 0], ![1962, 9, 0, 0]] ![![-9513, -5499, -432, 90], ![12492, 10890, 1728, -252]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R691RS1]  
      rfl
    g := ![![![-190347861047982, 192304960417824, 40538921776718, -5116978079775], ![133693250948984, 22133369911636, -1382, 0]], ![![-60327319946875, 60947587278566, 12848079778060, -1621733872293], ![42371663544512, 7014772221822, -438, 0]]]
    h := ![![![-100939, 9388191, 46770, 17], ![319944, -29759452, -11737, 0]], ![![131792, -12310096, -61694, -24], ![-417738, 39021538, 16556, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R691N1 : Ideal.span {9} * I691N1 =  Ideal.span {B.equivFun.symm ![-1057, -611, -48, 10]} * (J0 ^ 2*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E691RS1
                    

noncomputable def R691RS2 : IdealMulPrincipalCertificate timesTableO (J0 ^ 1*J1^ 2) ![3625, 1647, 79, -23] ![![9, 0, 0, 0], ![-564, -280, -15, 4]]
  ![![32625, 14823, 711, -207], ![-109584, -48717, -2259, 675]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_2
    hmul := by decide

noncomputable def E691RS2 : IdealEqCertificateO timesTableO (Ideal.span {9} * I691N2) (Ideal.span {B.equivFun.symm ![3625, 1647, 79, -23]} * (J0 ^ 1*J1^ 2)) 
      ![![6219, 0, 0, 0], ![-378, 9, 0, 0]] ![![32625, 14823, 711, -207], ![-109584, -48717, -2259, 675]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R691RS2]  
      rfl
    g := ![![![-12268232545604, 34470591295630, -9125717358029, -1505269896375], ![-289068636237596, -106347452182324, 421, 0]], ![![670237857449, -1883196715647, 498556024515, 82235877561], ![15792392470313, 5809972070785, -23, 0]]]
    h := ![![![85117, -20318318, 485526, -43], ![1400291, -334251407, 29690, 0]], ![![-285770, 68248740, -1630768, 142], ![-4701307, 1122742463, -98047, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R691N2 : Ideal.span {9} * I691N2 =  Ideal.span {B.equivFun.symm ![3625, 1647, 79, -23]} * (J0 ^ 1*J1^ 2) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E691RS2
                    
