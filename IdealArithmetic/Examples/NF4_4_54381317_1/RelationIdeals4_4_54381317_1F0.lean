import IdealArithmetic.Examples.NF4_4_54381317_1.PrimesBelow4_4_54381317_1F0
import IdealArithmetic.Examples.NF4_4_54381317_1.ClassGroupData4_4_54381317_1

    set_option linter.all false

    noncomputable section

noncomputable def R3RS0 : IdealMulPrincipalCertificate timesTableO (J0 ^ 2*J1^ 2) ![-126, -67, -4, 1] ![![9, 0, 0, 0], ![-128, -67, -4, 1]]
  ![![-1134, -603, -36, 9], ![-1107, -603, -36, 9]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_2J1_2
    hmul := by decide

noncomputable def E3RS0 : IdealEqCertificateO timesTableO (Ideal.span {9} * I3N0) (Ideal.span {B.equivFun.symm ![-126, -67, -4, 1]} * (J0 ^ 2*J1^ 2)) 
      ![![27, 0, 0, 0], ![-1188, -603, -36, 9]] ![![-1134, -603, -36, 9], ![-1107, -603, -36, 9]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R3RS0]  
      rfl
    g := ![![![127, 67, 4, -1], ![10, 0, 0, 0]], ![![25, -66, -22, 0], ![592, 198, 0, 0]]]
    h := ![![![152, -159, -54, 3], ![370, 126, 0, 0]], ![![140, -160, -53, 3], ![361, 123, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {9} * I3N0 =  Ideal.span {B.equivFun.symm ![-126, -67, -4, 1]} * (J0 ^ 2*J1^ 2) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E3RS0
                    

noncomputable def R3RS1 : IdealMulPrincipalCertificate timesTableO (J0 ^ 0*J1^ 1) ![1, 0, 0, 0] ![![3, 0, 0, 0], ![1, 1, 0, 0]]
  ![![3, 0, 0, 0], ![1, 1, 0, 0]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

noncomputable def E3RS1 : IdealEqCertificateO timesTableO (Ideal.span {1} * I3N1) (Ideal.span {B.equivFun.symm ![1, 0, 0, 0]} * (J0 ^ 0*J1^ 1)) 
      ![![3, 0, 0, 0], ![1, 1, 0, 0]] ![![3, 0, 0, 0], ![1, 1, 0, 0]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 1 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R3RS1]  
      rfl
    g := ![![![0, -2, 1, 2], ![3, 3, -6, 0]], ![![0, 0, 1, 1], ![1, 0, -3, 0]]]
    h := ![![![0, -2, 1, 2], ![3, 3, -6, 0]], ![![0, 0, 1, 1], ![1, 0, -3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {1} * I3N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0, 0]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E3RS1
                    

noncomputable def R3RS2 : IdealMulPrincipalCertificate timesTableO (J0 ^ 1*J1^ 0) ![1, 0, 0, 0] ![![3, 0, 0, 0], ![-1, 1, 0, 0]]
  ![![3, 0, 0, 0], ![-1, 1, 0, 0]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

noncomputable def E3RS2 : IdealEqCertificateO timesTableO (Ideal.span {1} * I3N2) (Ideal.span {B.equivFun.symm ![1, 0, 0, 0]} * (J0 ^ 1*J1^ 0)) 
      ![![3, 0, 0, 0], ![-1, 1, 0, 0]] ![![3, 0, 0, 0], ![-1, 1, 0, 0]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 1 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R3RS2]  
      rfl
    g := ![![![2, 1, 0, -2], ![3, 6, 6, 0]], ![![0, 0, 0, 0], ![1, 0, 0, 0]]]
    h := ![![![2, 1, 0, -2], ![3, 6, 6, 0]], ![![0, 0, 0, 0], ![1, 0, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N2 : Ideal.span {1} * I3N2 =  Ideal.span {B.equivFun.symm ![1, 0, 0, 0]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E3RS2
                    

noncomputable def R5RS0 : IdealMulPrincipalCertificate timesTableO (J0 ^ 1*J1^ 1) ![-138, -67, -4, 1] ![![3, 0, 0, 0], ![-131, -67, -4, 1]]
  ![![-414, -201, -12, 3], ![843, 402, 24, -6]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

noncomputable def E5RS0 : IdealEqCertificateO timesTableO (Ideal.span {3} * I5N0) (Ideal.span {B.equivFun.symm ![-138, -67, -4, 1]} * (J0 ^ 1*J1^ 1)) 
      ![![15, 0, 0, 0], ![-399, -201, -12, 3]] ![![-414, -201, -12, 3], ![843, 402, 24, -6]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 3 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R5RS0]  
      rfl
    g := ![![![42, 0, -4, 0], ![37, 12, 0, 0]], ![![-198, 603, 174, -9], ![-1214, -414, 0, 0]]]
    h := ![![![2619, -6322, -1789, 132], ![18256, 6305, 0, 0]], ![![-5138, 13009, 3658, -271], ![-37257, -12870, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {3} * I5N0 =  Ideal.span {B.equivFun.symm ![-138, -67, -4, 1]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E5RS0
                    

noncomputable def R5RS1 : IdealMulPrincipalCertificate timesTableO (J0 ^ 2*J1^ 0) ![-73, -50, -6, 1] ![![9, 0, 0, 0], ![-4, 1, 0, 0]]
  ![![-657, -450, -54, 9], ![675, 459, 54, -9]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_2J1_0
    hmul := by decide

noncomputable def E5RS1 : IdealEqCertificateO timesTableO (Ideal.span {9} * I5N1) (Ideal.span {B.equivFun.symm ![-73, -50, -6, 1]} * (J0 ^ 2*J1^ 0)) 
      ![![45, 0, 0, 0], ![18, 9, 0, 0]] ![![-657, -450, -54, 9], ![675, 459, 54, -9]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R5RS1]  
      rfl
    g := ![![![-615, -14567, 3677, 0], ![-1339, -33092, 1, 0]], ![![5, 15, -4, 0], ![10, 36, 0, 0]]]
    h := ![![![-1939, 2265, 1811, 97], ![4811, -8093, -484, 0]], ![![1983, -2341, -1868, -101], ![-4920, 8338, 504, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {9} * I5N1 =  Ideal.span {B.equivFun.symm ![-73, -50, -6, 1]} * (J0 ^ 2*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E5RS1
                    

noncomputable def R5RS2 : IdealMulPrincipalCertificate timesTableO (J0 ^ 0*J1^ 2) ![620, 285, 14, -4] ![![9, 0, 0, 0], ![-2, 1, 0, 0]]
  ![![5580, 2565, 126, -36], ![-2772, -1278, -63, 18]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_2
    hmul := by decide

noncomputable def E5RS2 : IdealEqCertificateO timesTableO (Ideal.span {9} * I5N2) (Ideal.span {B.equivFun.symm ![620, 285, 14, -4]} * (J0 ^ 0*J1^ 2)) 
      ![![45, 0, 0, 0], ![-9, 9, 0, 0]] ![![5580, 2565, 126, -36], ![-2772, -1278, -63, 18]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R5RS2]  
      rfl
    g := ![![![-2392430, -101678778, 51438757, -627], ![-10765986, -462937524, 5642, 0]], ![![-683565, -29051080, 14696783, -179], ![-3075994, -132267828, 1612, 0]]]
    h := ![![![414, -630, 416, -17], ![1450, -1985, 81, 0]], ![![-204, 312, -207, 8], ![-712, 990, -38, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N2 : Ideal.span {9} * I5N2 =  Ideal.span {B.equivFun.symm ![620, 285, 14, -4]} * (J0 ^ 0*J1^ 2) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E5RS2
                    

noncomputable def R7RS0 : IdealMulPrincipalCertificate timesTableO (J0 ^ 2*J1^ 1) ![-166, -71, -3, 1] ![![9, 0, 0, 0], ![-114, -104, -12, 2]]
  ![![-1494, -639, -27, 9], ![-6354, -2682, -108, 36]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_2J1_1
    hmul := by decide

noncomputable def E7RS0 : IdealEqCertificateO timesTableO (Ideal.span {9} * I7N0) (Ideal.span {B.equivFun.symm ![-166, -71, -3, 1]} * (J0 ^ 2*J1^ 1)) 
      ![![63, 0, 0, 0], ![-1206, -585, -36, 9]] ![![-1494, -639, -27, 9], ![-6354, -2682, -108, 36]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R7RS0]  
      rfl
    g := ![![![1032820254067, -1043439403037, -219962647145, 27764528298], ![-725414467244, -120094803279, 3196, 0]], ![![-26549556414550, 26822531018308, 5654334030815, -713711710806], ![18647419285409, 3087142939439, -82156, 0]]]
    h := ![![![9346, -23706, -7967, 258], ![46741, 16182, 0, 0]], ![![39778, -101236, -34008, 1102], ![199494, 69068, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {9} * I7N0 =  Ideal.span {B.equivFun.symm ![-166, -71, -3, 1]} * (J0 ^ 2*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E7RS0
                    

noncomputable def R7RS1 : IdealMulPrincipalCertificate timesTableO (J0 ^ 1*J1^ 2) ![482, 264, 17, -4] ![![9, 0, 0, 0], ![-564, -280, -15, 4]]
  ![![4338, 2376, 153, -36], ![16551, 9036, 558, -135]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_2
    hmul := by decide

noncomputable def E7RS1 : IdealEqCertificateO timesTableO (Ideal.span {9} * I7N1) (Ideal.span {B.equivFun.symm ![482, 264, 17, -4]} * (J0 ^ 1*J1^ 2)) 
      ![![63, 0, 0, 0], ![-1188, -630, -36, 9]] ![![4338, 2376, 153, -36], ![16551, 9036, 558, -135]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R7RS1]  
      rfl
    g := ![![![500910, -1406633, 372415, 61426], ![11796768, 4339960, -12, 0]], ![![-12808981, 35989885, -9527592, -1571547], ![-301804828, -111032212, 307, 0]]]
    h := ![![![5066, -4458, -3541, -265], ![-46461, -16104, 0, 0]], ![![18901, -17148, -13478, -1005], ![-176712, -61244, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {9} * I7N1 =  Ideal.span {B.equivFun.symm ![482, 264, 17, -4]} * (J0 ^ 1*J1^ 2) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E7RS1
                    

noncomputable def R11RS0 : IdealMulPrincipalCertificate timesTableO (J0 ^ 1*J1^ 1) ![-141, -67, -4, 1] ![![3, 0, 0, 0], ![-131, -67, -4, 1]]
  ![![-423, -201, -12, 3], ![1236, 603, 36, -9]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

noncomputable def E11RS0 : IdealEqCertificateO timesTableO (Ideal.span {3} * I11N0) (Ideal.span {B.equivFun.symm ![-141, -67, -4, 1]} * (J0 ^ 1*J1^ 1)) 
      ![![33, 0, 0, 0], ![-390, -201, -12, 3]] ![![-423, -201, -12, 3], ![1236, 603, 36, -9]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 3 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R11RS0]  
      rfl
    g := ![![![-66, 469, 126, -7], ![-862, -294, 0, 0]], ![![-6273, 13333, 4030, -199], ![-28510, -9702, 0, 0]]]
    h := ![![![63, -1036, -280, 12], ![7525, 2552, 0, 0]], ![![210, 3222, 828, -38], ![-21893, -7436, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {3} * I11N0 =  Ideal.span {B.equivFun.symm ![-141, -67, -4, 1]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E11RS0
                    

noncomputable def R11RS1 : IdealMulPrincipalCertificate timesTableO (J0 ^ 2*J1^ 2) ![-144, -67, -4, 1] ![![9, 0, 0, 0], ![-128, -67, -4, 1]]
  ![![-1296, -603, -36, 9], ![1197, 603, 36, -9]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_2J1_2
    hmul := by decide

noncomputable def E11RS1 : IdealEqCertificateO timesTableO (Ideal.span {9} * I11N1) (Ideal.span {B.equivFun.symm ![-144, -67, -4, 1]} * (J0 ^ 2*J1^ 2)) 
      ![![99, 0, 0, 0], ![-1197, -603, -36, 9]] ![![-1296, -603, -36, 9], ![1197, 603, 36, -9]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R11RS1]  
      rfl
    g := ![![![3, -12, -4, 0], ![107, 36, 0, 0]], ![![98, 157, 34, -1], ![-802, -270, 0, 0]]]
    h := ![![![48, -145, -40, 3], ![892, 308, 0, 0]], ![![15, 153, 36, -3], ![-760, -264, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {9} * I11N1 =  Ideal.span {B.equivFun.symm ![-144, -67, -4, 1]} * (J0 ^ 2*J1^ 2) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E11RS1
                    

noncomputable def R13RS0 : IdealMulPrincipalCertificate timesTableO (J0 ^ 2*J1^ 1) ![341, 151, 6, -2] ![![9, 0, 0, 0], ![-114, -104, -12, 2]]
  ![![3069, 1359, 54, -18], ![18576, 9378, 612, -144]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_2J1_1
    hmul := by decide

noncomputable def E13RS0 : IdealEqCertificateO timesTableO (Ideal.span {9} * I13N0) (Ideal.span {B.equivFun.symm ![341, 151, 6, -2]} * (J0 ^ 2*J1^ 1)) 
      ![![117, 0, 0, 0], ![-1224, -558, -36, 9]] ![![3069, 1359, 54, -18], ![18576, 9378, 612, -144]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R13RS0]  
      rfl
    g := ![![![-28886953556472529782, 29183960511313256194, 6152136116222016836, -776546199824519301], ![20289120718552946844, 3358932563868509118, -2800, 0]], ![![458580384865061406165, -463295370243917401687, -97665160239342579015, 12327670845762748261], ![-322089789409550451204, -53323054120723412336, 44450, 0]]]
    h := ![![![-87949, 315475, 109338, -2408], ![-616788, -216030, 0, 0]], ![![-527036, 1887906, 654396, -14408], ![-3691676, -1292988, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {9} * I13N0 =  Ideal.span {B.equivFun.symm ![341, 151, 6, -2]} * (J0 ^ 2*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E13RS0
                    

noncomputable def R13RS1 : IdealMulPrincipalCertificate timesTableO (J0 ^ 1*J1^ 2) ![-206, -84, -2, 1] ![![9, 0, 0, 0], ![-564, -280, -15, 4]]
  ![![-1854, -756, -18, 9], ![7029, 3159, 162, -45]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_2
    hmul := by decide

noncomputable def E13RS1 : IdealEqCertificateO timesTableO (Ideal.span {9} * I13N1) (Ideal.span {B.equivFun.symm ![-206, -84, -2, 1]} * (J0 ^ 1*J1^ 2)) 
      ![![117, 0, 0, 0], ![-1206, -630, -36, 9]] ![![-1854, -756, -18, 9], ![7029, 3159, 162, -45]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R13RS1]  
      rfl
    g := ![![![4377, -11457, 3073, 504], ![97135, 35734, 0, 0]], ![![-4300563639, 12083481238, -3198969372, -527663905], ![-101331436948, -37279515469, 1820, 0]]]
    h := ![![![-68654, 2790, 24646, 3154], ![685605, 242202, 0, 0]], ![![259435, -10443, -93066, -11912], ![-2589069, -914640, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {9} * I13N1 =  Ideal.span {B.equivFun.symm ![-206, -84, -2, 1]} * (J0 ^ 1*J1^ 2) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E13RS1
                    

noncomputable def R17RS0 : IdealMulPrincipalCertificate timesTableO (J0 ^ 1*J1^ 1) ![-129, -67, -4, 1] ![![3, 0, 0, 0], ![-131, -67, -4, 1]]
  ![![-387, -201, -12, 3], ![-336, -201, -12, 3]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

noncomputable def E17RS0 : IdealEqCertificateO timesTableO (Ideal.span {3} * I17N0) (Ideal.span {B.equivFun.symm ![-129, -67, -4, 1]} * (J0 ^ 1*J1^ 1)) 
      ![![51, 0, 0, 0], ![-387, -201, -12, 3]] ![![-387, -201, -12, 3], ![-336, -201, -12, 3]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 3 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R17RS0]  
      rfl
    g := ![![![681, -1206, -376, 18], ![2683, 912, 0, 0]], ![![683, -1206, -376, 18], ![2682, 912, 0, 0]]]
    h := ![![![-725, -1347, -290, 13], ![11918, 4046, 0, 0]], ![![-606, -1143, -247, 11], ![10167, 3451, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N0 : Ideal.span {3} * I17N0 =  Ideal.span {B.equivFun.symm ![-129, -67, -4, 1]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E17RS0
                    

noncomputable def R17RS1 : IdealMulPrincipalCertificate timesTableO (J0 ^ 1*J1^ 1) ![31, 16, 2, 0] ![![3, 0, 0, 0], ![-131, -67, -4, 1]]
  ![![93, 48, 6, 0], ![-231, -87, 6, 3]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

noncomputable def E17RS1 : IdealEqCertificateO timesTableO (Ideal.span {3} * I17N1) (Ideal.span {B.equivFun.symm ![31, 16, 2, 0]} * (J0 ^ 1*J1^ 1)) 
      ![![51, 0, 0, 0], ![21, 3, 0, 0]] ![![93, 48, 6, 0], ![-231, -87, 6, 3]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 3 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R17RS1]  
      rfl
    g := ![![![89, 36, 1, 0], ![-39, -17, 0, 0]], ![![126, 72, 6, -1], ![-19, -8, 0, 0]]]
    h := ![![![106, -300, -52, -1], ![-253, 767, 17, 0]], ![![-287, 751, 127, 2], ![686, -1926, -33, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {3} * I17N1 =  Ideal.span {B.equivFun.symm ![31, 16, 2, 0]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E17RS1
                    

noncomputable def R19RS0 : IdealMulPrincipalCertificate timesTableO (J0 ^ 2*J1^ 2) ![-243, -134, -8, 2] ![![9, 0, 0, 0], ![-128, -67, -4, 1]]
  ![![-2187, -1206, -72, 18], ![-3366, -1809, -108, 27]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_2J1_2
    hmul := by decide

noncomputable def E19RS0 : IdealEqCertificateO timesTableO (Ideal.span {9} * I19N0) (Ideal.span {B.equivFun.symm ![-243, -134, -8, 2]} * (J0 ^ 2*J1^ 2)) 
      ![![171, 0, 0, 0], ![-1179, -603, -36, 9]] ![![-2187, -1206, -72, 18], ![-3366, -1809, -108, 27]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R19RS0]  
      rfl
    g := ![![![95, 175, 40, -1], ![-965, -324, 0, 0]], ![![71, -216, -72, 0], ![1945, 648, 0, 0]]]
    h := ![![![-117879, -203680, -40196, 3040], ![1540294, 532684, 0, 0]], ![![-181653, -313828, -61931, 4684], ![2373122, 820705, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N0 : Ideal.span {9} * I19N0 =  Ideal.span {B.equivFun.symm ![-243, -134, -8, 2]} * (J0 ^ 2*J1^ 2) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E19RS0
                    

noncomputable def R19RS1 : IdealMulPrincipalCertificate timesTableO (J0 ^ 1*J1^ 1) ![-132, -67, -4, 1] ![![3, 0, 0, 0], ![-131, -67, -4, 1]]
  ![![-396, -201, -12, 3], ![57, 0, 0, 0]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

noncomputable def E19RS1 : IdealEqCertificateO timesTableO (Ideal.span {3} * I19N1) (Ideal.span {B.equivFun.symm ![-132, -67, -4, 1]} * (J0 ^ 1*J1^ 1)) 
      ![![57, 0, 0, 0], ![-396, -201, -12, 3]] ![![-396, -201, -12, 3], ![57, 0, 0, 0]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 3 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R19RS1]  
      rfl
    g := ![![![-2206, 4958, 1486, -74], ![-10487, -3570, 0, 0]], ![![21162, -44823, -13556, 669], ![95913, 32640, 0, 0]]]
    h := ![![![-11100, -21489, -4284, 363], ![154528, 53808, 0, 0]], ![![1777, 3320, 656, -56], ![-23560, -8208, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {3} * I19N1 =  Ideal.span {B.equivFun.symm ![-132, -67, -4, 1]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E19RS1
                    

noncomputable def R23RS0 : IdealMulPrincipalCertificate timesTableO (J0 ^ 1*J1^ 2) ![464, 264, 17, -4] ![![9, 0, 0, 0], ![-564, -280, -15, 4]]
  ![![4176, 2376, 153, -36], ![26703, 14076, 828, -207]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_2
    hmul := by decide

noncomputable def E23RS0 : IdealEqCertificateO timesTableO (Ideal.span {9} * I23N0) (Ideal.span {B.equivFun.symm ![464, 264, 17, -4]} * (J0 ^ 1*J1^ 2)) 
      ![![207, 0, 0, 0], ![-1179, -576, -36, 9]] ![![4176, 2376, 153, -36], ![26703, 14076, 828, -207]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R23RS0]  
      rfl
    g := ![![![105239736, -295683445, 78260114, 12908183], ![2479342183, 912094449, -17360, 0]], ![![-902052124, 2534430846, -670800889, -110641586], ![-21251503952, -7817952262, 148800, 0]]]
    h := ![![![2189, 8760, 2451, -59], ![-36855, -12736, 0, 0]], ![![13807, 56516, 15852, -379], ![-238602, -82432, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N0 : Ideal.span {9} * I23N0 =  Ideal.span {B.equivFun.symm ![464, 264, 17, -4]} * (J0 ^ 1*J1^ 2) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E23RS0
                    

noncomputable def R23RS1 : IdealMulPrincipalCertificate timesTableO (J0 ^ 2*J1^ 1) ![-148, -71, -3, 1] ![![9, 0, 0, 0], ![-114, -104, -12, 2]]
  ![![-1332, -639, -27, 9], ![-8406, -4554, -324, 72]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_2J1_1
    hmul := by decide

noncomputable def E23RS1 : IdealEqCertificateO timesTableO (Ideal.span {9} * I23N1) (Ideal.span {B.equivFun.symm ![-148, -71, -3, 1]} * (J0 ^ 2*J1^ 1)) 
      ![![207, 0, 0, 0], ![-1179, -558, -36, 9]] ![![-1332, -639, -27, 9], ![-8406, -4554, -324, 72]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R23RS1]  
      rfl
    g := ![![![51867292432043, -52400576308661, -11046323815237, 1394309329100], ![-36429655187504, -6031052641012, 65, 0]], ![![-415727452606523, 420001837045070, 88538650179369, -11175687766891], ![291991485198822, 48340178047166, -521, 0]]]
    h := ![![![-1168, -13501, -4173, 59], ![43920, 15092, 0, 0]], ![![-6490, -75046, -23196, 328], ![244128, 83888, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {9} * I23N1 =  Ideal.span {B.equivFun.symm ![-148, -71, -3, 1]} * (J0 ^ 2*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E23RS1
                    
