import IdealArithmetic.Examples.NF4_0_76176_2.PrimesBelow4_0_76176_2F0
import IdealArithmetic.Examples.NF4_0_76176_2.PrimesBelow4_0_76176_2F1
import IdealArithmetic.Examples.NF4_0_76176_2.ClassGroupData4_0_76176_2

set_option linter.all false

noncomputable section

noncomputable def R2RS0 : IdealMulPrincipalCertificate timesTableO (J0 ^ 5*J1^ 0) ![2, -2, -2, 5] ![![8, 0, 0, 0], ![2, -4, -5, 10]]
  ![![16, -16, -16, 40], ![-8, 8, 16, -40]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_5J1_0
    hmul := by decide

noncomputable def E2RS0 : IdealEqCertificateO timesTableO (Ideal.span {8} * I2N0) (Ideal.span {B.equivFun.symm ![2, -2, -2, 5]} * (J0 ^ 5*J1^ 0)) 
      ![![16, 0, 0, 0], ![-8, 8, 0, -8]] ![![16, -16, -16, 40], ![-8, 8, 16, -40]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 8 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R2RS0]  
      rfl
    g := ![![![-69983, -7549, -10254, 10210], ![5468, -27421, -15, 0]], ![![-76105, -8208, -11153, 11108], ![5949, -29821, -15, 0]]]
    h := ![![![-36374, 35483, -280, -35198], ![-71292, 27, 45, 0]], ![![48580, -47393, 364, 47024], ![95205, -34, -60, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {8} * I2N0 =  Ideal.span {B.equivFun.symm ![2, -2, -2, 5]} * (J0 ^ 5*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E2RS0
                    

noncomputable def R2RS1 : IdealMulPrincipalCertificate timesTableO (J0 ^ 1*J1^ 0) ![1, 0, 0, 0] ![![2, 0, 0, 0], ![0, -1, 0, 0]]
  ![![2, 0, 0, 0], ![0, -1, 0, 0]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

noncomputable def E2RS1 : IdealEqCertificateO timesTableO (Ideal.span {1} * I2N1) (Ideal.span {B.equivFun.symm ![1, 0, 0, 0]} * (J0 ^ 1*J1^ 0)) 
      ![![2, 0, 0, 0], ![0, 0, -1, 1]] ![![2, 0, 0, 0], ![0, -1, 0, 0]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 1 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R2RS1]  
      rfl
    g := ![![![1, 0, 0, 0], ![0, 0, 0, 0]], ![![8, -12, -6, 18], ![-9, 5, 1, 0]]]
    h := ![![![1, 0, 0, 0], ![0, 0, 0, 0]], ![![-8, -7, -34, 44], ![-45, 1, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {1} * I2N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0, 0]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E2RS1
                    

noncomputable def R3RS0 : IdealMulPrincipalCertificate timesTableO (J0 ^ 1*J1^ 1) ![-1, 0, -1, 1] ![![6, 0, 0, 0], ![2, -2, -3, 6]]
  ![![-6, 0, -6, 6], ![0, 6, 0, 0]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

noncomputable def E3RS0 : IdealEqCertificateO timesTableO (Ideal.span {6} * I3N0) (Ideal.span {B.equivFun.symm ![-1, 0, -1, 1]} * (J0 ^ 1*J1^ 1)) 
      ![![18, 0, 0, 0], ![12, -6, -12, 24]] ![![-6, 0, -6, 6], ![0, 6, 0, 0]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 6 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R3RS0]  
      rfl
    g := ![![![-2267, 1532, 3455, -6999], ![5712, 313, -424, 0]], ![![-1126, 766, 1728, -3500], ![2855, 160, -212, 0]]]
    h := ![![![7, -2, 3, -6], ![3, 4, -1, 0]], ![![-4, 1, 1, -2], ![2, -1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {6} * I3N0 =  Ideal.span {B.equivFun.symm ![-1, 0, -1, 1]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E3RS0
                    

noncomputable def R3RS1 : IdealMulPrincipalCertificate timesTableO (J0 ^ 5*J1^ 1) ![-1, 0, -1, 2] ![![24, 0, 0, 0], ![0, -1, 6, -13]]
  ![![-24, 0, -24, 48], ![40, 8, -8, 16]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_5J1_1
    hmul := by decide

noncomputable def E3RS1 : IdealEqCertificateO timesTableO (Ideal.span {8} * I3N1) (Ideal.span {B.equivFun.symm ![-1, 0, -1, 2]} * (J0 ^ 5*J1^ 1)) 
      ![![24, 0, 0, 0], ![-8, 0, -16, 24]] ![![-24, 0, -24, 48], ![40, 8, -8, 16]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 8 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R3RS1]  
      rfl
    g := ![![![-141801, -113681, -34574, 144498], ![-82176, 189057, -6, 0]], ![![46987, 37669, 11453, -47873], ![27242, -62645, 2, 0]]]
    h := ![![![-126, 36, 24, -59], ![-27, -18, 3, 0]], ![![459, -130, -82, 208], ![110, 65, -11, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {8} * I3N1 =  Ideal.span {B.equivFun.symm ![-1, 0, -1, 2]} * (J0 ^ 5*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E3RS1
                    

noncomputable def R5RS0 : IdealMulPrincipalCertificate timesTableO (J0 ^ 0*J1^ 1) ![2, 0, 2, -5] ![![6, 0, 0, 0], ![6, -1, 0, 2]]
  ![![12, 0, 12, -30], ![30, 36, 48, -90]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

noncomputable def E5RS0 : IdealEqCertificateO timesTableO (Ideal.span {6} * I5N0) (Ideal.span {B.equivFun.symm ![2, 0, 2, -5]} * (J0 ^ 0*J1^ 1)) 
      ![![30, 0, 0, 0], ![-12, -6, 0, 0]] ![![12, 0, 12, -30], ![30, 36, 48, -90]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 6 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R5RS0]  
      rfl
    g := ![![![-18961, -1615159, -3420571, 6443249], ![2397991, -1202880, -2864, 0]], ![![14212, 1211324, 2565329, -4832253], ![-1798414, 902125, 2148, 0]]]
    h := ![![![14, 10, 2, -1], ![34, 8, 0, 0]], ![![45, 28, 4, -3], ![110, 12, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {6} * I5N0 =  Ideal.span {B.equivFun.symm ![2, 0, 2, -5]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E5RS0
                    

noncomputable def R5RS1 : IdealMulPrincipalCertificate timesTableO (J0 ^ 0*J1^ 1) ![-4, 0, -4, 7] ![![6, 0, 0, 0], ![6, -1, 0, 2]]
  ![![-24, 0, -24, 42], ![18, -24, -36, 60]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

noncomputable def E5RS1 : IdealEqCertificateO timesTableO (Ideal.span {6} * I5N1) (Ideal.span {B.equivFun.symm ![-4, 0, -4, 7]} * (J0 ^ 0*J1^ 1)) 
      ![![30, 0, 0, 0], ![-24, 6, 12, -24]] ![![-24, 0, -24, 42], ![18, -24, -36, 60]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 6 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R5RS1]  
      rfl
    g := ![![![2314829, -419221, -2657378, 4545956], ![4031269, -1724692, -354, 669235]], ![![-1550797, 280853, 1771386, -3032993], ![-2679048, 1149593, 236, -446045]]]
    h := ![![![116, 94, 8, -61], ![-22, 0, 0, -112]], ![![-205, -165, -16, 110], ![37, 0, 0, 196]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {6} * I5N1 =  Ideal.span {B.equivFun.symm ![-4, 0, -4, 7]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E5RS1
                    

noncomputable def R13RS0 : IdealMulPrincipalCertificate timesTableO (J0 ^ 2*J1^ 1) ![-10, 6, 2, -5] ![![12, 0, 0, 0], ![0, -5, -2, 5]]
  ![![-120, 72, 24, -60], ![12, -24, -72, 120]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_2J1_1
    hmul := by decide

noncomputable def E13RS0 : IdealEqCertificateO timesTableO (Ideal.span {12} * I13N0) (Ideal.span {B.equivFun.symm ![-10, 6, 2, -5]} * (J0 ^ 2*J1^ 1)) 
      ![![156, 0, 0, 0], ![12, 12, 0, -12]] ![![-120, 72, 24, -60], ![12, -24, -72, 120]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 12 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R13RS0]  
      rfl
    g := ![![![515227717753274, 1431188105051896, 2890999972205264, -4007326694169920], ![-2747881161709951, 3091366306889510, -8406, 0]], ![![114484888937161, 318013580421380, 642387432451282, -890438025185331], ![-610586074411335, 686909333705159, -1868, 0]]]
    h := ![![![21072, -29636, -29938, 59625], ![-5242, 43464, -220, 0]], ![![-6711, 9438, 9534, -18988], ![1672, -13842, 70, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {12} * I13N0 =  Ideal.span {B.equivFun.symm ![-10, 6, 2, -5]} * (J0 ^ 2*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E13RS0
                    

noncomputable def R13RS1 : IdealMulPrincipalCertificate timesTableO (J0 ^ 4*J1^ 1) ![2, -6, -10, 19] ![![24, 0, 0, 0], ![-10, 4, 9, -18]]
  ![![48, -144, -240, 456], ![120, -48, 0, 48]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_4J1_1
    hmul := by decide

noncomputable def E13RS1 : IdealEqCertificateO timesTableO (Ideal.span {24} * I13N1) (Ideal.span {B.equivFun.symm ![2, -6, -10, 19]} * (J0 ^ 4*J1^ 1)) 
      ![![312, 0, 0, 0], ![96, 24, 0, -24]] ![![48, -144, -240, 456], ![120, -48, 0, 48]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 24 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R13RS1]  
      rfl
    g := ![![![-41003026794144026, 469293471127276, -6375021241360806, 13938991530975280], ![4317933462339469, 28534777157848670, 29920, 0]], ![![-12813678454012689, 146656871693461, -1992230298860885, 4356013919358570], ![1349378699529132, 8917279719208399, 9350, 0]]]
    h := ![![![-257107514, 502075007, 377561858, -753783670], ![17494519, -545373700, 4928, 0]], ![![7597, -14841, -11160, 22281], ![-509, 16120, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {24} * I13N1 =  Ideal.span {B.equivFun.symm ![2, -6, -10, 19]} * (J0 ^ 4*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E13RS1
                    

noncomputable def R13RS2 : IdealMulPrincipalCertificate timesTableO (J0 ^ 2*J1^ 1) ![-4, 6, 8, -17] ![![12, 0, 0, 0], ![0, -5, -2, 5]]
  ![![-48, 72, 96, -204], ![-36, -48, -72, 156]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_2J1_1
    hmul := by decide

noncomputable def E13RS2 : IdealEqCertificateO timesTableO (Ideal.span {12} * I13N2) (Ideal.span {B.equivFun.symm ![-4, 6, 8, -17]} * (J0 ^ 2*J1^ 1)) 
      ![![156, 0, 0, 0], ![-60, 12, 0, -12]] ![![-48, 72, 96, -204], ![-36, -48, -72, 156]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 12 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R13RS2]  
      rfl
    g := ![![![19550400625, 54306588614, 109699308798, -152058437297], ![-104268645581, 117302241310, 3692, 0]], ![![-7519209336, -20886661908, -42191056981, 58482649185], ![40102389123, -45115193537, -1420, 0]]]
    h := ![![![27139541, -15819297, -51967114, 102430942], ![-19534455, 75064528, -2754, 0]], ![![-25633767, 14941601, 49083843, -96747806], ![18450636, -70899752, 2601, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N2 : Ideal.span {12} * I13N2 =  Ideal.span {B.equivFun.symm ![-4, 6, 8, -17]} * (J0 ^ 2*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E13RS2
                    

noncomputable def R13RS3 : IdealMulPrincipalCertificate timesTableO (J0 ^ 4*J1^ 1) ![8, -6, -4, 7] ![![24, 0, 0, 0], ![-10, 4, 9, -18]]
  ![![192, -144, -96, 168], ![-168, 0, 48, -72]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_4J1_1
    hmul := by decide

noncomputable def E13RS3 : IdealEqCertificateO timesTableO (Ideal.span {24} * I13N3) (Ideal.span {B.equivFun.symm ![8, -6, -4, 7]} * (J0 ^ 4*J1^ 1)) 
      ![![312, 0, 0, 0], ![-192, 24, 0, -24]] ![![192, -144, -96, 168], ![-168, 0, 48, -72]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 24 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R13RS3]  
      rfl
    g := ![![![259815725, -2987984, 40395278, -88321989], ![-27364801, -180813882, 7436, 0]], ![![-139906523, 1608976, -21752209, 47559972], ![14735526, 97365329, -4004, 0]]]
    h := ![![![300502912, 22488596, -720535708, 1418577365], ![-292316300, 1040773800, -11818, 0]], ![![-292593849, -21896711, 701571641, -1381241260], ![284622722, -1013381259, 11507, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N3 : Ideal.span {24} * I13N3 =  Ideal.span {B.equivFun.symm ![8, -6, -4, 7]} * (J0 ^ 4*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E13RS3
                    

noncomputable def R23RS0 : IdealMulPrincipalCertificate timesTableO (J0 ^ 3*J1^ 1) ![-5, 0, -5, 8] ![![12, 0, 0, 0], ![0, 1, 6, -11]]
  ![![-60, 0, -60, 96], ![168, -72, -84, 168]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_3J1_1
    hmul := by decide

noncomputable def E23RS0 : IdealEqCertificateO timesTableO (Ideal.span {12} * I23N0) (Ideal.span {B.equivFun.symm ![-5, 0, -5, 8]} * (J0 ^ 3*J1^ 1)) 
      ![![276, 0, 0, 0], ![72, 12, 0, -12]] ![![-60, 0, -60, 96], ![168, -72, -84, 168]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 12 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R23RS0]  
      rfl
    g := ![![![-1280405159, 60487061, 149521921, -238556703], ![298478546, 512162094, 23, 0]], ![![-380395614, 17970102, 44421470, -70872814], ![88675007, 152158255, 7, 0]]]
    h := ![![![-2206735, 5117750, 3277670, -6574684], ![-67285, -8407185, 19875, 0]], ![![3442522, -7983748, -5113202, 10256582], ![104999, 13115301, -31005, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N0 : Ideal.span {12} * I23N0 =  Ideal.span {B.equivFun.symm ![-5, 0, -5, 8]} * (J0 ^ 3*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E23RS0
                    

noncomputable def R23RS1 : IdealMulPrincipalCertificate timesTableO (J0 ^ 3*J1^ 1) ![-1, 0, -1, 4] ![![12, 0, 0, 0], ![0, 1, 6, -11]]
  ![![-12, 0, -12, 48], ![24, 24, -12, 24]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_3J1_1
    hmul := by decide

noncomputable def E23RS1 : IdealEqCertificateO timesTableO (Ideal.span {12} * I23N1) (Ideal.span {B.equivFun.symm ![-1, 0, -1, 4]} * (J0 ^ 3*J1^ 1)) 
      ![![276, 0, 0, 0], ![-120, 12, 0, -12]] ![![-12, 0, -12, 48], ![24, 24, -12, 24]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 12 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R23RS1]  
      rfl
    g := ![![![136920485, -6468140, -15989173, 25510128], ![-31917862, -54768226, -23, 0]], ![![-59713418, 2820868, 6973152, -11125402], ![13919950, 23885381, 10, 0]]]
    h := ![![![-50023, -22104, 93795, -186312], ![28898, -239690, 38, 0]], ![![192142, 84892, -360235, 715564], ![-110940, 920568, -146, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {12} * I23N1 =  Ideal.span {B.equivFun.symm ![-1, 0, -1, 4]} * (J0 ^ 3*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E23RS1
                    
