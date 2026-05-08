import IdealArithmetic.Examples.NF4_4_54381317_1.PrimesBelow4_4_54381317_1F8
import IdealArithmetic.Examples.NF4_4_54381317_1.ClassGroupData4_4_54381317_1

    set_option linter.all false

    noncomputable section

noncomputable def R421RS1 : IdealMulPrincipalCertificate timesTableO (J0 ^ 1*J1^ 0) ![-76, -50, -6, 1] ![![3, 0, 0, 0], ![-1, 1, 0, 0]]
  ![![-228, -150, -18, 3], ![459, 306, 36, -6]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

noncomputable def E421RS1 : IdealEqCertificateO timesTableO (Ideal.span {3} * I421N1) (Ideal.span {B.equivFun.symm ![-76, -50, -6, 1]} * (J0 ^ 1*J1^ 0)) 
      ![![1263, 0, 0, 0], ![-630, 3, 0, 0]] ![![-228, -150, -18, 3], ![459, 306, 36, -6]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 3 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R421RS1]  
      rfl
    g := ![![![1042147, 10424345, -11467200, 282], ![3127400, 34400752, -842, 0]], ![![-517359, -5175038, 5692751, -140], ![-1552559, -17077832, 418, 0]]]
    h := ![![![-95206, 27015, -126, 0], ![-190865, 53250, 1, 0]], ![![192933, -52782, 456, -1], ![386784, -103974, 419, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R421N1 : Ideal.span {3} * I421N1 =  Ideal.span {B.equivFun.symm ![-76, -50, -6, 1]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E421RS1
                    

noncomputable def R421RS2 : IdealMulPrincipalCertificate timesTableO (J0 ^ 0*J1^ 1) ![-623, -285, -14, 4] ![![3, 0, 0, 0], ![1, 1, 0, 0]]
  ![![-1869, -855, -42, 12], ![909, 420, 21, -6]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

noncomputable def E421RS2 : IdealEqCertificateO timesTableO (Ideal.span {3} * I421N2) (Ideal.span {B.equivFun.symm ![-623, -285, -14, 4]} * (J0 ^ 0*J1^ 1)) 
      ![![1263, 0, 0, 0], ![-495, 3, 0, 0]] ![![-1869, -855, -42, 12], ![909, 420, 21, -6]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 3 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R421RS2]  
      rfl
    g := ![![![549970, -5508528, -6058766, 215], ![-1652850, 18176808, -620, 0]], ![![-214658, 2150103, 2364870, -84], ![645149, -7094808, 242, 0]]]
    h := ![![![-51233, 6245153, -42796, 30], ![-130718, 15933812, -12626, 0]], ![![25368, -3037105, 20880, -15], ![64725, -7748828, 6313, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R421N2 : Ideal.span {3} * I421N2 =  Ideal.span {B.equivFun.symm ![-623, -285, -14, 4]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E421RS2
                    

noncomputable def R431RS1 : IdealMulPrincipalCertificate timesTableO (J0 ^ 2*J1^ 2) ![637, 364, 29, -6] ![![9, 0, 0, 0], ![-128, -67, -4, 1]]
  ![![5733, 3276, 261, -54], ![1575, 774, 18, -9]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_2J1_2
    hmul := by decide

noncomputable def E431RS1 : IdealEqCertificateO timesTableO (Ideal.span {9} * I431N1) (Ideal.span {B.equivFun.symm ![637, 364, 29, -6]} * (J0 ^ 2*J1^ 2)) 
      ![![3879, 0, 0, 0], ![630, 9, 0, 0]] ![![5733, 3276, 261, -54], ![1575, 774, 18, -9]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R431RS1]  
      rfl
    g := ![![![-89103, -23840947, -6966971, 53455], ![181853810, 60778310, 0, 0]], ![![-14659, -3943779, -1152489, 8842], ![30082658, 10054080, 0, 0]]]
    h := ![![![22547, -1410530, -20714, -8], ![-138816, 8686823, 3442, 0]], ![![6125, -387794, -5751, -3], ![-37710, 2388243, 1292, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R431N1 : Ideal.span {9} * I431N1 =  Ideal.span {B.equivFun.symm ![637, 364, 29, -6]} * (J0 ^ 2*J1^ 2) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E431RS1
                    

noncomputable def R431RS2 : IdealMulPrincipalCertificate timesTableO (J0 ^ 2*J1^ 2) ![-46, -19, -2, 0] ![![9, 0, 0, 0], ![-128, -67, -4, 1]]
  ![![-414, -171, -18, 0], ![909, 432, 9, -9]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_2J1_2
    hmul := by decide

noncomputable def E431RS2 : IdealEqCertificateO timesTableO (Ideal.span {9} * I431N2) (Ideal.span {B.equivFun.symm ![-46, -19, -2, 0]} * (J0 ^ 2*J1^ 2)) 
      ![![3879, 0, 0, 0], ![-1710, 9, 0, 0]] ![![-414, -171, -18, 0], ![909, 432, 9, -9]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R431RS2]  
      rfl
    g := ![![![-182205, -48732186, -14240864, 109268], ![371718680, 124234013, 0, 0]], ![![80086, 21374336, 6246139, -47927], ![-163038162, -54489827, 0, 0]]]
    h := ![![![-171746, 7051423, -43188, 32], ![-389592, 15993546, -13792, 0]], ![![377491, -15470160, 94901, -71], ![856308, -35088330, 30600, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R431N2 : Ideal.span {9} * I431N2 =  Ideal.span {B.equivFun.symm ![-46, -19, -2, 0]} * (J0 ^ 2*J1^ 2) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E431RS2
                    

noncomputable def R433RS1 : IdealMulPrincipalCertificate timesTableO (J0 ^ 1*J1^ 1) ![-22, -7, 1, 0] ![![3, 0, 0, 0], ![-131, -67, -4, 1]]
  ![![-66, -21, 3, 0], ![-948, -546, -42, 9]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

noncomputable def E433RS1 : IdealEqCertificateO timesTableO (Ideal.span {3} * I433N1) (Ideal.span {B.equivFun.symm ![-22, -7, 1, 0]} * (J0 ^ 1*J1^ 1)) 
      ![![1299, 0, 0, 0], ![-555, 3, 0, 0]] ![![-66, -21, 3, 0], ![-948, -546, -42, 9]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 3 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R433RS1]  
      rfl
    g := ![![![-2079997, 4408845, 1333283, -65801], ![-9433613, -3210304, 0, 0]], ![![888689, -1883313, -569553, 28108], ![4029897, 1371392, 0, 0]]]
    h := ![![![-12874, -300, -659893, 3567], ![-30132, -865, -1544511, 0]], ![![-189492, -10400, -14015722, 75761], ![-443512, -26738, -32804510, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R433N1 : Ideal.span {3} * I433N1 =  Ideal.span {B.equivFun.symm ![-22, -7, 1, 0]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E433RS1
                    

noncomputable def R433RS2 : IdealMulPrincipalCertificate timesTableO (J0 ^ 1*J1^ 1) ![-165, -76, -4, 1] ![![3, 0, 0, 0], ![-131, -67, -4, 1]]
  ![![-495, -228, -12, 3], ![933, 402, 15, -6]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

noncomputable def E433RS2 : IdealEqCertificateO timesTableO (Ideal.span {3} * I433N2) (Ideal.span {B.equivFun.symm ![-165, -76, -4, 1]} * (J0 ^ 1*J1^ 1)) 
      ![![1299, 0, 0, 0], ![-219, 3, 0, 0]] ![![-495, -228, -12, 3], ![933, 402, 15, -6]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 3 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R433RS2]  
      rfl
    g := ![![![2855283, -6051764, -1830071, 90323], ![12948188, 4406376, 0, 0]], ![![-474601, 1005960, 304203, -15014], ![-2152307, -732448, 0, 0]]]
    h := ![![![-68733, 5370030, -75520, 27], ![-407688, 31846786, -11690, 0]], ![![129907, -10123472, 142522, -53], ![770540, -60036890, 22947, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R433N2 : Ideal.span {3} * I433N2 =  Ideal.span {B.equivFun.symm ![-165, -76, -4, 1]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E433RS2
                    

noncomputable def R439RS1 : IdealMulPrincipalCertificate timesTableO (J0 ^ 1*J1^ 2) ![-122, -72, -5, 1] ![![9, 0, 0, 0], ![-564, -280, -15, 4]]
  ![![-1098, -648, -45, 9], ![-9324, -4833, -270, 72]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_2
    hmul := by decide

noncomputable def E439RS1 : IdealEqCertificateO timesTableO (Ideal.span {9} * I439N1) (Ideal.span {B.equivFun.symm ![-122, -72, -5, 1]} * (J0 ^ 1*J1^ 2)) 
      ![![3951, 0, 0, 0], ![279, 9, 0, 0]] ![![-1098, -648, -45, 9], ![-9324, -4833, -270, 72]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R439RS1]  
      rfl
    g := ![![![-80, 577, -131, -24], ![-4387, -1612, 0, 0]], ![![-174814, 491709, -130120, -21464], ![-4122391, -1516544, 26, 0]]]
    h := ![![![-1500, 61830, 1996, 0], ![21238, -876280, 1, 0]], ![![-12198, 525478, 17025, 2], ![172706, -7447035, -870, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R439N1 : Ideal.span {9} * I439N1 =  Ideal.span {B.equivFun.symm ![-122, -72, -5, 1]} * (J0 ^ 1*J1^ 2) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E439RS1
                    

noncomputable def R439RS2 : IdealMulPrincipalCertificate timesTableO (J0 ^ 2*J1^ 1) ![-94, -53, -3, 1] ![![9, 0, 0, 0], ![-114, -104, -12, 2]]
  ![![-846, -477, -27, 9], ![-774, -270, 36, 0]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_2J1_1
    hmul := by decide

noncomputable def E439RS2 : IdealEqCertificateO timesTableO (Ideal.span {9} * I439N2) (Ideal.span {B.equivFun.symm ![-94, -53, -3, 1]} * (J0 ^ 2*J1^ 1)) 
      ![![3951, 0, 0, 0], ![450, 9, 0, 0]] ![![-846, -477, -27, 9], ![-774, -270, 36, 0]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R439RS2]  
      rfl
    g := ![![![-1457121916771, 1472115043669, 310325162539, -39170086130], ![1023299095233, 169337229556, -15111300, 0]], ![![-169140426410, 170880805083, 36022058085, -4546802155], ![118782953802, 19656399980, -1754096, 0]]]
    h := ![![![-71496, 14910226, 302033, 76], ![627733, -130924340, -33363, 0]], ![![-65424, 13647991, 276436, 69], ![574421, -119840850, -30291, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R439N2 : Ideal.span {9} * I439N2 =  Ideal.span {B.equivFun.symm ![-94, -53, -3, 1]} * (J0 ^ 2*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E439RS2
                    

noncomputable def R449RS1 : IdealMulPrincipalCertificate timesTableO (J0 ^ 1*J1^ 2) ![179, 84, 2, -1] ![![9, 0, 0, 0], ![-564, -280, -15, 4]]
  ![![1611, 756, 18, -9], ![8199, 4401, 243, -63]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_2
    hmul := by decide

noncomputable def E449RS1 : IdealEqCertificateO timesTableO (Ideal.span {9} * I449N1) (Ideal.span {B.equivFun.symm ![179, 84, 2, -1]} * (J0 ^ 1*J1^ 2)) 
      ![![4041, 0, 0, 0], ![738, 9, 0, 0]] ![![1611, 756, 18, -9], ![8199, 4401, 243, -63]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R449RS1]  
      rfl
    g := ![![![11772161, -33076262, 8756589, 1444383], ![277376074, 102045802, 0, 0]], ![![217740212, -611793363, 161965733, 26715940], ![5130469223, 1887483667, -1, 0]]]
    h := ![![![6819, -431498, -5509, -3], ![-37336, 2363171, 1346, 0]], ![![35481, -2194242, -27665, -11], ![-194269, 12017188, 4932, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R449N1 : Ideal.span {9} * I449N1 =  Ideal.span {B.equivFun.symm ![179, 84, 2, -1]} * (J0 ^ 1*J1^ 2) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E449RS1
                    

noncomputable def R449RS2 : IdealMulPrincipalCertificate timesTableO (J0 ^ 2*J1^ 1) ![-368, -151, -6, 2] ![![9, 0, 0, 0], ![-114, -104, -12, 2]]
  ![![-3312, -1359, -54, 18], ![-15498, -6570, -288, 90]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_2J1_1
    hmul := by decide

noncomputable def E449RS2 : IdealEqCertificateO timesTableO (Ideal.span {9} * I449N2) (Ideal.span {B.equivFun.symm ![-368, -151, -6, 2]} * (J0 ^ 2*J1^ 1)) 
      ![![4041, 0, 0, 0], ![-945, 9, 0, 0]] ![![-3312, -1359, -54, 18], ![-15498, -6570, -288, 90]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R449RS2]  
      rfl
    g := ![![![11655704572440, -11775545015776, -2482348334811, 313331520889], ![-8186532948984, -1355308220211, 170, 0]], ![![-2673961520441, 2701454387394, 569481140031, -71882092139], ![1878091020217, 310924320938, -39, 0]]]
    h := ![![![-735802, 41538440, -416012, 195], ![-3146426, 177596317, -87553, 0]], ![![-3443433, 194347921, -1946798, 916], ![-14724759, 830928500, -411274, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R449N2 : Ideal.span {9} * I449N2 =  Ideal.span {B.equivFun.symm ![-368, -151, -6, 2]} * (J0 ^ 2*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E449RS2
                    

noncomputable def R457RS1 : IdealMulPrincipalCertificate timesTableO (J0 ^ 2*J1^ 0) ![590, 331, 21, -5] ![![9, 0, 0, 0], ![-4, 1, 0, 0]]
  ![![5310, 2979, 189, -45], ![-4275, -2394, -153, 36]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_2J1_0
    hmul := by decide

noncomputable def E457RS1 : IdealEqCertificateO timesTableO (Ideal.span {9} * I457N1) (Ideal.span {B.equivFun.symm ![590, 331, 21, -5]} * (J0 ^ 2*J1^ 0)) 
      ![![4113, 0, 0, 0], ![-1044, 9, 0, 0]] ![![5310, 2979, 189, -45], ![-4275, -2394, -153, 36]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R457RS1]  
      rfl
    g := ![![![-8551047314018925443, -207362897364958939130, 52375164798444656200, -19684649], ![-19239856456542581927, -471376483185293258417, 177161845, 0]], ![![2179862205548977168, 52861658484562695507, -13351656009007557257, 5018078], ![4904689962485198546, 120164904080887364500, -45162703, 0]]]
    h := ![![![677190, 19425, 48850397, -421126], ![2667890, 99524, 192454577, 0]], ![![-544983, -15489, -39265129, 338494], ![-2147041, -79528, -154691754, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R457N1 : Ideal.span {9} * I457N1 =  Ideal.span {B.equivFun.symm ![590, 331, 21, -5]} * (J0 ^ 2*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E457RS1
                    

noncomputable def R457RS2 : IdealMulPrincipalCertificate timesTableO (J0 ^ 0*J1^ 2) ![-274, -138, -7, 2] ![![9, 0, 0, 0], ![-2, 1, 0, 0]]
  ![![-2466, -1242, -63, 18], ![1314, 666, 36, -9]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_2
    hmul := by decide

noncomputable def E457RS2 : IdealEqCertificateO timesTableO (Ideal.span {9} * I457N2) (Ideal.span {B.equivFun.symm ![-274, -138, -7, 2]} * (J0 ^ 0*J1^ 2)) 
      ![![4113, 0, 0, 0], ![-837, 9, 0, 0]] ![![-2466, -1242, -63, 18], ![1314, 666, 36, -9]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R457RS2]  
      rfl
    g := ![![![1765396, 75046653, -37965452, 284], ![7946208, 341683927, -2532, 0]], ![![-354190, -15056758, 7617084, -57], ![-1594257, -68552724, 508, 0]]]
    h := ![![![-11800, -953, -2536842, 27278], ![-57982, -5305, -12466044, 0]], ![![6422, 564, 1356398, -14585], ![31556, 3110, 6665344, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R457N2 : Ideal.span {9} * I457N2 =  Ideal.span {B.equivFun.symm ![-274, -138, -7, 2]} * (J0 ^ 0*J1^ 2) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E457RS2
                    

noncomputable def R463RS0 : IdealMulPrincipalCertificate timesTableO (J0 ^ 2*J1^ 2) ![-13, -4, 1, 0] ![![9, 0, 0, 0], ![-128, -67, -4, 1]]
  ![![-117, -36, 9, 0], ![-1017, -558, -36, 9]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_2J1_2
    hmul := by decide

noncomputable def E463RS0 : IdealEqCertificateO timesTableO (Ideal.span {9} * I463N0) (Ideal.span {B.equivFun.symm ![-13, -4, 1, 0]} * (J0 ^ 2*J1^ 2)) 
      ![![4167, 0, 0, 0], ![531, 9, 0, 0]] ![![-117, -36, 9, 0], ![-1017, -558, -36, 9]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R463RS0]  
      rfl
    g := ![![![120, 128, 42, 1], ![-1455, -463, 0, 0]], ![![30, 25, 6, 0], ![-187, -60, 0, 0]]]
    h := ![![![-5420, 498, -2398340, -40650], ![42533, -4629, 18820950, 0]], ![![-100058, 21110990, 363506, 96], ![785199, -165680909, -44447, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R463N0 : Ideal.span {9} * I463N0 =  Ideal.span {B.equivFun.symm ![-13, -4, 1, 0]} * (J0 ^ 2*J1^ 2) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E463RS0
                    

noncomputable def R463RS1 : IdealMulPrincipalCertificate timesTableO (J0 ^ 0*J1^ 2) ![-292, -147, -7, 2] ![![9, 0, 0, 0], ![-2, 1, 0, 0]]
  ![![-2628, -1323, -63, 18], ![1350, 666, 27, -9]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_2
    hmul := by decide

noncomputable def E463RS1 : IdealEqCertificateO timesTableO (Ideal.span {9} * I463N1) (Ideal.span {B.equivFun.symm ![-292, -147, -7, 2]} * (J0 ^ 0*J1^ 2)) 
      ![![4167, 0, 0, 0], ![1125, 9, 0, 0]] ![![-2628, -1323, -63, 18], ![1350, 666, 27, -9]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R463RS1]  
      rfl
    g := ![![![388512, 16535632, -8366305, 536], ![1750960, 75287048, -4790, 0]], ![![105122, 4473944, -2263619, 145], ![473752, 20369948, -1296, 0]]]
    h := ![![![-451884, 116346954, 993929, 505], ![1673776, -430962509, -233813, 0]], ![![232050, -59768428, -510662, -260], ![-859512, 221389134, 120379, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R463N1 : Ideal.span {9} * I463N1 =  Ideal.span {B.equivFun.symm ![-292, -147, -7, 2]} * (J0 ^ 0*J1^ 2) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E463RS1
                    

noncomputable def R463RS2 : IdealMulPrincipalCertificate timesTableO (J0 ^ 2*J1^ 2) ![-162, -76, -4, 1] ![![9, 0, 0, 0], ![-128, -67, -4, 1]]
  ![![-1458, -684, -36, 9], ![54, -27, -9, 0]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_2J1_2
    hmul := by decide

noncomputable def E463RS2 : IdealEqCertificateO timesTableO (Ideal.span {9} * I463N2) (Ideal.span {B.equivFun.symm ![-162, -76, -4, 1]} * (J0 ^ 2*J1^ 2)) 
      ![![4167, 0, 0, 0], ![1143, 9, 0, 0]] ![![-1458, -684, -36, 9], ![54, -27, -9, 0]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R463RS2]  
      rfl
    g := ![![![186635, 49883606, 14577320, -111849], ![-380501153, -127169282, 0, 0]], ![![51633, 13769172, 4023705, -30874], ![-105027736, -35101872, 0, 0]]]
    h := ![![![-13560, 1360988, 11352, 5], ![49434, -4962102, -2314, 0]], ![![474, -50796, -527, -1], ![-1728, 185199, 463, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R463N2 : Ideal.span {9} * I463N2 =  Ideal.span {B.equivFun.symm ![-162, -76, -4, 1]} * (J0 ^ 2*J1^ 2) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E463RS2
                    

noncomputable def R463RS3 : IdealMulPrincipalCertificate timesTableO (J0 ^ 2*J1^ 0) ![-571, -281, -15, 4] ![![9, 0, 0, 0], ![-4, 1, 0, 0]]
  ![![-5139, -2529, -135, 36], ![3816, 1881, 99, -27]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_2J1_0
    hmul := by decide

noncomputable def E463RS3 : IdealEqCertificateO timesTableO (Ideal.span {9} * I463N3) (Ideal.span {B.equivFun.symm ![-571, -281, -15, 4]} * (J0 ^ 2*J1^ 0)) 
      ![![4167, 0, 0, 0], ![1359, 9, 0, 0]] ![![-5139, -2529, -135, 36], ![3816, 1881, 99, -27]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R463RS3]  
      rfl
    g := ![![![84305978734, 2044419986460, -516374123689, 847], ![189688452401, 4647367082728, -7620, 0]], ![![27570927241, 668594986230, -168871930623, 277], ![62034586373, 1519847365641, -2492, 0]]]
    h := ![![![-16803, 391935, 2746, 1], ![51518, -1202104, -459, 0]], ![![11760, -291201, -2230, -2], ![-36056, 893128, 923, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R463N3 : Ideal.span {9} * I463N3 =  Ideal.span {B.equivFun.symm ![-571, -281, -15, 4]} * (J0 ^ 2*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E463RS3
                    
