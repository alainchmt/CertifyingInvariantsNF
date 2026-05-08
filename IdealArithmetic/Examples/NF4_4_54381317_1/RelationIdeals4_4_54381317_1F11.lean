import IdealArithmetic.Examples.NF4_4_54381317_1.PrimesBelow4_4_54381317_1F11
import IdealArithmetic.Examples.NF4_4_54381317_1.ClassGroupData4_4_54381317_1

    set_option linter.all false

    noncomputable section

noncomputable def R607RS1 : IdealMulPrincipalCertificate timesTableO (J0 ^ 2*J1^ 1) ![-712, -332, -9, 4] ![![9, 0, 0, 0], ![-114, -104, -12, 2]]
  ![![-6408, -2988, -81, 36], ![-68202, -39798, -3294, 666]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_2J1_1
    hmul := by decide

noncomputable def E607RS1 : IdealEqCertificateO timesTableO (Ideal.span {9} * I607N1) (Ideal.span {B.equivFun.symm ![-712, -332, -9, 4]} * (J0 ^ 2*J1^ 1)) 
      ![![5463, 0, 0, 0], ![810, 9, 0, 0]] ![![-6408, -2988, -81, 36], ![-68202, -39798, -3294, 666]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R607RS1]  
      rfl
    g := ![![![751762491818982, -759491887307073, -160104981914893, 20209064450146], ![-528009986171720, -87413839223629, 1214, 0]], ![![112702437370292, -113861209882002, -24002556516575, 3029694677893], ![-79157996102464, -13104874009552, 182, 0]]]
    h := ![![![-968326, 172959485, 1963201, 459], ![6530813, -1166588206, -278609, 0]], ![![-10306134, 1840274562, 20888316, 4884], ![69509064, -12412401918, -2964514, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R607N1 : Ideal.span {9} * I607N1 =  Ideal.span {B.equivFun.symm ![-712, -332, -9, 4]} * (J0 ^ 2*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E607RS1
                    

noncomputable def R607RS2 : IdealMulPrincipalCertificate timesTableO (J0 ^ 1*J1^ 2) ![-68, -18, 4, 1] ![![9, 0, 0, 0], ![-564, -280, -15, 4]]
  ![![-612, -162, 36, 9], ![5031, 2223, 36, -45]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_2
    hmul := by decide

noncomputable def E607RS2 : IdealEqCertificateO timesTableO (Ideal.span {9} * I607N2) (Ideal.span {B.equivFun.symm ![-68, -18, 4, 1]} * (J0 ^ 1*J1^ 2)) 
      ![![5463, 0, 0, 0], ![2727, 9, 0, 0]] ![![-612, -162, 36, 9], ![5031, 2223, 36, -45]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R607RS2]  
      rfl
    g := ![![![-10964038530657647505, 30806140145372592215, -8155593429216314685, -1345249780873628322], ![-258338734122073575831, -95042016774117756928, 29711444, 0]], ![![-5478995537261269699, 15394574171258177064, -4075547516314068391, -672253889412973858], ![-129098120861097134756, -47494797131697702306, 14847528, 0]]]
    h := ![![![-150053, 112283879, 444204, 243], ![300601, -224939324, -147500, 0]], ![![1227709, -922987125, -3652779, -2002], ![-2459468, 1849028530, 1215209, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R607N2 : Ideal.span {9} * I607N2 =  Ideal.span {B.equivFun.symm ![-68, -18, 4, 1]} * (J0 ^ 1*J1^ 2) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E607RS2
                    

noncomputable def R617RS0 : IdealMulPrincipalCertificate timesTableO (J0 ^ 1*J1^ 2) ![188, 84, 2, -1] ![![9, 0, 0, 0], ![-564, -280, -15, 4]]
  ![![1692, 756, 18, -9], ![3123, 1881, 108, -27]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_2
    hmul := by decide

noncomputable def E617RS0 : IdealEqCertificateO timesTableO (Ideal.span {9} * I617N0) (Ideal.span {B.equivFun.symm ![188, 84, 2, -1]} * (J0 ^ 1*J1^ 2)) 
      ![![5553, 0, 0, 0], ![315, 9, 0, 0]] ![![1692, 756, 18, -9], ![3123, 1881, 108, -27]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R617RS0]  
      rfl
    g := ![![![827191201277783, -2324195394485507, 615305639344849, 101493505646884], ![19490584707523029, 7170525416228628, -27668938, 0]], ![![48306770939759, -135729652789976, 35932960277859, 5927074081025], ![1138221984822572, 418748323560051, -1615826, 0]]]
    h := ![![![107869, -27451445, -786935, -72], ![-1901571, 483984092, 44423, 0]], ![![199126, -50653212, -1452052, -133], ![-3510297, 893044066, 82058, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R617N0 : Ideal.span {9} * I617N0 =  Ideal.span {B.equivFun.symm ![188, 84, 2, -1]} * (J0 ^ 1*J1^ 2) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E617RS0
                    

noncomputable def R617RS1 : IdealMulPrincipalCertificate timesTableO (J0 ^ 2*J1^ 1) ![194, 130, 9, -2] ![![9, 0, 0, 0], ![-114, -104, -12, 2]]
  ![![1746, 1170, 81, -18], ![7758, 5454, 450, -90]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_2J1_1
    hmul := by decide

noncomputable def E617RS1 : IdealEqCertificateO timesTableO (Ideal.span {9} * I617N1) (Ideal.span {B.equivFun.symm ![194, 130, 9, -2]} * (J0 ^ 2*J1^ 1)) 
      ![![5553, 0, 0, 0], ![2124, 9, 0, 0]] ![![1746, 1170, 81, -18], ![7758, 5454, 450, -90]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R617RS1]  
      rfl
    g := ![![![-6596395619113491874, 6664217771844701247, 1404853012480025659, -177325931602025338], ![4633062699347199327, 767019201366852008, -13209794, 0]], ![![-2537075238114276414, 2563160681472369206, 540328081721745635, -68202281385225075], ![1781947192052192114, 295007385140364681, -5080690, 0]]]
    h := ![![![26378, -3493580, -16691, -8], ![-68962, 9133932, 4934, 0]], ![![117490, -15519311, -74254, -36], ![-307163, 40575096, 22202, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R617N1 : Ideal.span {9} * I617N1 =  Ideal.span {B.equivFun.symm ![194, 130, 9, -2]} * (J0 ^ 2*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E617RS1
                    

noncomputable def R617RS2 : IdealMulPrincipalCertificate timesTableO (J0 ^ 1*J1^ 2) ![-679, -348, -19, 5] ![![9, 0, 0, 0], ![-564, -280, -15, 4]]
  ![![-6111, -3132, -171, 45], ![-14598, -8397, -531, 126]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_2
    hmul := by decide

noncomputable def E617RS2 : IdealEqCertificateO timesTableO (Ideal.span {9} * I617N2) (Ideal.span {B.equivFun.symm ![-679, -348, -19, 5]} * (J0 ^ 1*J1^ 2)) 
      ![![5553, 0, 0, 0], ![-1260, 9, 0, 0]] ![![-6111, -3132, -171, 45], ![-14598, -8397, -531, 126]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R617RS2]  
      rfl
    g := ![![![-25796589470, 72481808970, -19188776693, -3165152564], ![-607828777451, -223618315000, 617, 0]], ![![5853354827, -16446427299, 4354014160, 718186431], ![137918906650, 50739936402, -140, 0]]]
    h := ![![![-24507, -1631, -5228986, 37350], ![-108001, -7957, -23044945, 0]], ![![-58966, -4329, -13858143, 98987], ![-259860, -20928, -61074965, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R617N2 : Ideal.span {9} * I617N2 =  Ideal.span {B.equivFun.symm ![-679, -348, -19, 5]} * (J0 ^ 1*J1^ 2) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E617RS2
                    

noncomputable def R617RS3 : IdealMulPrincipalCertificate timesTableO (J0 ^ 2*J1^ 1) ![-359, -151, -6, 2] ![![9, 0, 0, 0], ![-114, -104, -12, 2]]
  ![![-3231, -1359, -54, 18], ![-16524, -7506, -396, 108]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_2J1_1
    hmul := by decide

noncomputable def E617RS3 : IdealEqCertificateO timesTableO (Ideal.span {9} * I617N3) (Ideal.span {B.equivFun.symm ![-359, -151, -6, 2]} * (J0 ^ 2*J1^ 1)) 
      ![![5553, 0, 0, 0], ![-1188, 9, 0, 0]] ![![-3231, -1359, -54, 18], ![-16524, -7506, -396, 108]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R617RS3]  
      rfl
    g := ![![![441349127003268, -445886945803480, -93995370562546, 11864455926855], ![-309987195131920, -51319428544624, 32084, 0]], ![![-94779187546627, 95753678607996, 20185391360276, -2547877461699], ![66569372650600, 11020784782896, -6890, 0]]]
    h := ![![![-37231, 6410917, -50677, 16], ![-174024, 29964863, -9870, 0]], ![![-190332, 32782650, -259164, 82], ![-889644, 153227320, -50582, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R617N3 : Ideal.span {9} * I617N3 =  Ideal.span {B.equivFun.symm ![-359, -151, -6, 2]} * (J0 ^ 2*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E617RS3
                    

noncomputable def R619RS1 : IdealMulPrincipalCertificate timesTableO (J0 ^ 1*J1^ 2) ![719, 414, 35, -7] ![![9, 0, 0, 0], ![-564, -280, -15, 4]]
  ![![6471, 3726, 315, -63], ![3528, 2871, 315, -54]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_2
    hmul := by decide

noncomputable def E619RS1 : IdealEqCertificateO timesTableO (Ideal.span {9} * I619N1) (Ideal.span {B.equivFun.symm ![719, 414, 35, -7]} * (J0 ^ 1*J1^ 2)) 
      ![![5571, 0, 0, 0], ![1953, 9, 0, 0]] ![![6471, 3726, 315, -63], ![3528, 2871, 315, -54]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R619RS1]  
      rfl
    g := ![![![695837639313, -1955125546334, 517598405847, 85376882478], ![16395583995101, 6031884354229, -904, 0]], ![![244005008489, -685591578203, 181502977461, 29938574386], ![5749336316853, 2115162947973, -317, 0]]]
    h := ![![![750194, -209530, 423315460, 1950767], ![-2139951, 607555, -1207524780, 0]], ![![409304, -153954, 309303706, 1425366], ![-1167552, 444541, -882301560, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R619N1 : Ideal.span {9} * I619N1 =  Ideal.span {B.equivFun.symm ![719, 414, 35, -7]} * (J0 ^ 1*J1^ 2) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E619RS1
                    

noncomputable def R619RS2 : IdealMulPrincipalCertificate timesTableO (J0 ^ 2*J1^ 1) ![-293, -148, -9, 2] ![![9, 0, 0, 0], ![-114, -104, -12, 2]]
  ![![-2637, -1332, -81, 18], ![-10260, -5058, -270, 72]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_2J1_1
    hmul := by decide

noncomputable def E619RS2 : IdealEqCertificateO timesTableO (Ideal.span {9} * I619N2) (Ideal.span {B.equivFun.symm ![-293, -148, -9, 2]} * (J0 ^ 2*J1^ 1)) 
      ![![5571, 0, 0, 0], ![2448, 9, 0, 0]] ![![-2637, -1332, -81, 18], ![-10260, -5058, -270, 72]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R619RS2]  
      rfl
    g := ![![![1455233049, -1470195137, -309925063, 39119929], ![-1022101507, -169212375, 0, 0]], ![![643320829, -649935133, -137009833, 17293906], ![-451844576, -74804404, 0, 0]]]
    h := ![![![-16799, 562405, 2339, 1], ![38229, -1280026, -617, 0]], ![![-62412, 2189795, 9136, 4], ![142029, -4983918, -2468, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R619N2 : Ideal.span {9} * I619N2 =  Ideal.span {B.equivFun.symm ![-293, -148, -9, 2]} * (J0 ^ 2*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E619RS2
                    

noncomputable def R631RS1 : IdealMulPrincipalCertificate timesTableO (J0 ^ 1*J1^ 1) ![-16, -4, 1, 0] ![![3, 0, 0, 0], ![-131, -67, -4, 1]]
  ![![-48, -12, 3, 0], ![-585, -345, -27, 6]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

noncomputable def E631RS1 : IdealEqCertificateO timesTableO (Ideal.span {3} * I631N1) (Ideal.span {B.equivFun.symm ![-16, -4, 1, 0]} * (J0 ^ 1*J1^ 1)) 
      ![![1893, 0, 0, 0], ![573, 3, 0, 0]] ![![-48, -12, 3, 0], ![-585, -345, -27, 6]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 3 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R631RS1]  
      rfl
    g := ![![![-1189, 2774, 783, -45], ![-4867, -1722, 0, 0]], ![![-311, 866, 239, -14], ![-1478, -523, 0, 0]]]
    h := ![![![-11783, 3691395, 20855, 8], ![38927, -12195336, -5048, 0]], ![![-142710, 44968984, 255116, 103], ![471465, -148564924, -64991, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R631N1 : Ideal.span {3} * I631N1 =  Ideal.span {B.equivFun.symm ![-16, -4, 1, 0]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E631RS1
                    

noncomputable def R631RS2 : IdealMulPrincipalCertificate timesTableO (J0 ^ 1*J1^ 1) ![-153, -73, -4, 1] ![![3, 0, 0, 0], ![-131, -67, -4, 1]]
  ![![-459, -219, -12, 3], ![510, 201, 6, -3]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

noncomputable def E631RS2 : IdealEqCertificateO timesTableO (Ideal.span {3} * I631N2) (Ideal.span {B.equivFun.symm ![-153, -73, -4, 1]} * (J0 ^ 1*J1^ 1)) 
      ![![1893, 0, 0, 0], ![885, 3, 0, 0]] ![![-459, -219, -12, 3], ![510, 201, 6, -3]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 3 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R631RS2]  
      rfl
    g := ![![![1144366, -2425343, -733440, 36201], ![5189036, 1765858, 0, 0]], ![![537311, -1138541, -344313, 16994], ![2436012, 828988, 0, 0]]]
    h := ![![![-129408, 72002416, 287737, 148], ![276801, -154012886, -93387, 0]], ![![142410, -80006901, -319886, -165], ![-304612, 171134438, 104114, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R631N2 : Ideal.span {3} * I631N2 =  Ideal.span {B.equivFun.symm ![-153, -73, -4, 1]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E631RS2
                    
