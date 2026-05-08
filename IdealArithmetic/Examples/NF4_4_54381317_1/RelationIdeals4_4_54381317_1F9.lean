import IdealArithmetic.Examples.NF4_4_54381317_1.PrimesBelow4_4_54381317_1F9
import IdealArithmetic.Examples.NF4_4_54381317_1.ClassGroupData4_4_54381317_1

    set_option linter.all false

    noncomputable section

noncomputable def R467RS1 : IdealMulPrincipalCertificate timesTableO (J0 ^ 0*J1^ 2) ![896, 465, 29, -7] ![![9, 0, 0, 0], ![-2, 1, 0, 0]]
  ![![8064, 4185, 261, -63], ![-4473, -2358, -153, 36]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_2
    hmul := by decide

noncomputable def E467RS1 : IdealEqCertificateO timesTableO (Ideal.span {9} * I467N1) (Ideal.span {B.equivFun.symm ![896, 465, 29, -7]} * (J0 ^ 0*J1^ 2)) 
      ![![4203, 0, 0, 0], ![1296, 9, 0, 0]] ![![8064, 4185, 261, -63], ![-4473, -2358, -153, 36]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R467RS1]  
      rfl
    g := ![![![-770477361, -32745294518, 16566107265, -420290], ![-3467148861, -149087400136, 3782600, 0]], ![![-300486182, -12770664803, 6460781799, -163913], ![-1352188042, -58144085748, 1475214, 0]]]
    h := ![![![58864, -3966390, -29993, -17], ![-190893, 12864552, 7932, 0]], ![![-33019, 2199841, 16573, 9], ![107079, -7134952, -4199, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R467N1 : Ideal.span {9} * I467N1 =  Ideal.span {B.equivFun.symm ![896, 465, 29, -7]} * (J0 ^ 0*J1^ 2) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E467RS1
                    

noncomputable def R467RS2 : IdealMulPrincipalCertificate timesTableO (J0 ^ 2*J1^ 0) ![-1087, -503, -24, 7] ![![9, 0, 0, 0], ![-4, 1, 0, 0]]
  ![![-9783, -4527, -216, 63], ![7029, 3249, 153, -45]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_2J1_0
    hmul := by decide

noncomputable def E467RS2 : IdealEqCertificateO timesTableO (Ideal.span {9} * I467N2) (Ideal.span {B.equivFun.symm ![-1087, -503, -24, 7]} * (J0 ^ 2*J1^ 0)) 
      ![![4203, 0, 0, 0], ![-450, 9, 0, 0]] ![![-9783, -4527, -216, 63], ![7029, 3249, 153, -45]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R467RS2]  
      rfl
    g := ![![![507404468700, 12304558368766, -3107875973066, 5900389], ![1141660054887, 27970671343600, -53103492, 0]], ![![-51318685579, -1244478125678, 314329336323, -596763], ![-115467042588, -2828942543440, 5370866, 0]]]
    h := ![![![-980811, 13364100, -269889, 60], ![-9160753, 124637489, -28013, 0]], ![![704793, -9602120, 193960, -44], ![6582751, -89552153, 20543, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R467N2 : Ideal.span {9} * I467N2 =  Ideal.span {B.equivFun.symm ![-1087, -503, -24, 7]} * (J0 ^ 2*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E467RS2
                    

noncomputable def R491RS0 : IdealMulPrincipalCertificate timesTableO (J0 ^ 1*J1^ 1) ![258, 137, 8, -2] ![![3, 0, 0, 0], ![-131, -67, -4, 1]]
  ![![774, 411, 24, -6], ![1821, 1005, 63, -15]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

noncomputable def E491RS0 : IdealEqCertificateO timesTableO (Ideal.span {3} * I491N0) (Ideal.span {B.equivFun.symm ![258, 137, 8, -2]} * (J0 ^ 1*J1^ 1)) 
      ![![1473, 0, 0, 0], ![-696, 3, 0, 0]] ![![774, 411, 24, -6], ![1821, 1005, 63, -15]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 3 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R491RS0]  
      rfl
    g := ![![![401, -733, -220, 12], ![1416, 491, 0, 0]], ![![-145, 368, 105, -6], ![-665, -231, 0, 0]]]
    h := ![![![373014, -15213135, 77630, -52], ![789438, -32193362, 25530, 0]], ![![878005, -35782666, 182521, -122], ![1858189, -75721686, 59897, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R491N0 : Ideal.span {3} * I491N0 =  Ideal.span {B.equivFun.symm ![258, 137, 8, -2]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E491RS0
                    

noncomputable def R491RS1 : IdealMulPrincipalCertificate timesTableO (J0 ^ 0*J1^ 1) ![-289, -138, -7, 2] ![![3, 0, 0, 0], ![1, 1, 0, 0]]
  ![![-867, -414, -21, 6], ![477, 237, 15, -3]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

noncomputable def E491RS1 : IdealEqCertificateO timesTableO (Ideal.span {3} * I491N1) (Ideal.span {B.equivFun.symm ![-289, -138, -7, 2]} * (J0 ^ 0*J1^ 1)) 
      ![![1473, 0, 0, 0], ![-348, 3, 0, 0]] ![![-867, -414, -21, 6], ![477, 237, 15, -3]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 3 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R491RS1]  
      rfl
    g := ![![![103103, -1044888, -1148332, 367], ![-313926, 3445791, -1052, 0]], ![![-24096, 244344, 268527, -86], ![73417, -805764, 246, 0]]]
    h := ![![![-197911, 15974147, -144885, 62], ![-837707, 67607488, -30440, 0]], ![![109149, -8787271, 79804, -35], ![462000, -37190415, 17184, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R491N1 : Ideal.span {3} * I491N1 =  Ideal.span {B.equivFun.symm ![-289, -138, -7, 2]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E491RS1
                    

noncomputable def R491RS2 : IdealMulPrincipalCertificate timesTableO (J0 ^ 1*J1^ 1) ![-135, -70, -4, 1] ![![3, 0, 0, 0], ![-131, -67, -4, 1]]
  ![![-405, -210, -12, 3], ![-699, -402, -27, 6]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

noncomputable def E491RS2 : IdealEqCertificateO timesTableO (Ideal.span {3} * I491N2) (Ideal.span {B.equivFun.symm ![-135, -70, -4, 1]} * (J0 ^ 1*J1^ 1)) 
      ![![1473, 0, 0, 0], ![-342, 3, 0, 0]] ![![-405, -210, -12, 3], ![-699, -402, -27, 6]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 3 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R491RS2]  
      rfl
    g := ![![![-386, 1001, 290, -16], ![-1894, -653, 0, 0]], ![![180, -184, -64, 3], ![437, 150, 0, 0]]]
    h := ![![![-4401, 762040, -7026, 3], ![-18954, 3281954, -1472, 0]], ![![-7573, 1314651, -12101, 5], ![-32615, 5661940, -2453, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R491N2 : Ideal.span {3} * I491N2 =  Ideal.span {B.equivFun.symm ![-135, -70, -4, 1]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E491RS2
                    

noncomputable def R491RS3 : IdealMulPrincipalCertificate timesTableO (J0 ^ 1*J1^ 0) ![605, 331, 21, -5] ![![3, 0, 0, 0], ![-1, 1, 0, 0]]
  ![![1815, 993, 63, -15], ![-2520, -1386, -90, 21]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

noncomputable def E491RS3 : IdealEqCertificateO timesTableO (Ideal.span {3} * I491N3) (Ideal.span {B.equivFun.symm ![605, 331, 21, -5]} * (J0 ^ 1*J1^ 0)) 
      ![![1473, 0, 0, 0], ![-90, 3, 0, 0]] ![![1815, 993, 63, -15], ![-2520, -1386, -90, 21]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 3 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R491RS3]  
      rfl
    g := ![![![-3009276, -30143105, 33163243, -2654], ![-9044609, -99481510, 7856, 0]], ![![177701, 1780327, -1958727, 157], ![534211, 5875693, -464, 0]]]
    h := ![![![49945, -1042, 4992039, -166402], ![817413, 10182, 81703377, 0]], ![![-69300, 1480, -6965582, 232187], ![-1134182, -13568, -114003810, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R491N3 : Ideal.span {3} * I491N3 =  Ideal.span {B.equivFun.symm ![605, 331, 21, -5]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E491RS3
                    

noncomputable def R509RS1 : IdealMulPrincipalCertificate timesTableO (J0 ^ 1*J1^ 2) ![95, 63, 5, -1] ![![9, 0, 0, 0], ![-564, -280, -15, 4]]
  ![![855, 567, 45, -9], ![10764, 5517, 315, -81]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_2
    hmul := by decide

noncomputable def E509RS1 : IdealEqCertificateO timesTableO (Ideal.span {9} * I509N1) (Ideal.span {B.equivFun.symm ![95, 63, 5, -1]} * (J0 ^ 1*J1^ 2)) 
      ![![4581, 0, 0, 0], ![1224, 9, 0, 0]] ![![855, 567, 45, -9], ![10764, 5517, 315, -81]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R509RS1]  
      rfl
    g := ![![![214720005417910410809, -603308220819157415574, 159719346153242360058, 26345405429897088394], ![5059312244787061998589, 1861305238910634605318, -11763152, 0]], ![![57442618271527790982, -161399045054693966031, 42728656856178636108, 7048011499314079197], ![1353484233703023705606, 497942639845984570416, -3146918, 0]]]
    h := ![![![5651, -434244, -3465, -2], ![-21149, 1625378, 1017, 0]], ![![75644, -5470787, -42948, -20], ![-283100, 20477311, 10171, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R509N1 : Ideal.span {9} * I509N1 =  Ideal.span {B.equivFun.symm ![95, 63, 5, -1]} * (J0 ^ 1*J1^ 2) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E509RS1
                    

noncomputable def R509RS2 : IdealMulPrincipalCertificate timesTableO (J0 ^ 2*J1^ 1) ![221, 130, 9, -2] ![![9, 0, 0, 0], ![-114, -104, -12, 2]]
  ![![1989, 1170, 81, -18], ![4680, 2646, 126, -36]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_2J1_1
    hmul := by decide

noncomputable def E509RS2 : IdealEqCertificateO timesTableO (Ideal.span {9} * I509N2) (Ideal.span {B.equivFun.symm ![221, 130, 9, -2]} * (J0 ^ 2*J1^ 1)) 
      ![![4581, 0, 0, 0], ![1818, 9, 0, 0]] ![![1989, 1170, 81, -18], ![4680, 2646, 126, -36]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R509RS2]  
      rfl
    g := ![![![-27400449261598621, 27682172433685711, 5835551095288643, -736585624909833], ![19245055369518003, 3186083971217942, -8753654, 0]], ![![-10968782671017403, 11081560392963295, 2336052636171445, -294865517024746], ![7704064551079748, 1275433928774312, -3504210, 0]]]
    h := ![![![10231, -345937, -2116, -2], ![-25779, 871821, 1016, 0]], ![![23966, -814267, -4636, -3], ![-60387, 2052092, 1523, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R509N2 : Ideal.span {9} * I509N2 =  Ideal.span {B.equivFun.symm ![221, 130, 9, -2]} * (J0 ^ 2*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E509RS2
                    

noncomputable def R541RS0 : IdealMulPrincipalCertificate timesTableO (J0 ^ 1*J1^ 2) ![206, 75, 2, -1] ![![9, 0, 0, 0], ![-564, -280, -15, 4]]
  ![![1854, 675, 18, -9], ![-20817, -10035, -522, 144]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_2
    hmul := by decide

noncomputable def E541RS0 : IdealEqCertificateO timesTableO (Ideal.span {9} * I541N0) (Ideal.span {B.equivFun.symm ![206, 75, 2, -1]} * (J0 ^ 1*J1^ 2)) 
      ![![4869, 0, 0, 0], ![1512, 9, 0, 0]] ![![1854, 675, 18, -9], ![-20817, -10035, -522, 144]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R541RS0]  
      rfl
    g := ![![![-3423834035053, 9620096712843, -2546816858364, -420092645133], ![-80673644571820, -29679582880500, 14066, 0]], ![![-1075881307221, 3022950915545, -800293654316, -132006931331], ![-25350313513925, -9326301482680, 4420, 0]]]
    h := ![![![20606, -2307578, -15080, -8], ![-66355, 7431346, 4327, 0]], ![![-232461, 25895995, 167586, 80], ![748566, -83395732, -43264, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R541N0 : Ideal.span {9} * I541N0 =  Ideal.span {B.equivFun.symm ![206, 75, 2, -1]} * (J0 ^ 1*J1^ 2) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E541RS0
                    

noncomputable def R541RS1 : IdealMulPrincipalCertificate timesTableO (J0 ^ 2*J1^ 1) ![-838, -461, -30, 7] ![![9, 0, 0, 0], ![-114, -104, -12, 2]]
  ![![-7542, -4149, -270, 63], ![-19368, -9684, -378, 126]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_2J1_1
    hmul := by decide

noncomputable def E541RS1 : IdealEqCertificateO timesTableO (Ideal.span {9} * I541N1) (Ideal.span {B.equivFun.symm ![-838, -461, -30, 7]} * (J0 ^ 2*J1^ 1)) 
      ![![4869, 0, 0, 0], ![1827, 9, 0, 0]] ![![-7542, -4149, -270, 63], ![-19368, -9684, -378, 126]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R541RS1]  
      rfl
    g := ![![![33117968444849, -33458477441335, -7053227307148, 890285382905], ![-23260827815701, -3850908589139, 28132, 0]], ![![12488106199000, -12616505153132, -2659627259573, 335708345990], ![-8771180772256, -1452098594271, 10608, 0]]]
    h := ![![![-5403, 19802, 95, 0], ![14395, -52846, 7, 0]], ![![-13032, 51766, 250, 0], ![34720, -138134, 14, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R541N1 : Ideal.span {9} * I541N1 =  Ideal.span {B.equivFun.symm ![-838, -461, -30, 7]} * (J0 ^ 2*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E541RS1
                    

noncomputable def R541RS2 : IdealMulPrincipalCertificate timesTableO (J0 ^ 2*J1^ 1) ![1415, 841, 69, -14] ![![9, 0, 0, 0], ![-114, -104, -12, 2]]
  ![![12735, 7569, 621, -126], ![-28026, -21024, -2898, 450]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_2J1_1
    hmul := by decide

noncomputable def E541RS2 : IdealEqCertificateO timesTableO (Ideal.span {9} * I541N2) (Ideal.span {B.equivFun.symm ![1415, 841, 69, -14]} * (J0 ^ 2*J1^ 1)) 
      ![![4869, 0, 0, 0], ![-1710, 9, 0, 0]] ![![12735, 7569, 621, -126], ![-28026, -21024, -2898, 450]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R541RS2]  
      rfl
    g := ![![![14928777944778, -15082271142679, -3179424018663, 401319085381], ![-10485417828927, -1735896387873, 233, 0]], ![![-5125761883755, 5178463423470, 1091647990715, -137791993336], ![3600144314678, 596016068566, -80, 0]]]
    h := ![![![220895, -31027741, 181343, -95], ![628962, -88344104, 51381, 0]], ![![-486024, 68242377, -398660, 208], ![-1383873, 194303918, -112478, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R541N2 : Ideal.span {9} * I541N2 =  Ideal.span {B.equivFun.symm ![1415, 841, 69, -14]} * (J0 ^ 2*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E541RS2
                    

noncomputable def R541RS3 : IdealMulPrincipalCertificate timesTableO (J0 ^ 1*J1^ 2) ![-260, -129, -11, 1] ![![9, 0, 0, 0], ![-564, -280, -15, 4]]
  ![![-2340, -1161, -99, 9], ![6462, 2979, 216, -27]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_2
    hmul := by decide

noncomputable def E541RS3 : IdealEqCertificateO timesTableO (Ideal.span {9} * I541N3) (Ideal.span {B.equivFun.symm ![-260, -129, -11, 1]} * (J0 ^ 1*J1^ 2)) 
      ![![4869, 0, 0, 0], ![-1638, 9, 0, 0]] ![![-2340, -1161, -99, 9], ![6462, 2979, 216, -27]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R541RS3]  
      rfl
    g := ![![![419435439465141647, -1178506158471343541, 311996797942086786, 51463284395862489], ![9882893075787608817, 3635885623879359831, -1387570, 0]], ![![-132453296824598492, 372159839942650187, -98525304725906332, -16251563512006019], ![-3120913606447544387, -1148174408853229500, 438180, 0]]]
    h := ![![![-48178, 6126442, -36936, 18], ![-143209, 18210231, -9737, 0]], ![![133772, -16919812, 102607, -53], ![397637, -50292423, 28670, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R541N3 : Ideal.span {9} * I541N3 =  Ideal.span {B.equivFun.symm ![-260, -129, -11, 1]} * (J0 ^ 1*J1^ 2) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E541RS3
                    
