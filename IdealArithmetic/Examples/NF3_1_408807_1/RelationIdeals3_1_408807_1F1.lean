import IdealArithmetic.Examples.NF3_1_408807_1.PrimesBelow3_1_408807_1F1
import IdealArithmetic.Examples.NF3_1_408807_1.ClassGroupData3_1_408807_1

set_option linter.all false

noncomputable section


noncomputable def E37RS1 : RelationCertificate Table 275 ![![37, 0, 0], ![-13, 1, 0]]
  ![-184, -15, -4] ![![275, 0, 0], ![-80, 1, 0]] where
    su := ![![10175, 0, 0], ![-3575, 275, 0]]
    hsu := by decide
    w := ![![-50600, -4125, -1100], ![14300, 1100, 275]]
    hw := by decide
    g := ![![![-19099, -19596508, 734878], ![-65652, -67363817, 0]], ![![6860, 6973461, -261508], ![23581, 23971567, 0]]]
    h := ![![![-844388, 70481, -1276], ![-2403244, 15736, 0]], ![![238654, -19909, 358], ![679242, -4415, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {275} * I37N1 =  Ideal.span {B.equivFun.symm ![-184, -15, -4]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E37RS1 


noncomputable def E43RS1 : RelationCertificate Table 55 ![![43, 0, 0], ![-14, 1, 0]]
  ![46, -10, 1] ![![55, 0, 0], ![-25, 1, 0]] where
    su := ![![2365, 0, 0], ![-770, 55, 0]]
    hsu := by decide
    w := ![![2530, -550, 55], ![-1045, 275, -55]]
    hw := by decide
    g := ![![![9, 134, -16], ![14, 295, 0]], ![![628, 88658, -10642], ![1383, 195103, 0]]]
    h := ![![![36950, -2868, 49], ![113486, -702, 0]], ![![-15237, 1191, -22], ![-46798, 315, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {55} * I43N1 =  Ideal.span {B.equivFun.symm ![46, -10, 1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E43RS1 


noncomputable def E47RS1 : RelationCertificate Table 5 ![![47, 0, 0], ![-23, 1, 0]]
  ![4, 0, -1] ![![5, 0, 0], ![0, 1, 0]] where
    su := ![![235, 0, 0], ![-115, 5, 0]]
    hsu := by decide
    w := ![![20, 0, -5], ![-105, 25, 0]]
    hw := by decide
    g := ![![![-25, -2, -1], ![3, 0, 0]], ![![10, 0, -14], ![3, 24, 0]]]
    h := ![![![510, -7, -2], ![1042, 31, 0]], ![![-2482, 131, -3], ![-5071, 47, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {5} * I47N1 =  Ideal.span {B.equivFun.symm ![4, 0, -1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E47RS1 


noncomputable def E53RS1 : RelationCertificate Table 11 ![![53, 0, 0], ![22, 1, 0]]
  ![2, 1, 1] ![![11, 0, 0], ![-3, 1, 0]] where
    su := ![![583, 0, 0], ![242, 11, 0]]
    hsu := by decide
    w := ![![22, 11, 11], ![99, -22, 0]]
    hw := by decide
    g := ![![![4, -37, 37], ![5, -135, 0]], ![![2, -23, 23], ![2, -84, 0]]]
    h := ![![![186, 1, -1], ![-448, 18, 0]], ![![947, 43, 0], ![-2281, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {11} * I53N1 =  Ideal.span {B.equivFun.symm ![2, 1, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E53RS1 


noncomputable def E59RS0 : RelationCertificate Table 11 ![![59, 0, 0], ![3, 1, 0]]
  ![59, 2, 2] ![![11, 0, 0], ![-3, 1, 0]] where
    su := ![![649, 0, 0], ![33, 11, 0]]
    hsu := by decide
    w := ![![649, 22, 22], ![33, 11, 0]]
    hw := by decide
    g := ![![![1, -80, 80], ![0, -294, 0]], ![![0, -9, 9], ![1, -33, 0]]]
    h := ![![![55, 16, -2], ![-1062, 40, 0]], ![![-3, -1, 0], ![60, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N0 : Ideal.span {11} * I59N0 =  Ideal.span {B.equivFun.symm ![59, 2, 2]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E59RS0 


noncomputable def E59RS1 : RelationCertificate Table 605 ![![59, 0, 0], ![26, 1, 0]]
  ![923, 60, 38] ![![605, 0, 0], ![250, 1, 0]] where
    su := ![![35695, 0, 0], ![15730, 605, 0]]
    hsu := by decide
    w := ![![558415, 36300, 22990], ![234740, 15125, 9680]]
    hw := by decide
    g := ![![![-14504069, 24861198649, 298335080], ![35099847, -60164241130, 0]], ![![-836558776, 1433945036681, 17207380595], ![2024472238, -3470155086657, 0]]]
    h := ![![![7007, 325, 7], ![-15865, -125, 0]], ![![2908, 127, 2], ![-6584, -34, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {605} * I59N1 =  Ideal.span {B.equivFun.symm ![923, 60, 38]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E59RS1 


noncomputable def E59RS2 : RelationCertificate Table 25 ![![59, 0, 0], ![-29, 1, 0]]
  ![-17, 5, -2] ![![25, 0, 0], ![-5, 1, 0]] where
    su := ![![1475, 0, 0], ![-725, 25, 0]]
    hsu := by decide
    w := ![![-425, 125, -50], ![-125, 0, 25]]
    hw := by decide
    g := ![![![-567, -73520, 44179], ![-2809, -368160, 0]], ![![282, 36261, -21790], ![1399, 181584, 0]]]
    h := ![![![-12632, 532, -10], ![-25699, 196, 0]], ![![-3688, 166, -4], ![-7503, 79, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N2 : Ideal.span {25} * I59N2 =  Ideal.span {B.equivFun.symm ![-17, 5, -2]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E59RS2 


noncomputable def E67RS1 : RelationCertificate Table 605 ![![67, 0, 0], ![-7, 1, 0]]
  ![-268, 75, -13] ![![605, 0, 0], ![250, 1, 0]] where
    su := ![![40535, 0, 0], ![-4235, 605, 0]]
    hsu := by decide
    w := ![![-162140, 45375, -7865], ![-68365, 18755, -3025]]
    hw := by decide
    g := ![![![103316969, -177095947395, -2125156328], ![-250027068, 428573192804, 0]], ![![-8288633, 14207399762, 170489195], ![20058492, -34381987658, 0]]]
    h := ![![![-1201904, 173453, -751], ![-11503900, 16768, 0]], ![![-506767, 73135, -317], ![-4850468, 7078, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {605} * I67N1 =  Ideal.span {B.equivFun.symm ![-268, 75, -13]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E67RS1 


noncomputable def E71RS1 : RelationCertificate Table 3025 ![![71, 0, 0], ![-33, 1, 0]]
  ![2213, 155, 78] ![![3025, 0, 0], ![-355, 1, 0]] where
    su := ![![214775, 0, 0], ![-99825, 3025, 0]]
    hsu := by decide
    w := ![![6694325, 468875, 235950], ![-777425, -54450, -27225]]
    hw := by decide
    g := ![![![1185, 25405572, -214695], ![10097, 216484128, 0]], ![![-436, -11808009, 99786], ![-3715, -100617552, 0]]]
    h := ![![![42181, -1428, 15], ![90686, -329, 0]], ![![-4843, 178, -3], ![-10412, 68, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {3025} * I71N1 =  Ideal.span {B.equivFun.symm ![2213, 155, 78]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E71RS1 


noncomputable def E73RS1 : RelationCertificate Table 605 ![![73, 0, 0], ![-13, 1, 0]]
  ![-397, 5, -17] ![![605, 0, 0], ![250, 1, 0]] where
    su := ![![44165, 0, 0], ![-7865, 605, 0]]
    hsu := by decide
    w := ![![-240185, 3025, -10285], ![-101035, 1210, -4235]]
    hw := by decide
    g := ![![![34693126, -59467615311, -713613049], ![-83957365, 143911964882, 0]], ![![-3517119, 6028466015, 72341761], ![8511428, -14588921802, 0]]]
    h := ![![![-3533708, 279202, -1703], ![-19843099, 41434, 0]], ![![-1486462, 117454, -718], ![-8347043, 17469, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {605} * I73N1 =  Ideal.span {B.equivFun.symm ![-397, 5, -17]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E73RS1 
