import IdealArithmetic.Examples.NF3_1_251451_1.PrimesBelow3_1_251451_1F1
import IdealArithmetic.Examples.NF3_1_251451_1.ClassGroupData3_1_251451_1

set_option linter.all false

noncomputable section


noncomputable def E37RS0 : RelationCertificate Table 14 ![![37, 0, 0], ![6, 1, 0]]
  ![1, 0, 1] ![![14, 0, 0], ![21, 1, 1]] where
    su := ![![518, 0, 0], ![84, 14, 0]]
    hsu := by decide
    w := ![![14, 0, 14], ![70, 14, -14]]
    hw := by decide
    g := ![![![-14, -2, -1], ![20, -1, 0]], ![![-6, -9, -1], ![22, -7, 0]]]
    h := ![![![61, 10, 0], ![-376, 1, 0]], ![![305, 51, 0], ![-1880, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N0 : Ideal.span {14} * I37N0 =  Ideal.span {B.equivFun.symm ![1, 0, 1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E37RS0 


noncomputable def E37RS2 : RelationCertificate Table 14 ![![37, 0, 0], ![-17, 1, 0]]
  ![-727, 567, -6] ![![14, 0, 0], ![21, 1, 1]] where
    su := ![![518, 0, 0], ![-238, 14, 0]]
    hsu := by decide
    w := ![![-10178, 7938, -84], ![12222, -9310, -70]]
    hw := by decide
    g := ![![![37682, 187, -788], ![56521, 0, 0]], ![![-16014, -83, 333], ![-23962, -2, 0]]]
    h := ![![![-216318, 14470, -102], ![-470767, 3768, 0]], ![![259728, -17354, 121], ![565239, -4482, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N2 : Ideal.span {14} * I37N2 =  Ideal.span {B.equivFun.symm ![-727, 567, -6]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E37RS2 


noncomputable def E43RS0 : RelationCertificate Table 2 ![![43, 0, 0], ![1, 1, 0]]
  ![1, 1, 0] ![![2, 0, 0], ![25, 1, 1]] where
    su := ![![86, 0, 0], ![2, 2, 0]]
    hsu := by decide
    w := ![![2, 2, 0], ![74, -10, 2]]
    hw := by decide
    g := ![![![-19, -2, -1], ![3, 0, 0]], ![![-24, -1, -1], ![2, 0, 0]]]
    h := ![![![0, 0, 0], ![1, 0, 0]], ![![0, -1, 0], ![37, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N0 : Ideal.span {2} * I43N0 =  Ideal.span {B.equivFun.symm ![1, 1, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E43RS0 


noncomputable def E43RS2 : RelationCertificate Table 2 ![![43, 0, 0], ![-3, 1, 0]]
  ![-3, 1, 0] ![![2, 0, 0], ![25, 1, 1]] where
    su := ![![86, 0, 0], ![-6, 2, 0]]
    hsu := by decide
    w := ![![-6, 2, 0], ![-26, -14, -2]]
    hw := by decide
    g := ![![![-10, -1, 0], ![-1, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    h := ![![![-15, 8, -1], ![-214, 43, 0]], ![![-67, 25, -1], ![-956, 42, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N2 : Ideal.span {2} * I43N2 =  Ideal.span {B.equivFun.symm ![-3, 1, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E43RS2 


noncomputable def E47RS1 : RelationCertificate Table 14 ![![47, 0, 0], ![12, 1, 0]]
  ![417, 14, 11] ![![14, 0, 0], ![21, 1, 1]] where
    su := ![![658, 0, 0], ![168, 14, 0]]
    hsu := by decide
    w := ![![5838, 196, 154], ![9982, 350, 266]]
    hw := by decide
    g := ![![![172, -184, -7], ![249, -156, 0]], ![![51, -54, -2], ![73, -46, 0]]]
    h := ![![![399, 30, 0], ![-1528, 11, 0]], ![![703, 53, 0], ![-2694, 19, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {14} * I47N1 =  Ideal.span {B.equivFun.symm ![417, 14, 11]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E47RS1 


noncomputable def E59RS0 : RelationCertificate Table 2 ![![59, 0, 0], ![5, 1, 0]]
  ![-7915, -273, -210] ![![2, 0, 0], ![25, 1, 1]] where
    su := ![![118, 0, 0], ![10, 2, 0]]
    hsu := by decide
    w := ![![-15830, -546, -420], ![-221542, -7642, -5878]]
    hw := by decide
    g := ![![![-12, -55, 8], ![5, 0, 0]], ![![-12, -11, -1], ![2, 0, 0]]]
    h := ![![![-7915, -1573, -6], ![91814, 144, 0]], ![![-110659, -21982, -82], ![1283622, 1899, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N0 : Ideal.span {2} * I59N0 =  Ideal.span {B.equivFun.symm ![-7915, -273, -210]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E59RS0 


noncomputable def E59RS1 : RelationCertificate Table 7 ![![59, 0, 0], ![13, 1, 0]]
  ![-12174, -420, -323] ![![7, 0, 0], ![0, 1, 0]] where
    su := ![![413, 0, 0], ![91, 7, 0]]
    hsu := by decide
    w := ![![-85218, -2940, -2261], ![-15827, -546, -420]]
    hw := by decide
    g := ![![![-24, 19, -23], ![4, 155, 0]], ![![-6, 4, -5], ![3, 36, 0]]]
    h := ![![![-698294, -57574, -303], ![3168244, 17554, 0]], ![![-129699, -10703, -57], ![588460, 3303, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {7} * I59N1 =  Ideal.span {B.equivFun.symm ![-12174, -420, -323]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E59RS1 


noncomputable def E59RS2 : RelationCertificate Table 14 ![![59, 0, 0], ![-18, 1, 0]]
  ![68, -77, 19] ![![14, 0, 0], ![21, 1, 1]] where
    su := ![![826, 0, 0], ![-252, 14, 0]]
    hsu := by decide
    w := ![![952, -1078, 266], ![-1414, 1470, -294]]
    hw := by decide
    g := ![![![2079, 10, -44], ![3135, 0, 0]], ![![-490, -117, 8], ![-729, -96, 0]]]
    h := ![![![676, -33, 0], ![2212, 19, 0]], ![![-949, 66, -1], ![-3105, 38, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N2 : Ideal.span {14} * I59N2 =  Ideal.span {B.equivFun.symm ![68, -77, 19]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E59RS2 


noncomputable def E67RS1 : RelationCertificate Table 7 ![![67, 0, 0], ![-16, 1, 0]]
  ![-318, 203, 32] ![![7, 0, 0], ![0, 1, 0]] where
    su := ![![469, 0, 0], ![-112, 7, 0]]
    hsu := by decide
    w := ![![-2226, 1421, 224], ![1568, -1470, 203]]
    hw := by decide
    g := ![![![67880, 2294, 1801], ![332, 0, 0]], ![![-14893, -504, -402], ![-68, 48, 0]]]
    h := ![![![-2090, 141, 0], ![-8732, 32, 0]], ![![1504, -90, 0], ![6284, 29, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {7} * I67N1 =  Ideal.span {B.equivFun.symm ![-318, 203, 32]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E67RS1 


noncomputable def E71RS1 : RelationCertificate Table 7 ![![71, 0, 0], ![31, 1, 0]]
  ![-2035, -70, -54] ![![7, 0, 0], ![0, 1, 0]] where
    su := ![![497, 0, 0], ![217, 7, 0]]
    hsu := by decide
    w := ![![-14245, -490, -378], ![-2646, -91, -70]]
    hw := by decide
    g := ![![![11, -9, -28], ![1, 198, 0]], ![![5, -4, -14], ![1, 98, 0]]]
    h := ![![![-184838, -8171, -72], ![423273, 5058, 0]], ![![-34328, -1537, -14], ![78610, 984, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {7} * I71N1 =  Ideal.span {B.equivFun.symm ![-2035, -70, -54]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E71RS1 


noncomputable def E73RS1 : RelationCertificate Table 7 ![![73, 0, 0], ![19, 1, 0]]
  ![-313130, -10801, -8308] ![![7, 0, 0], ![0, 1, 0]] where
    su := ![![511, 0, 0], ![133, 7, 0]]
    hsu := by decide
    w := ![![-2191910, -75607, -58156], ![-407092, -14042, -10801]]
    hw := by decide
    g := ![![![108, -65, -131], ![-3, 822, 0]], ![![19, -9, -37], ![1, 228, 0]]]
    h := ![![![-26506504, -1527777, -7102], ![101824298, 510138, 0]], ![![-4922920, -283746, -1319], ![18911316, 94744, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {7} * I73N1 =  Ideal.span {B.equivFun.symm ![-313130, -10801, -8308]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E73RS1 


noncomputable def E79RS1 : RelationCertificate Table 14 ![![79, 0, 0], ![20, 1, 0]]
  ![194, 7, 5] ![![14, 0, 0], ![21, 1, 1]] where
    su := ![![1106, 0, 0], ![280, 14, 0]]
    hsu := by decide
    w := ![![2716, 98, 70], ![4662, 154, 126]]
    hw := by decide
    g := ![![![3278175, -3476270, -123310], ![4660176, -2933839, 0]], ![![856289, -908050, -32211], ![1217312, -766359, 0]]]
    h := ![![![166, 7, 0], ![-646, 5, 0]], ![![307, 13, 0], ![-1196, 9, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {14} * I79N1 =  Ideal.span {B.equivFun.symm ![194, 7, 5]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E79RS1 
