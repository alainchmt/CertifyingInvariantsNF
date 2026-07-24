import IdealArithmetic.Examples.NF3_1_393835_1.PrimesBelow3_1_393835_1F0
import IdealArithmetic.Examples.NF3_1_393835_1.ClassGroupData3_1_393835_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 2 ![![2, 0, 0], ![0, 1, 0]]
  ![116, 11, -2] ![![2, 0, 0], ![-51, -5, 1]] where
    su := ![![4, 0, 0], ![0, 2, 0]]
    hsu := by decide
    w := ![![232, 22, -4], ![-596, -162, 20]]
    hw := by decide
    g := ![![![37, -22, -6], ![5, 0, 0]], ![![20, -137, -29], ![20, 0, 0]]]
    h := ![![![58, 4, 0], ![3, -2, 0]], ![![-149, -33, 0], ![-15, 10, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {2} * I2N0 =  Ideal.span {B.equivFun.symm ![116, 11, -2]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 1 ![![2, 0, 0], ![-51, -5, 1]]
  ![1, 0, 0] ![![2, 0, 0], ![-51, -5, 1]] where
    su := ![![2, 0, 0], ![-51, -5, 1]]
    hsu := by decide
    w := ![![2, 0, 0], ![-51, -5, 1]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {1} * I2N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS1 


noncomputable def E3RS0 : RelationCertificate Table 1 ![![3, 0, 0], ![-52, -5, 1]]
  ![1, 0, 0] ![![3, 0, 0], ![-52, -5, 1]] where
    su := ![![3, 0, 0], ![-52, -5, 1]]
    hsu := by decide
    w := ![![3, 0, 0], ![-52, -5, 1]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {1} * I3N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 3 ![![3, 0, 0], ![1, 1, 0]]
  ![-671, -256, -26] ![![3, 0, 0], ![-52, -5, 1]] where
    su := ![![9, 0, 0], ![3, 3, 0]]
    hsu := by decide
    w := ![![-2013, -768, -78], ![-7668, -2925, -297]]
    hw := by decide
    g := ![![![27, -6, 0], ![10, 0, 0]], ![![37, 12, -1], ![-13, 0, 0]]]
    h := ![![![-183, -183, -147], ![-122, 415, 0]], ![![-698, -698, -560], ![-462, 1581, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {3} * I3N1 =  Ideal.span {B.equivFun.symm ![-671, -256, -26]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E3RS1 


noncomputable def E5RS1 : RelationCertificate Table 6 ![![5, 0, 0], ![2, 1, 0]]
  ![-56402, -21516, -2185] ![![6, 0, 0], ![-49, -5, 1]] where
    su := ![![30, 0, 0], ![12, 6, 0]]
    hsu := by decide
    w := ![![-338412, -129096, -13110], ![-813582, -310362, -31518]]
    hw := by decide
    g := ![![![10, 83, -6], ![-85, 0, 0]], ![![18, -36, 1], ![106, 0, 0]]]
    h := ![![![-418854, -249602, -21193], ![1018934, 103780, 0]], ![![-1006969, -600067, -50949], ![2449624, 249492, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {6} * I5N1 =  Ideal.span {B.equivFun.symm ![-56402, -21516, -2185]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E5RS1 


noncomputable def E7RS0 : RelationCertificate Table 2 ![![7, 0, 0], ![0, 1, 0]]
  ![36946, 3189, -608] ![![2, 0, 0], ![-51, -5, 1]] where
    su := ![![14, 0, 0], ![0, 2, 0]]
    hsu := by decide
    w := ![![73892, 6378, -1216], ![-310366, -62308, 8382]]
    hw := by decide
    g := ![![![240679, -2724428, -570421], ![389649, 0, 0]], ![![372938, -4221751, -883919], ![603796, 0, 0]]]
    h := ![![![5278, 446, 0], ![67, -608, 0]], ![![-22169, -4362, 0], ![-620, 4191, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {2} * I7N0 =  Ideal.span {B.equivFun.symm ![36946, 3189, -608]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 2 ![![7, 0, 0], ![-53, -8, 1]]
  ![-22122, -8439, -857] ![![2, 0, 0], ![-51, -5, 1]] where
    su := ![![14, 0, 0], ![-106, -16, 2]]
    hsu := by decide
    w := ![![-44244, -16878, -1714], ![-274858, -104852, -10648]]
    hw := by decide
    g := ![![![35, 47, -5], ![7, 0, 0]], ![![9, 81, -2], ![-105, 0, 0]]]
    h := ![![![50, -721, -183], ![424, 0, 0]], ![![318, -4478, -1137], ![2635, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {2} * I7N1 =  Ideal.span {B.equivFun.symm ![-22122, -8439, -857]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E7RS1 


noncomputable def E13RS0 : RelationCertificate Table 3 ![![13, 0, 0], ![2, 1, 0]]
  ![-11, 1, 0] ![![3, 0, 0], ![-52, -5, 1]] where
    su := ![![39, 0, 0], ![6, 3, 0]]
    hsu := by decide
    w := ![![-33, 3, 0], ![852, 84, -15]]
    hw := by decide
    g := ![![![25, 0, -1], ![2, 0, 0]], ![![26, 0, -1], ![2, 0, 0]]]
    h := ![![![-49, -26, -1], ![313, 13, 0]], ![![1232, 622, 7], ![-7866, -96, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {3} * I13N0 =  Ideal.span {B.equivFun.symm ![-11, 1, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E13RS0 


noncomputable def E19RS0 : RelationCertificate Table 2 ![![19, 0, 0], ![9, 1, 0]]
  ![351985962, 134274173, 13635858] ![![2, 0, 0], ![-51, -5, 1]] where
    su := ![![38, 0, 0], ![18, 2, 0]]
    hsu := by decide
    w := ![![703971924, 268548346, 27271716], ![4373323418, 1668317628, 169421578]]
    hw := by decide
    g := ![![![-1554, 8615, -1740], ![18163, 0, 0]], ![![-169, 369, -264], ![4383, 0, 0]]]
    h := ![![![1960737906, 343504299, 14121662], ![-4100226028, -254675720, 0]], ![![12180799711, 2133970638, 87728779], ![-25472059200, -1582136012, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N0 : Ideal.span {2} * I19N0 =  Ideal.span {B.equivFun.symm ![351985962, 134274173, 13635858]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E19RS0 


noncomputable def E19RS1 : RelationCertificate Table 6 ![![19, 0, 0], ![-9, 1, 0]]
  ![262186, 104552, -11867] ![![6, 0, 0], ![-49, -5, 1]] where
    su := ![![114, 0, 0], ![-54, 6, 0]]
    hsu := by decide
    w := ![![1573116, 627312, -71202], ![29718486, 2556882, -488298]]
    hw := by decide
    g := ![![![72030866, -1669561837, -356421426], ![743645983, 0, 0]], ![![7002693, -162311094, -34650500], ![72295613, 0, 0]]]
    h := ![![![14823628, -1923638, 30887], ![31265194, -598720, 0]], ![![283375731, -36777507, 589351], ![597687312, -11279052, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {6} * I19N1 =  Ideal.span {B.equivFun.symm ![262186, 104552, -11867]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E19RS1 


noncomputable def E19RS2 : RelationCertificate Table 3 ![![19, 0, 0], ![-1, 1, 0]]
  ![-27, -10, -1] ![![3, 0, 0], ![-52, -5, 1]] where
    su := ![![57, 0, 0], ![-3, 3, 0]]
    hsu := by decide
    w := ![![-81, -30, -3], ![-276, -111, -12]]
    hw := by decide
    g := ![![![27, 8, -1], ![1, 0, 0]], ![![7, -1, 0], ![1, 0, 0]]]
    h := ![![![-2, 1, -1], ![-11, 18, 0]], ![![-10, 4, -1], ![-98, 15, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N2 : Ideal.span {3} * I19N2 =  Ideal.span {B.equivFun.symm ![-27, -10, -1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E19RS2 


noncomputable def E23RS1 : RelationCertificate Table 2 ![![23, 0, 0], ![6, 1, 0]]
  ![6, 1, 0] ![![2, 0, 0], ![-51, -5, 1]] where
    su := ![![46, 0, 0], ![12, 2, 0]]
    hsu := by decide
    w := ![![12, 2, 0], ![-26, 0, 2]]
    hw := by decide
    g := ![![![6, -1, 0], ![1, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    h := ![![![-6, -1, 0], ![24, 0, 0]], ![![-23, -4, 0], ![86, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {2} * I23N1 =  Ideal.span {B.equivFun.symm ![6, 1, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E23RS1 


noncomputable def E29RS1 : RelationCertificate Table 3 ![![29, 0, 0], ![11, 1, 0]]
  ![-94967, -16150, 2296] ![![3, 0, 0], ![-52, -5, 1]] where
    su := ![![87, 0, 0], ![33, 3, 0]]
    hsu := by decide
    w := ![![-284901, -48450, 6888], ![-2155236, -94539, 27033]]
    hw := by decide
    g := ![![![-2887603, 36021052, 7430550], ![-7506214, 0, 0]], ![![-2175337, 27136448, 5597801], ![-5654801, 0, 0]]]
    h := ![![![-239073, -25218, -214], ![621650, 8502, 0]], ![![-1802300, -187449, -1941], ![4686208, 65300, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {3} * I29N1 =  Ideal.span {B.equivFun.symm ![-94967, -16150, 2296]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E29RS1 
