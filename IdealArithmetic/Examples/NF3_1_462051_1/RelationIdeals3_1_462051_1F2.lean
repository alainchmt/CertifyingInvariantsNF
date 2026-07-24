import IdealArithmetic.Examples.NF3_1_462051_1.PrimesBelow3_1_462051_1F2
import IdealArithmetic.Examples.NF3_1_462051_1.ClassGroupData3_1_462051_1

set_option linter.all false

noncomputable section


noncomputable def E89RS1 : RelationCertificate Table 130321 ![![89, 0, 0], ![-22, 1, 0]]
  ![-129794, -47318, -6221] ![![130321, 0, 0], ![-36500, 1, 0]] where
    su := ![![11598569, 0, 0], ![-2867062, 130321, 0]]
    hsu := by decide
    w := ![![-16914883874, -6166529078, -810726941], ![4736516745, 1726753250, 227019182]]
    hw := by decide
    g := ![![![-1443423026206, -724314162983463246, 19844223644466], ![-5153652936937, -2586119069570453880, 0]], ![![342523183358, 171879193750313327, -4709019007115], ![1222957911737, 613684066026234000, 0]]]
    h := ![![![-379208594594, 18210677248, -44269322], ![-1534071126776, 3939963437, 0]], ![![106186236707, -5099365653, 12396324], ![429571592299, -1103271094, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {130321} * I89N1 =  Ideal.span {B.equivFun.symm ![-129794, -47318, -6221]} * (J0 ^ 4*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_0 E89RS1 


noncomputable def E97RS1 : RelationCertificate Table 6859 ![![97, 0, 0], ![-10, 1, 0]]
  ![-354, 262, 53] ![![6859, 0, 0], ![-2205, 1, 0]] where
    su := ![![665323, 0, 0], ![-68590, 6859, 0]]
    hsu := by decide
    w := ![![-2428086, 1797058, 363527], ![788785, -576156, -116603]]
    hw := by decide
    g := ![![![3017, 57748948, -26190], ![9385, 179637208, 0]], ![![705, -5417685, 2457], ![2193, -16852562, 0]]]
    h := ![![![-25798382, 2605376, -2553], ![-250244270, 247694, 0]], ![![8380675, -846360, 829], ![81292536, -80430, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {6859} * I97N1 =  Ideal.span {B.equivFun.symm ![-354, 262, 53]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E97RS1 


noncomputable def E107RS1 : RelationCertificate Table 13718 ![![107, 0, 0], ![-18, 1, 0]]
  ![-253, 226, -59] ![![13718, 0, 0], ![-6097, -3, 1]] where
    su := ![![1467826, 0, 0], ![-246924, 13718, 0]]
    hsu := by decide
    w := ![![-3470654, 3100268, -809362], ![1605006, -1371800, 356668]]
    hw := by decide
    g := ![![![56621923510876, -2641436472065736, -1305631005630], ![-24588195345965, -5978411443526106, 0]], ![![-9063012931725, 422793353407689, 208981785865], ![3935633396266, 956915923964113, 0]]]
    h := ![![![-323, 28, -1], ![-1906, 48, 0]], ![![171, -6, 0], ![1010, 26, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {13718} * I107N1 =  Ideal.span {B.equivFun.symm ![-253, 226, -59]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E107RS1 


noncomputable def E109RS0 : RelationCertificate Table 361 ![![109, 0, 0], ![11, 1, 0]]
  ![-2383, -902, 162] ![![361, 0, 0], ![-39, 1, 0]] where
    su := ![![39349, 0, 0], ![3971, 361, 0]]
    hsu := by decide
    w := ![![-860263, -325622, 58482], ![118047, 38627, -7220]]
    hw := by decide
    g := ![![![79, 102816, -2634], ![358, 951580, 0]], ![![25, 12495, -320], ![168, 115640, 0]]]
    h := ![![![-2391, -229, 1], ![23476, 53, 0]], ![![311, 20, -1], ![-3052, 89, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N0 : Ideal.span {361} * I109N0 =  Ideal.span {B.equivFun.symm ![-2383, -902, 162]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E109RS0 


noncomputable def E109RS1 : RelationCertificate Table 361 ![![109, 0, 0], ![-22, 1, 0]]
  ![592, 343, -56] ![![361, 0, 0], ![-39, 1, 0]] where
    su := ![![39349, 0, 0], ![-7942, 361, 0]]
    hsu := by decide
    w := ![![213712, 123823, -20216], ![-31768, -14801, 2527]]
    hw := by decide
    g := ![![![26, -2834, 73], ![186, -26248, 0]], ![![7, -3512, 90], ![72, -32504, 0]]]
    h := ![![![860, -25, -1], ![4234, 53, 0]], ![![-88, 5, 0], ![-432, 7, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {361} * I109N1 =  Ideal.span {B.equivFun.symm ![592, 343, -56]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E109RS1 


noncomputable def E113RS1 : RelationCertificate Table 38 ![![113, 0, 0], ![40, 1, 0]]
  ![22, 1, 1] ![![38, 0, 0], ![-17, -3, 1]] where
    su := ![![4294, 0, 0], ![1520, 38, 0]]
    hsu := by decide
    w := ![![836, 38, 38], ![-684, 0, 38]]
    hw := by decide
    g := ![![![17783, 1984, -201], ![-8109, -5248, 0]], ![![6442, 719, -73], ![-2927, -1900, 0]]]
    h := ![![![21094, 607, 2], ![-59590, -225, 0]], ![![-17266, -512, -2], ![48776, 227, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {38} * I113N1 =  Ideal.span {B.equivFun.symm ![22, 1, 1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E113RS1 


noncomputable def E127RS1 : RelationCertificate Table 4952198 ![![127, 0, 0], ![60, 1, 0]]
  ![142988, 32089, -6101] ![![4952198, 0, 0], ![-1172127, -3, 1]] where
    su := ![![628929146, 0, 0], ![297131880, 4952198, 0]]
    hsu := by decide
    w := ![![708104887624, 158911081622, -30213359998], ![-167592284716, -37611943810, 7150973912]]
    hw := by decide
    g := ![![![3226459704, -25735617677412, -65870889], ![-747301015, -108735477355088, 0]], ![![1560236309, -12441299220008, -31843784], ![-359247314, -52565694228219, 0]]]
    h := ![![![1903364, 39279, 74], ![-4026404, -15499, 0]], ![![-450566, -9327, -18], ![953134, 3730, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N1 : Ideal.span {4952198} * I127N1 =  Ideal.span {B.equivFun.symm ![142988, 32089, -6101]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E127RS1 
