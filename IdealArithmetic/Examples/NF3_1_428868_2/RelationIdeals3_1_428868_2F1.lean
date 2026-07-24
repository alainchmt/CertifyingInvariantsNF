import IdealArithmetic.Examples.NF3_1_428868_2.PrimesBelow3_1_428868_2F1
import IdealArithmetic.Examples.NF3_1_428868_2.ClassGroupData3_1_428868_2

set_option linter.all false

noncomputable section


noncomputable def E53RS1 : RelationCertificate Table 2 ![![53, 0, 0], ![-26, 1, 0]]
  ![-98, 9, 26] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![106, 0, 0], ![-52, 2, 0]]
    hsu := by decide
    w := ![![-196, 18, 52], ![2372, -834, 18]]
    hw := by decide
    g := ![![![294243, -41793, 10923], ![126227, 0, 0]], ![![-128225, 18212, -4760], ![-55006, 0, 0]]]
    h := ![![![6, -1644, 132], ![16, -3485, 0]], ![![198, 22350, -1789], ![358, 47413, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {2} * I53N1 =  Ideal.span {B.equivFun.symm ![-98, 9, 26]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E53RS1 


noncomputable def E61RS1 : RelationCertificate Table 25 ![![61, 0, 0], ![-22, 1, 0]]
  ![514099, 30672, 15714] ![![25, 0, 0], ![5, 1, 0]] where
    su := ![![1525, 0, 0], ![-550, 25, 0]]
    hsu := by decide
    w := ![![12852475, 766800, 392850], ![4063325, 242425, 124200]]
    hw := by decide
    g := ![![![39, 280, 90], ![20, -1206, 0]], ![![-27, -96, -32], ![7, 427, 0]]]
    h := ![![![104190037, -4757373, 2386], ![288867189, -64916, 0]], ![![32939835, -1504047, 754], ![91325791, -20513, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {25} * I61N1 =  Ideal.span {B.equivFun.symm ![514099, 30672, 15714]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E61RS1 


noncomputable def E67RS1 : RelationCertificate Table 10 ![![67, 0, 0], ![23, 1, 0]]
  ![-2651, -158, -81] ![![10, 0, 0], ![20, 1, 1]] where
    su := ![![670, 0, 0], ![230, 10, 0]]
    hsu := by decide
    w := ![![-26510, -1580, -810], ![-68030, -4060, -2080]]
    hw := by decide
    g := ![![![-2964177, 1781819, 419448], ![-5708215, 1513748, 0]], ![![-17024655659, 10233844379, 2409084030], ![-32785018463, 8694178167, 0]]]
    h := ![![![2073, -464428, -38711], ![-6154, 1296778, 0]], ![![5368, -1191811, -99340], ![-15933, 3327786, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {10} * I67N1 =  Ideal.span {B.equivFun.symm ![-2651, -158, -81]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E67RS1 


noncomputable def E73RS1 : RelationCertificate Table 2 ![![73, 0, 0], ![-16, 1, 0]]
  ![720831, 43006, 22033] ![![2, 0, 0], ![20, 1, 1]] where
    su := ![![146, 0, 0], ![-32, 2, 0]]
    hsu := by decide
    w := ![![1441662, 86012, 44066], ![18502190, 1103872, 565540]]
    hw := by decide
    g := ![![![28, -471, -105], ![127, 0, 0]], ![![-16, 115, 9], ![-18, -3, 0]]]
    h := ![![![8955303, -571304, 2009], ![40813518, -62312, 0]], ![![114931679, -7332197, 25800], ![523797592, -800315, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {2} * I73N1 =  Ideal.span {B.equivFun.symm ![720831, 43006, 22033]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E73RS1 
