import IdealArithmetic.Examples.NF3_1_662796_4.PrimesBelow3_1_662796_4F2
import IdealArithmetic.Examples.NF3_1_662796_4.ClassGroupData3_1_662796_4

set_option linter.all false

noncomputable section


noncomputable def E83RS1 : RelationCertificate Table 169 ![![83, 0, 0], ![26, 1, 0]]
  ![299, 1, -2] ![![169, 0, 0], ![-52, -6, 1]] where
    su := ![![14027, 0, 0], ![4394, 169, 0]]
    hsu := by decide
    w := ![![50531, 169, -338], ![-9126, -1352, 169]]
    hw := by decide
    g := ![![![480951439, 60830023, -5514128], ![-150177257, -180344150, 0]], ![![156588868, 19805127, -1795298], ![-48894833, -58716700, 0]]]
    h := ![![![1313, 51, 0], ![-4180, -2, 0]], ![![-250, -36, -1], ![796, 84, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {169} * I83N1 =  Ideal.span {B.equivFun.symm ![299, 1, -2]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E83RS1 


noncomputable def E89RS1 : RelationCertificate Table 13 ![![89, 0, 0], ![-39, 1, 0]]
  ![-91, -7, 1] ![![13, 0, 0], ![-6, 1, 0]] where
    su := ![![1157, 0, 0], ![-507, 13, 0]]
    hsu := by decide
    w := ![![-1183, -91, 13], ![1040, 65, -13]]
    hw := by decide
    g := ![![![9, 6, -1], ![-1, 11, 0]], ![![1, -1, 0], ![13, 1, 0]]]
    h := ![![![-1001, 65, -1], ![-2282, 90, 0]], ![![922, -24, 0], ![2102, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {13} * I89N1 =  Ideal.span {B.equivFun.symm ![-91, -7, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E89RS1 


noncomputable def E97RS1 : RelationCertificate Table 169 ![![97, 0, 0], ![-30, 1, 0]]
  ![-117, -27, 2] ![![169, 0, 0], ![-71, 1, 0]] where
    su := ![![16393, 0, 0], ![-5070, 169, 0]]
    hsu := by decide
    w := ![![-19773, -4563, 338], ![9295, 2028, -169]]
    hw := by decide
    g := ![![![341, 144621, -2037], ![808, 344250, 0]], ![![-43, -44374, 625], ![-101, -105624, 0]]]
    h := ![![![-735471, 26256, -58], ![-2378019, 5628, 0]], ![![345805, -12307, 26], ![1118101, -2523, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {169} * I97N1 =  Ideal.span {B.equivFun.symm ![-117, -27, 2]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E97RS1 


noncomputable def E101RS1 : RelationCertificate Table 169 ![![101, 0, 0], ![41, 1, 0]]
  ![177, 11, -2] ![![169, 0, 0], ![-26, 46, 1]] where
    su := ![![17069, 0, 0], ![6929, 169, 0]]
    hsu := by decide
    w := ![![29913, 1859, -338], ![-44616, -2366, 507]]
    hw := by decide
    g := ![![![1, -5, 0], ![19, 0, 0]], ![![1, -2, 0], ![8, 0, 0]]]
    h := ![![![641778, 19836, 102], ![-1580961, -10304, 0]], ![![-957174, -29661, -154], ![2357910, 15557, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {169} * I101N1 =  Ideal.span {B.equivFun.symm ![177, 11, -2]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E101RS1 


noncomputable def E109RS1 : RelationCertificate Table 169 ![![109, 0, 0], ![-14, 1, 0]]
  ![-3869, -1209, -98] ![![169, 0, 0], ![-52, 1, 0]] where
    su := ![![18421, 0, 0], ![-2366, 169, 0]]
    hsu := by decide
    w := ![![-653861, -204321, -16562], ![152776, 47827, 3887]]
    hw := by decide
    g := ![![![-12336979, -7417590239, 142650529], ![-40095060, -24107939328, 0]], ![![1470484, 884095530, -17002381], ![4779051, 2873402376, 0]]]
    h := ![![![-22543, 1626, -3], ![-175237, 229, 0]], ![![5280, -371, 0], ![41044, 23, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {169} * I109N1 =  Ideal.span {B.equivFun.symm ![-3869, -1209, -98]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E109RS1 


noncomputable def E113RS0 : RelationCertificate Table 169 ![![113, 0, 0], ![56, 1, 0]]
  ![-351, -35, 5] ![![169, 0, 0], ![-52, -6, 1]] where
    su := ![![19097, 0, 0], ![9464, 169, 0]]
    hsu := by decide
    w := ![![-59319, -5915, 845], ![-13858, -1014, 169]]
    hw := by decide
    g := ![![![296603975, 37514029, -3400577], ![-92614625, -111218688, 0]], ![![155584684, 19678119, -1783785], ![-48581300, -58340160, 0]]]
    h := ![![![-727847, -24704, -209], ![1468685, 23622, 0]], ![![-169986, -5780, -49], ![343006, 5538, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N0 : Ideal.span {169} * I113N0 =  Ideal.span {B.equivFun.symm ![-351, -35, 5]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E113RS0 


noncomputable def E113RS1 : RelationCertificate Table 169 ![![113, 0, 0], ![-47, 1, 0]]
  ![61, 26, 3] ![![169, 0, 0], ![-26, -6, 1]] where
    su := ![![19097, 0, 0], ![-7943, 169, 0]]
    hsu := by decide
    w := ![![10309, 4394, 507], ![2366, 1352, 169]]
    hw := by decide
    g := ![![![218130981, 38574400, -2507895], ![-34942874, -76462848, 0]], ![![-90651809, -16030913, 1042241], ![14521898, 31776768, 0]]]
    h := ![![![519420, -12554, 32], ![1248817, -3613, 0]], ![![119168, -2864, 7], ![286510, -790, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {169} * I113N1 =  Ideal.span {B.equivFun.symm ![61, 26, 3]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E113RS1 


noncomputable def E127RS0 : RelationCertificate Table 13 ![![127, 0, 0], ![1, 1, 0]]
  ![-143, -14, 2] ![![13, 0, 0], ![-6, 1, 0]] where
    su := ![![1651, 0, 0], ![13, 13, 0]]
    hsu := by decide
    w := ![![-1859, -182, 26], ![1846, 169, -26]]
    hw := by decide
    g := ![![![439413, 15012901, -2514356], ![952045, 32686626, 0]], ![![3755, 128146, -21462], ![8137, 279006, 0]]]
    h := ![![![-2, -2, -1], ![111, 129, 0]], ![![1, 1, 1], ![15, -129, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N0 : Ideal.span {13} * I127N0 =  Ideal.span {B.equivFun.symm ![-143, -14, 2]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E127RS0 


noncomputable def E127RS1 : RelationCertificate Table 13 ![![127, 0, 0], ![15, 1, 0]]
  ![-137, -13, 2] ![![13, 0, 0], ![0, 1, 0]] where
    su := ![![1651, 0, 0], ![195, 13, 0]]
    hsu := by decide
    w := ![![-1781, -169, 26], ![988, 91, -13]]
    hw := by decide
    g := ![![![11, 1, -1409757], ![2, 18326840, 0]], ![![1, 0, -171680], ![2, 2231840, 0]]]
    h := ![![![-296, -35, -1], ![2497, 129, 0]], ![![148, 10, 0], ![-1248, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N1 : Ideal.span {13} * I127N1 =  Ideal.span {B.equivFun.symm ![-137, -13, 2]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E127RS1 


noncomputable def E127RS2 : RelationCertificate Table 169 ![![127, 0, 0], ![-16, 1, 0]]
  ![-241, 7, 1] ![![169, 0, 0], ![-26, 46, 1]] where
    su := ![![21463, 0, 0], ![-2704, 169, 0]]
    hsu := by decide
    w := ![![-40729, 1183, 169], ![32448, -4732, 169]]
    hw := by decide
    g := ![![![-17, -57, -2], ![162, 0, 0]], ![![2, -1, 0], ![5, 0, 0]]]
    h := ![![![-271, 33, -1], ![-2136, 128, 0]], ![![256, -16, 0], ![2020, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N2 : Ideal.span {169} * I127N2 =  Ideal.span {B.equivFun.symm ![-241, 7, 1]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E127RS2 


noncomputable def E137RS1 : RelationCertificate Table 169 ![![137, 0, 0], ![2, 1, 0]]
  ![283, 87, 7] ![![169, 0, 0], ![-26, 46, 1]] where
    su := ![![23153, 0, 0], ![338, 169, 0]]
    hsu := by decide
    w := ![![47827, 14703, 1183], ![194688, 60840, 4901]]
    hw := by decide
    g := ![![![29, -3, 0], ![2, 0, 0]], ![![26, -45, -1], ![166, 0, 0]]]
    h := ![![![93977, 46998, 5], ![-6437283, -678, 0]], ![![382556, 191316, 20], ![-26204510, -2711, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {169} * I137N1 =  Ideal.span {B.equivFun.symm ![283, 87, 7]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E137RS1 
