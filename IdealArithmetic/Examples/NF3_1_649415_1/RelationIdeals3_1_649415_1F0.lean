import IdealArithmetic.Examples.NF3_1_649415_1.PrimesBelow3_1_649415_1F0
import IdealArithmetic.Examples.NF3_1_649415_1.ClassGroupData3_1_649415_1

set_option linter.all false

noncomputable section


noncomputable def E3RS0 : RelationCertificate Table 27 ![![3, 0, 0], ![0, 1, 0]]
  ![-3089, 132, 67] ![![27, 0, 0], ![-4, 1, 0]] where
    su := ![![81, 0, 0], ![0, 27, 0]]
    hsu := by decide
    w := ![![-83403, 3564, 1809], ![23139, -3213, 459]]
    hw := by decide
    g := ![![![-5498, -871, -276], ![809, -553, 0]], ![![-19871, -2760, -1352], ![2853, -28, 0]]]
    h := ![![![-931, -148194, 269], ![444566, -148, 0]], ![![243, 41064, -101], ![-123247, 64, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {27} * I3N0 =  Ideal.span {B.equivFun.symm ![-3089, 132, 67]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 81 ![![3, 0, 0], ![1, 1, 0]]
  ![377, -123, 38] ![![81, 0, 0], ![-4, 1, 0]] where
    su := ![![243, 0, 0], ![81, 81, 0]]
    hsu := by decide
    w := ![![30537, -9963, 3078], ![4212, 1296, -729]]
    hw := by decide
    g := ![![![-102, 20, -39], ![66, 532, 0]], ![![-365, -31, -41], ![58, 273, 0]]]
    h := ![![![-73216, 7284, -201654], ![-21975, 121000, 0]], ![![-5265, 531, -14523], ![-1577, 8712, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {81} * I3N1 =  Ideal.span {B.equivFun.symm ![377, -123, 38]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E3RS1 


noncomputable def E3RS2 : RelationCertificate Table 1 ![![3, 0, 0], ![-1, 1, 0]]
  ![1, 0, 0] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![3, 0, 0], ![-1, 1, 0]]
    hsu := by decide
    w := ![![3, 0, 0], ![-1, 1, 0]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N2 : Ideal.span {1} * I3N2 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E3RS2 


noncomputable def E5RS0 : RelationCertificate Table 81 ![![5, 0, 0], ![2, 1, 0]]
  ![-223, 30, -4] ![![81, 0, 0], ![-4, 1, 0]] where
    su := ![![405, 0, 0], ![162, 81, 0]]
    hsu := by decide
    w := ![![-18063, 2430, -324], ![324, -405, 162]]
    hw := by decide
    g := ![![![117, -269, 270], ![37, -4366, 0]], ![![82, -149, 152], ![58, -2442, 0]]]
    h := ![![![-7635906, 154003, -169019], ![-3023561, 0, 281697]], ![![185707, -3747, 4111], ![73538, 0, -6851]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {81} * I5N0 =  Ideal.span {B.equivFun.symm ![-223, 30, -4]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 729 ![![5, 0, 0], ![-3, -1, 1]]
  ![152, -15, 2] ![![729, 0, 0], ![-328, 1, 0]] where
    su := ![![3645, 0, 0], ![-2187, -729, 729]]
    hsu := by decide
    w := ![![110808, -10935, 1458], ![-49572, 5103, -729]]
    hw := by decide
    g := ![![![-485, 128046, -1946], ![652, 283727, 0]], ![![641, -80934, 1230], ![331, -179333, 0]]]
    h := ![![![7388, -464, 589], ![-4219, -319, 0]], ![![-3309, 209, -265], ![1896, 143, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {729} * I5N1 =  Ideal.span {B.equivFun.symm ![152, -15, 2]} * (J0 ^ 6) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6 E5RS1 


noncomputable def E7RS0 : RelationCertificate Table 27 ![![7, 0, 0], ![-6, -4, 1]]
  ![1193, 156, 80] ![![27, 0, 0], ![-4, 1, 0]] where
    su := ![![189, 0, 0], ![-162, -108, 27]]
    hsu := by decide
    w := ![![32211, 4212, 2160], ![8100, 1053, 540]]
    hw := by decide
    g := ![![![13367, -34500, 34620], ![-3236, -186948, 0]], ![![-8904, 23005, -23086], ![2198, 124661, 0]]]
    h := ![![![107, -20, 22], ![-74, 0, 0]], ![![30, -3, 5], ![-15, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {27} * I7N0 =  Ideal.span {B.equivFun.symm ![1193, 156, 80]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 243 ![![7, 0, 0], ![-2, 1, 0]]
  ![18454, 2409, 1234] ![![243, 0, 0], ![-85, 1, 0]] where
    su := ![![1701, 0, 0], ![-486, 243, 0]]
    hsu := by decide
    w := ![![4484322, 585387, 299862], ![-1370034, -178848, -91611]]
    hw := by decide
    g := ![![![-917, 49071, -2853], ![646, 138662, 0]], ![![274, -10993, 639], ![43, -31061, 0]]]
    h := ![![![41960, -64706, 113647], ![-21226, -158859, 0]], ![![-12818, 19768, -34721], ![6490, 48534, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {243} * I7N1 =  Ideal.span {B.equivFun.symm ![18454, 2409, 1234]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E7RS1 


noncomputable def E11RS0 : RelationCertificate Table 3 ![![11, 0, 0], ![5, 1, 0]]
  ![-299, -39, -20] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![33, 0, 0], ![15, 3, 0]]
    hsu := by decide
    w := ![![-897, -117, -60], ![-2919, -381, -195]]
    hw := by decide
    g := ![![![-20, -2, -5], ![8, 4, 0]], ![![12, 1, -5], ![-1, 3, 0]]]
    h := ![![![-10680, -27304, -34960], ![-7327, 76908, 0]], ![![-34743, -88849, -113765], ![-23868, 250270, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {3} * I11N0 =  Ideal.span {B.equivFun.symm ![-299, -39, -20]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 81 ![![11, 0, 0], ![-4, 1, 0]]
  ![-1070144, -139683, -71561] ![![81, 0, 0], ![-4, 1, 0]] where
    su := ![![891, 0, 0], ![-324, 81, 0]]
    hsu := by decide
    w := ![![-86681664, -11314323, -5796441], ![-7233867, -944217, -483732]]
    hw := by decide
    g := ![![![-1471317, 3691535, -3692994], ![118288, 59826443, 0]], ![![404603, -1015284, 1015687], ![-32501, -16454076, 0]]]
    h := ![![![-1329066, 3740393, -3834446], ![823339, 8421469, 0]], ![![-110915, 312148, -319997], ![68710, 702799, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {81} * I11N1 =  Ideal.span {B.equivFun.symm ![-1070144, -139683, -71561]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E11RS1 


noncomputable def E11RS2 : RelationCertificate Table 27 ![![11, 0, 0], ![-1, 1, 0]]
  ![-23, -21, 10] ![![27, 0, 0], ![-4, 1, 0]] where
    su := ![![297, 0, 0], ![-27, 27, 0]]
    hsu := by decide
    w := ![![-621, -567, 270], ![1620, 162, -135]]
    hw := by decide
    g := ![![![-381625026, 985069673, -988514895], ![93021127, 5337980442, 0]], ![![36345271, -93816169, 94144290], ![-8859149, -508379158, 0]]]
    h := ![![![-529, 525, -1340], ![104, 2950, 0]], ![![270, -264, 670], ![-40, -1475, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N2 : Ideal.span {27} * I11N2 =  Ideal.span {B.equivFun.symm ![-23, -21, 10]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E11RS2 


noncomputable def E13RS0 : RelationCertificate Table 9 ![![13, 0, 0], ![1, 1, 0]]
  ![82, -3, -2] ![![9, 0, 0], ![-4, 1, 0]] where
    su := ![![117, 0, 0], ![9, 9, 0]]
    hsu := by decide
    w := ![![738, -27, -18], ![-648, 81, -9]]
    hw := by decide
    g := ![![![-1009, 3242, -3339], ![811, 6006, 0]], ![![-86, 202, -216], ![70, 385, 0]]]
    h := ![![![-1437, 8, -3629], ![-107, 9435, 0]], ![![1369, -8, 3458], ![113, -8991, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {9} * I13N0 =  Ideal.span {B.equivFun.symm ![82, -3, -2]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 27 ![![13, 0, 0], ![6, 1, 0]]
  ![-21145, -2760, -1414] ![![27, 0, 0], ![-4, 1, 0]] where
    su := ![![351, 0, 0], ![162, 27, 0]]
    hsu := by decide
    w := ![![-570915, -74520, -38178], ![-142938, -18657, -9558]]
    hw := by decide
    g := ![![![-67, 180, -183], ![31, 995, 0]], ![![-22, 105, -107], ![33, 575, 0]]]
    h := ![![![-81157, -260982, -265303], ![-57519, 689505, 0]], ![![-20318, -65341, -66423], ![-14403, 172629, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {27} * I13N1 =  Ideal.span {B.equivFun.symm ![-21145, -2760, -1414]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E13RS1 


noncomputable def E19RS0 : RelationCertificate Table 9 ![![19, 0, 0], ![1, 1, 0]]
  ![-59, 24, -8] ![![9, 0, 0], ![-4, 1, 0]] where
    su := ![![171, 0, 0], ![9, 9, 0]]
    hsu := by decide
    w := ![![-531, 216, -72], ![-972, -243, 144]]
    hw := by decide
    g := ![![![-197, -171, 108], ![71, -228, 0]], ![![-143, -35, -6], ![62, -10, 0]]]
    h := ![![![1408, -3, 3538], ![81, -13446, 0]], ![![1371, -6, 3454], ![87, -13122, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N0 : Ideal.span {9} * I19N0 =  Ideal.span {B.equivFun.symm ![-59, 24, -8]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E19RS0 


noncomputable def E19RS1 : RelationCertificate Table 9 ![![19, 0, 0], ![6, 1, 0]]
  ![19171624, 2502420, 1282015] ![![9, 0, 0], ![-4, 1, 0]] where
    su := ![![171, 0, 0], ![54, 9, 0]]
    hsu := by decide
    w := ![![172544616, 22521780, 11538135], ![129594699, 16915644, 8666055]]
    hw := by decide
    g := ![![![-2785, -136, 140], ![1229, -20, 0]], ![![8, -121, 55], ![-15, -8, 0]]]
    h := ![![![196368726, 555777081, 560516145], ![91262621, -2129704948, 0]], ![![147488497, 417432692, 420992105], ![68545468, -1599577420, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {9} * I19N1 =  Ideal.span {B.equivFun.symm ![19171624, 2502420, 1282015]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E19RS1 


noncomputable def E19RS2 : RelationCertificate Table 81 ![![19, 0, 0], ![-7, 1, 0]]
  ![178, 24, 13] ![![81, 0, 0], ![-4, 1, 0]] where
    su := ![![1539, 0, 0], ![-567, 81, 0]]
    hsu := by decide
    w := ![![14418, 1944, 1053], ![1377, 162, 81]]
    hw := by decide
    g := ![![![675, -1688, 1688], ![7, -27346, 0]], ![![-239, 606, -607], ![77, 9834, 0]]]
    h := ![![![183843, -898787, 565527], ![-115023, -2149000, 0]], ![![17598, -86027, 54129], ![-11005, -205690, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N2 : Ideal.span {81} * I19N2 =  Ideal.span {B.equivFun.symm ![178, 24, 13]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E19RS2 


noncomputable def E29RS0 : RelationCertificate Table 2187 ![![29, 0, 0], ![0, 1, 0]]
  ![4016, -51, -139] ![![2187, 0, 0], ![-1057, 1, 0]] where
    su := ![![63423, 0, 0], ![0, 2187, 0]]
    hsu := by decide
    w := ![![8782992, -111537, -303993], ![-4266837, 56862, 146529]]
    hw := by decide
    g := ![![![4232, -3000679, 14181], ![-2983, -6202730, 0]], ![![1007, -684307, 3234], ![-594, -1414537, 0]]]
    h := ![![![-17561968, 8770622, -43905271], ![302455, 254650544, 0]], ![![8531723, -4260828, 21329478], ![-146921, -123710959, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N0 : Ideal.span {2187} * I29N0 =  Ideal.span {B.equivFun.symm ![4016, -51, -139]} * (J0 ^ 7) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7 E29RS0 
