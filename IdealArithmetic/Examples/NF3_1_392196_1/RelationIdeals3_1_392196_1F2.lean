import IdealArithmetic.Examples.NF3_1_392196_1.PrimesBelow3_1_392196_1F2
import IdealArithmetic.Examples.NF3_1_392196_1.ClassGroupData3_1_392196_1

set_option linter.all false

noncomputable section


noncomputable def E89RS1 : RelationCertificate Table 3 ![![89, 0, 0], ![14, 1, 0]]
  ![34605, 359, 1484] ![![3, 0, 0], ![13, 0, 1]] where
    su := ![![267, 0, 0], ![42, 3, 0]]
    hsu := by decide
    w := ![![103815, 1077, 4452], ![546849, 5673, 23451]]
    hw := by decide
    g := ![![![-10, -59, 33], ![23, 0, 0]], ![![-7, -17, -1], ![13, 0, 0]]]
    h := ![![![13190299, 81933053, 40983370], ![2995534, -607919741, 0]], ![![69480391, 431585114, 215881279], ![15778773, -3202237669, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {3} * I89N1 =  Ideal.span {B.equivFun.symm ![34605, 359, 1484]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E89RS1 


noncomputable def E103RS0 : RelationCertificate Table 12 ![![103, 0, 0], ![11, 1, 0]]
  ![106, -38, 9] ![![12, 0, 0], ![69, 1, 5]] where
    su := ![![1236, 0, 0], ![132, 12, 0]]
    hsu := by decide
    w := ![![1272, -456, 108], ![-5172, 1812, -384]]
    hw := by decide
    g := ![![![-103897435, 378744134, 94711680], ![-526384753, 93453857, -3605]], ![![-10087133, 36771283, 9195309], ![-51105317, 9073192, -350]]]
    h := ![![![185763, 849169, 566295], ![28119, -9721396, 0]], ![![-755258, -3452382, -2302328], ![-114131, 39523292, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N0 : Ideal.span {12} * I103N0 =  Ideal.span {B.equivFun.symm ![106, -38, 9]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E103RS0 


noncomputable def E103RS1 : RelationCertificate Table 2 ![![103, 0, 0], ![28, 1, 0]]
  ![-36, 8, 3] ![![2, 0, 0], ![15, 0, 1]] where
    su := ![![206, 0, 0], ![56, 2, 0]]
    hsu := by decide
    w := ![![-72, 16, 6], ![238, -38, -38]]
    hw := by decide
    g := ![![![-166, 1129, 395], ![-1015, 309, 0]], ![![-41, 298, 99], ![-240, 81, 0]]]
    h := ![![![-11080, -160025, -36939], ![-4537, 634120, 0]], ![![36551, 528611, 122021], ![15170, -2094697, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {2} * I103N1 =  Ideal.span {B.equivFun.symm ![-36, 8, 3]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E103RS1 


noncomputable def E103RS2 : RelationCertificate Table 3 ![![103, 0, 0], ![-39, 1, 0]]
  ![-7229, -75, -310] ![![3, 0, 0], ![13, 0, 1]] where
    su := ![![309, 0, 0], ![-117, 3, 0]]
    hsu := by decide
    w := ![![-21687, -225, -930], ![-114237, -1185, -4899]]
    hw := by decide
    g := ![![![-11, 25, 22], ![-26, 0, 0]], ![![-3, -14, -8], ![14, 0, 0]]]
    h := ![![![-187298, 4746095, -694720], ![117115, 11925975, 0]], ![![-986783, 25000220, -3659461], ![616420, 62820475, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N2 : Ideal.span {3} * I103N2 =  Ideal.span {B.equivFun.symm ![-7229, -75, -310]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E103RS2 


noncomputable def E107RS1 : RelationCertificate Table 3 ![![107, 0, 0], ![-7, 1, 0]]
  ![-69, 7, 16] ![![3, 0, 0], ![13, 0, 1]] where
    su := ![![321, 0, 0], ![-21, 3, 0]]
    hsu := by decide
    w := ![![-207, 21, 48], ![399, 33, -183]]
    hw := by decide
    g := ![![![3062, 603, -1743], ![12707, 0, 0]], ![![-112, -20, 57], ![-419, 0, 0]]]
    h := ![![![-3832, 17372, -11584], ![459, 206584, 0]], ![![7371, -33385, 22261], ![-776, -396998, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {3} * I107N1 =  Ideal.span {B.equivFun.symm ![-69, 7, 16]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E107RS1 


noncomputable def E109RS1 : RelationCertificate Table 3 ![![109, 0, 0], ![-44, 1, 0]]
  ![41, -7, -6] ![![3, 0, 0], ![-14, -1, -1]] where
    su := ![![327, 0, 0], ![-132, 3, 0]]
    hsu := by decide
    w := ![![123, -21, -18], ![756, -207, -15]]
    hw := by decide
    g := ![![![499, -1110, -584], ![-1707, 0, 109]], ![![-186, 450, 238], ![675, 0, -45]]]
    h := ![![![9859, -287900, 37560], ![-6593, -682341, 0]], ![![60666, -1773027, 231313], ![-40728, -4202187, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {3} * I109N1 =  Ideal.span {B.equivFun.symm ![41, -7, -6]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E109RS1 


noncomputable def E113RS1 : RelationCertificate Table 12 ![![113, 0, 0], ![-48, 1, 0]]
  ![2690, -686, -115] ![![12, 0, 0], ![19, 0, 1]] where
    su := ![![1356, 0, 0], ![-576, 12, 0]]
    hsu := by decide
    w := ![![32280, -8232, -1380], ![-9060, 1368, 1548]]
    hw := by decide
    g := ![![![1075166, -54351, -15055], ![1701095, -292788, 0]], ![![-797942324, 104729350, 35184486], ![-1260476624, 418947119, 0]]]
    h := ![![![1965362, -64000923, 7681597], ![-1401187, -144670096, 0]], ![![-550179, 17916664, -2150415], ![392282, 40499504, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {12} * I113N1 =  Ideal.span {B.equivFun.symm ![2690, -686, -115]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E113RS1 


noncomputable def E131RS1 : RelationCertificate Table 12 ![![131, 0, 0], ![-19, 1, 0]]
  ![218, 2, 9] ![![12, 0, 0], ![69, 1, 5]] where
    su := ![![1572, 0, 0], ![-228, 12, 0]]
    hsu := by decide
    w := ![![2616, 24, 108], ![18636, 204, 816]]
    hw := by decide
    g := ![![![30928531, -112740784, -28198508], ![156694743, -27818505, -131]], ![![-4721951, 17212333, 4305113], ![-23922855, 4247100, 20]]]
    h := ![![![5603, -60649, 17331], ![-1211, -378392, 0]], ![![39853, -432039, 123460], ![-9046, -2695532, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {12} * I131N1 =  Ideal.span {B.equivFun.symm ![218, 2, 9]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E131RS1 


noncomputable def E137RS1 : RelationCertificate Table 4 ![![137, 0, 0], ![-38, 1, 0]]
  ![-25254, -262, -1083] ![![4, 0, 0], ![15, 0, 1]] where
    su := ![![548, 0, 0], ![-152, 4, 0]]
    hsu := by decide
    w := ![![-101016, -1048, -4332], ![-449588, -4664, -19280]]
    hw := by decide
    g := ![![![-785348, 1000298, 423948], ![-2839053, 571590, 0]], ![![-15639640360, 19919962976, 8443053972], ![-56537887838, 11382835987, 0]]]
    h := ![![![3184854, -71485538, 10724361], ![-1405156, -244873090, 0]], ![![14174681, -318157927, 47730500], ![-6253967, -1089847220, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {4} * I137N1 =  Ideal.span {B.equivFun.symm ![-25254, -262, -1083]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E137RS1 
