import IdealArithmetic.Examples.NF3_1_469300_2.PrimesBelow3_1_469300_2F2
import IdealArithmetic.Examples.NF3_1_469300_2.ClassGroupData3_1_469300_2

set_option linter.all false

noncomputable section


noncomputable def E89RS1 : RelationCertificate Table 96 ![![89, 0, 0], ![26, 1, 0]]
  ![-392, -22, 5] ![![96, 0, 0], ![-15, -4, 1]] where
    su := ![![8544, 0, 0], ![2496, 96, 0]]
    hsu := by decide
    w := ![![-37632, -2112, 480], ![-10080, -192, 96]]
    hw := by decide
    g := ![![![883, 186, -8], ![-109, -225, 0]], ![![277, 59, -3], ![26, -68, 0]]]
    h := ![![![-2404, -120, -1], ![8214, 94, 0]], ![![-669, -52, -1], ![2286, 90, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {96} * I89N1 =  Ideal.span {B.equivFun.symm ![-392, -22, 5]} * (J0 ^ 9*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_9J1_1 E89RS1 


noncomputable def E97RS1 : RelationCertificate Table 18 ![![97, 0, 0], ![-13, 1, 0]]
  ![-46, -2, 1] ![![18, 0, 0], ![-61, -6, 1]] where
    su := ![![1746, 0, 0], ![-234, 18, 0]]
    hsu := by decide
    w := ![![-828, -36, 18], ![-234, 18, 0]]
    hw := by decide
    g := ![![![668, -7, -6], ![-2225, -388, 0]], ![![-42, 6, 0], ![325, 54, 0]]]
    h := ![![![-90, 7, 0], ![-668, 1, 0]], ![![-26, 15, -1], ![-193, 97, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {18} * I97N1 =  Ideal.span {B.equivFun.symm ![-46, -2, 1]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E97RS1 


noncomputable def E103RS1 : RelationCertificate Table 36 ![![103, 0, 0], ![-38, 1, 0]]
  ![-128, -13, 2] ![![36, 0, 0], ![-75, -4, 1]] where
    su := ![![3708, 0, 0], ![-1368, 36, 0]]
    hsu := by decide
    w := ![![-4608, -468, 72], ![1620, 252, -36]]
    hw := by decide
    g := ![![![-50808911, -2518993, -85810], ![106129539, 25760096, 0]], ![![18362336, 910364, 31011], ![-38355082, -9309672, 0]]]
    h := ![![![-1308, 73, -1], ![-3542, 105, 0]], ![![521, -14, 0], ![1411, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {36} * I103N1 =  Ideal.span {B.equivFun.symm ![-128, -13, 2]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E103RS1 


noncomputable def E107RS1 : RelationCertificate Table 36 ![![107, 0, 0], ![51, 1, 0]]
  ![-28, -2, 1] ![![36, 0, 0], ![-75, -4, 1]] where
    su := ![![3852, 0, 0], ![1836, 36, 0]]
    hsu := by decide
    w := ![![-1008, -72, 36], ![-180, 72, 0]]
    hw := by decide
    g := ![![![74048301, 3671151, 125057], ![-154671695, -37542409, 0]], ![![34938808, 1732189, 59006], ![-72979883, -17713916, 0]]]
    h := ![![![-332, -58, -1], ![696, 108, 0]], ![![-52, -52, -1], ![109, 107, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {36} * I107N1 =  Ideal.span {B.equivFun.symm ![-28, -2, 1]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E107RS1 


noncomputable def E109RS1 : RelationCertificate Table 144 ![![109, 0, 0], ![22, 1, 0]]
  ![-164, -13, 2] ![![144, 0, 0], ![-111, -4, 1]] where
    su := ![![15696, 0, 0], ![3168, 144, 0]]
    hsu := by decide
    w := ![![-23616, -1872, 288], ![10224, 864, -144]]
    hw := by decide
    g := ![![![-253, 31, 3], ![327, 193, 0]], ![![19, 10, 0], ![178, 45, 0]]]
    h := ![![![-188, -9, 0], ![924, 2, 0]], ![![61, -19, -1], ![-299, 108, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {144} * I109N1 =  Ideal.span {B.equivFun.symm ![-164, -13, 2]} * (J0 ^ 6*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6J1_2 E109RS1 


noncomputable def E127RS1 : RelationCertificate Table 64 ![![127, 0, 0], ![9, 1, 0]]
  ![36, 13, 1] ![![64, 0, 0], ![-1213, -108, 19]] where
    su := ![![8128, 0, 0], ![576, 64, 0]]
    hsu := by decide
    w := ![![2304, 832, 64], ![9152, 768, -128]]
    hw := by decide
    g := ![![![-358835, 716922, -69383], ![5592729, 942790, 0]], ![![-30569, 61836, -5987], ![482151, 81275, 0]]]
    h := ![![![18108, 2021, 1], ![-255520, -126, 0]], ![![71909, 8035, 5], ![-1014700, -637, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N1 : Ideal.span {64} * I127N1 =  Ideal.span {B.equivFun.symm ![36, 13, 1]} * (J0 ^ 11*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_11J1_0 E127RS1 


noncomputable def E131RS1 : RelationCertificate Table 16 ![![131, 0, 0], ![42, 1, 0]]
  ![-148, -21, 3] ![![16, 0, 0], ![-181, -20, 3]] where
    su := ![![2096, 0, 0], ![672, 16, 0]]
    hsu := by decide
    w := ![![-2368, -336, 48], ![-19952, -1504, 288]]
    hw := by decide
    g := ![![![592785, -1108310, -68871], ![-5332453, -854964, 0]], ![![194719, -364001, -22620], ![-1751342, -280797, 0]]]
    h := ![![![-63500, -1765, -6], ![198056, 789, 0]], ![![-534355, -14577, -44], ![1666649, 5782, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {16} * I131N1 =  Ideal.span {B.equivFun.symm ![-148, -21, 3]} * (J0 ^ 7*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7J1_0 E131RS1 


noncomputable def E137RS1 : RelationCertificate Table 48 ![![137, 0, 0], ![-49, 1, 0]]
  ![-4, 7, 1] ![![48, 0, 0], ![-433, -36, 7]] where
    su := ![![6576, 0, 0], ![-2352, 48, 0]]
    hsu := by decide
    w := ![![-192, 336, 48], ![6672, 1008, -48]]
    hw := by decide
    g := ![![![-273, -163, -87], ![3815, 626, 0]], ![![530, 94, 24], ![-1311, -223, 0]]]
    h := ![![![20, 0, 0], ![56, 1, 0]], ![![1167, -24, 0], ![3260, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {48} * I137N1 =  Ideal.span {B.equivFun.symm ![-4, 7, 1]} * (J0 ^ 6*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6J1_1 E137RS1 
