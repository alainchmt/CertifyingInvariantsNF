import IdealArithmetic.Examples.NF3_1_996008_1.PrimesBelow3_1_996008_1F2
import IdealArithmetic.Examples.NF3_1_996008_1.ClassGroupData3_1_996008_1

set_option linter.all false

noncomputable section


noncomputable def E97RS0 : RelationCertificate Table 9 ![![97, 0, 0], ![27, 1, 0]]
  ![-693009, -183271, -25327] ![![9, 0, 0], ![-4, 1, 0]] where
    su := ![![873, 0, 0], ![243, 9, 0]]
    hsu := by decide
    w := ![![-6237081, -1649439, -227943], ![-2242710, -593100, -81963]]
    hw := by decide
    g := ![![![119687, 2902739, -733193], ![269342, 6599040, 0]], ![![33543, 812087, -205122], ![75330, 1846160, 0]]]
    h := ![![![-3150333, -127427, -599], ![11292196, 32776, 0]], ![![-1132804, -45837, -216], ![4060474, 11845, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N0 : Ideal.span {9} * I97N0 =  Ideal.span {B.equivFun.symm ![-693009, -183271, -25327]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E97RS0 


noncomputable def E97RS1 : RelationCertificate Table 729 ![![97, 0, 0], ![29, 1, 0]]
  ![-441, -34, 14] ![![729, 0, 0], ![-48, -1, 1]] where
    su := ![![70713, 0, 0], ![21141, 729, 0]]
    hsu := by decide
    w := ![![-321489, -24786, 10206], ![11664, 3645, -729]]
    hw := by decide
    g := ![![![-45963053813, 5366377681, 228998955], ![3019327129, 169959565314, 0]], ![![-13806109845, 1611920746, 68785349], ![906928217, 51051447634, 0]]]
    h := ![![![-4737342, -189751, -910], ![15845577, 88284, 0]], ![![172308, 6870, 32], ![-576340, -3105, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {729} * I97N1 =  Ideal.span {B.equivFun.symm ![-441, -34, 14]} * (J0 ^ 6*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6J1_1 E97RS1 


noncomputable def E97RS2 : RelationCertificate Table 3 ![![97, 0, 0], ![41, 1, 0]]
  ![43561, 11520, 1592] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![291, 0, 0], ![123, 3, 0]]
    hsu := by decide
    w := ![![130683, 34560, 4776], ![315216, 83361, 11520]]
    hw := by decide
    g := ![![![889, 115, 31], ![39, -197, 0]], ![![305, 48, 15], ![19, -85, 0]]]
    h := ![![![2327820, 74866, 455], ![-5506219, -42543, 0]], ![![5614870, 180644, 1099], ![-13281398, -102763, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N2 : Ideal.span {3} * I97N2 =  Ideal.span {B.equivFun.symm ![43561, 11520, 1592]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E97RS2 


noncomputable def E107RS1 : RelationCertificate Table 243 ![![107, 0, 0], ![33, 1, 0]]
  ![3060567, 688888, -153650] ![![243, 0, 0], ![-48, -1, 1]] where
    su := ![![26001, 0, 0], ![8019, 243, 0]]
    hsu := by decide
    w := ![![743717781, 167399784, -37336950], ![19915308, -45486441, 5905629]]
    hw := by decide
    g := ![![![4195109311, -697295183, -39118471], ![-825954782, -5953783561, 0]], ![![1301580603, -228684686, -13485935], ![-256216641, -1887014528, 0]]]
    h := ![![![11469354, 384840, -475], ![-37095767, -102825, 0]], ![![302740, 8387, 257], ![-979128, -3196, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {243} * I107N1 =  Ideal.span {B.equivFun.symm ![3060567, 688888, -153650]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E107RS1 


noncomputable def E127RS1 : RelationCertificate Table 3 ![![127, 0, 0], ![-37, 1, 0]]
  ![-195, -2, 4] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![381, 0, 0], ![-111, 3, 0]]
    hsu := by decide
    w := ![![-585, -6, 12], ![987, -93, -6]]
    hw := by decide
    g := ![![![-1080, -292, -147], ![263, 313, 0]], ![![253, 63, 40], ![-62, -90, 0]]]
    h := ![![![-22270, 677, -2], ![-76435, 258, 0]], ![![37712, -1057, 1], ![129435, -129, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N1 : Ideal.span {3} * I127N1 =  Ideal.span {B.equivFun.symm ![-195, -2, 4]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E127RS1 


noncomputable def E131RS1 : RelationCertificate Table 2187 ![![131, 0, 0], ![23, 1, 0]]
  ![-7406307, -1958648, -270674] ![![2187, 0, 0], ![662, 1, 0]] where
    su := ![![286497, 0, 0], ![50301, 2187, 0]]
    hsu := by decide
    w := ![![-16197593409, -4283563176, -591964038], ![-4956568686, -1310798133, -181144836]]
    hw := by decide
    g := ![![![1705, -15108593, -22822], ![-5717, 49913136, 0]], ![![-71, -2711622, -4096], ![223, 8958182, 0]]]
    h := ![![![-63238374, -2857916, -6237], ![359861769, 546373, 0]], ![![-19351378, -874552, -1909], ![110120180, 167251, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {2187} * I131N1 =  Ideal.span {B.equivFun.symm ![-7406307, -1958648, -270674]} * (J0 ^ 7*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7J1_0 E131RS1 
