import IdealArithmetic.Examples.NF3_1_614075_2.PrimesBelow3_1_614075_2F2
import IdealArithmetic.Examples.NF3_1_614075_2.ClassGroupData3_1_614075_2

set_option linter.all false

noncomputable section


noncomputable def E83RS1 : RelationCertificate Table 16 ![![83, 0, 0], ![-38, 1, 0]]
  ![5, -1, 1] ![![16, 0, 0], ![0, 1, 0]] where
    su := ![![1328, 0, 0], ![-608, 16, 0]]
    hsu := by decide
    w := ![![80, -16, 16], ![-112, -32, 0]]
    hw := by decide
    g := ![![![4, -1, -78], ![7, 1250, 0]], ![![-2, 0, 35], ![4, -561, 0]]]
    h := ![![![3703, -97, 0], ![8088, 1, 0]], ![![-5017, 170, -1], ![-10958, 83, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {16} * I83N1 =  Ideal.span {B.equivFun.symm ![5, -1, 1]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E83RS1 


noncomputable def E97RS0 : RelationCertificate Table 8 ![![97, 0, 0], ![10, 1, 0]]
  ![-4143, 315, -91] ![![8, 0, 0], ![0, 1, 0]] where
    su := ![![776, 0, 0], ![80, 8, 0]]
    hsu := by decide
    w := ![![-33144, 2520, -728], ![10192, -776, 224]]
    hw := by decide
    g := ![![![-29, -10, -88], ![3, 711, 0]], ![![-4, -2, -10], ![3, 80, 0]]]
    h := ![![![-273429, -27676, -35], ![2651847, 3304, 0]], ![![84062, 8501, 10], ![-815274, -942, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N0 : Ideal.span {8} * I97N0 =  Ideal.span {B.equivFun.symm ![-4143, 315, -91]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E97RS0 


noncomputable def E97RS1 : RelationCertificate Table 16 ![![97, 0, 0], ![22, 1, 0]]
  ![263399, -20027, 5787] ![![16, 0, 0], ![0, 1, 0]] where
    su := ![![1552, 0, 0], ![352, 16, 0]]
    hsu := by decide
    w := ![![4214384, -320432, 92592], ![-648144, 49280, -14240]]
    hw := by decide
    g := ![![![-110, -34, 1356070], ![1, -21697050, 0]], ![![-30, -11, 318071], ![8, -5089125, 0]]]
    h := ![![![60887847, 2970543, 9298], ![-268448080, -896119, 0]], ![![-9364181, -456874, -1431], ![41285684, 137917, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {16} * I97N1 =  Ideal.span {B.equivFun.symm ![263399, -20027, 5787]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E97RS1 


noncomputable def E97RS2 : RelationCertificate Table 32 ![![97, 0, 0], ![-33, 1, 0]]
  ![43, 17, -1] ![![32, 0, 0], ![16, 1, 0]] where
    su := ![![3104, 0, 0], ![-1056, 32, 0]]
    hsu := by decide
    w := ![![1376, 544, -32], ![800, 352, 0]]
    hw := by decide
    g := ![![![1309895, -104792620, -6554656], ![-2619820, 209748981, 0]], ![![-450292, 36022462, 2253163], ![900595, -72101212, 0]]]
    h := ![![![57844, -1885, 4], ![170025, -389, 0]], ![![33664, -1086, 2], ![98951, -194, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N2 : Ideal.span {32} * I97N2 =  Ideal.span {B.equivFun.symm ![43, 17, -1]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E97RS2 


noncomputable def E103RS1 : RelationCertificate Table 2 ![![103, 0, 0], ![-19, 1, 0]]
  ![-591, 45, -13] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![206, 0, 0], ![-38, 2, 0]]
    hsu := by decide
    w := ![![-1182, 90, -26], ![1456, -110, 32]]
    hw := by decide
    g := ![![![31, 5, -20758], ![3, 41511, 0]], ![![-3, 0, 3494], ![0, -6987, 0]]]
    h := ![![![-5059, 283, -1], ![-27394, 90, 0]], ![![6266, -327, 0], ![33930, 16, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {2} * I103N1 =  Ideal.span {B.equivFun.symm ![-591, 45, -13]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E103RS1 


noncomputable def E107RS0 : RelationCertificate Table 8 ![![107, 0, 0], ![19, 1, 0]]
  ![163811, -12455, 3599] ![![8, 0, 0], ![0, 1, 0]] where
    su := ![![856, 0, 0], ![152, 8, 0]]
    hsu := by decide
    w := ![![1310488, -99640, 28792], ![-403088, 30648, -8856]]
    hw := by decide
    g := ![![![-45, -44, 373151], ![-1, -2985292, 0]], ![![3, -5, 72747], ![3, -581995, 0]]]
    h := ![![![18880282, 1031452, 2031], ![-106317177, -213718, 0]], ![![-5807334, -317267, -625], ![32701808, 65768, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N0 : Ideal.span {8} * I107N0 =  Ideal.span {B.equivFun.symm ![163811, -12455, 3599]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E107RS0 


noncomputable def E107RS2 : RelationCertificate Table 8 ![![107, 0, 0], ![-8, 1, 0]]
  ![-23, 3, 5] ![![8, 0, 0], ![0, 1, 0]] where
    su := ![![856, 0, 0], ![-64, 8, 0]]
    hsu := by decide
    w := ![![-184, 24, 40], ![-560, -208, 8]]
    hw := by decide
    g := ![![![-757, 56, -137], ![12, 963, 0]], ![![74, -6, 11], ![3, -75, 0]]]
    h := ![![![-1477, 193, -1], ![-19752, 112, 0]], ![![-4498, 570, -1], ![-60152, 108, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N2 : Ideal.span {8} * I107N2 =  Ideal.span {B.equivFun.symm ![-23, 3, 5]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E107RS2 


noncomputable def E113RS1 : RelationCertificate Table 16 ![![113, 0, 0], ![25, 1, 0]]
  ![615, 277, 11] ![![16, 0, 0], ![0, 1, 0]] where
    su := ![![1808, 0, 0], ![400, 16, 0]]
    hsu := by decide
    w := ![![9840, 4432, 176], ![-1232, 208, 288]]
    hw := by decide
    g := ![![![-13777, 1043, -18511538], ![72, 296179765, 0]], ![![-2748, 208, -4040861], ![15, 64652810, 0]]]
    h := ![![![150130, 6455, 18], ![-678563, -2023, 0]], ![![-18754, -829, -3], ![84765, 357, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {16} * I113N1 =  Ideal.span {B.equivFun.symm ![615, 277, 11]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E113RS1 


noncomputable def E127RS1 : RelationCertificate Table 32 ![![127, 0, 0], ![55, 1, 0]]
  ![-591021, 44937, -12985] ![![32, 0, 0], ![16, 1, 0]] where
    su := ![![4064, 0, 0], ![1760, 32, 0]]
    hsu := by decide
    w := ![![-18912672, 1437984, -415520], ![-8002016, 608416, -175808]]
    hw := by decide
    g := ![![![-44641264124229, 3571301129943353, 223380700559445], ![89282528248622, -7148182417902167, 0]], ![![-18981324915148, 1518505993212957, 94980770376260], ![37962649830363, -3039384652040278, 0]]]
    h := ![![![-456922173, -11271999, -54007], ![1055064090, 6845904, 0]], ![![-193325319, -4769246, -22851], ![446401190, 2896583, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N1 : Ideal.span {32} * I127N1 =  Ideal.span {B.equivFun.symm ![-591021, 44937, -12985]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E127RS1 


noncomputable def E137RS1 : RelationCertificate Table 16 ![![137, 0, 0], ![-24, 1, 0]]
  ![15, 13, 3] ![![16, 0, 0], ![0, 1, 0]] where
    su := ![![2192, 0, 0], ![-384, 16, 0]]
    hsu := by decide
    w := ![![240, 208, 48], ![-336, -96, 16]]
    hw := by decide
    g := ![![![88, -7, -997159], ![3, 15954575, 0]], ![![-17, 1, 153409], ![5, -2454550, 0]]]
    h := ![![![135, -5, 0], ![770, 3, 0]], ![![-141, 30, -1], ![-804, 138, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {16} * I137N1 =  Ideal.span {B.equivFun.symm ![15, 13, 3]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E137RS1 
