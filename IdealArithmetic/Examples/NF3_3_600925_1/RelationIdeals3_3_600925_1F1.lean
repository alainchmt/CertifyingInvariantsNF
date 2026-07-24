import IdealArithmetic.Examples.NF3_3_600925_1.PrimesBelow3_3_600925_1F1
import IdealArithmetic.Examples.NF3_3_600925_1.ClassGroupData3_3_600925_1

set_option linter.all false

noncomputable section


noncomputable def E37RS1 : RelationCertificate Table 3 ![![37, 0, 0], ![-4, 1, 0]]
  ![1, -5, 1] ![![3, 0, 0], ![-30, -2, 1]] where
    su := ![![111, 0, 0], ![-12, 3, 0]]
    hsu := by decide
    w := ![![3, -15, 3], ![-906, -111, 36]]
    hw := by decide
    g := ![![![3335, 36111, 3244], ![-56216, -11620, 0]], ![![-276, -3096, -279], ![4820, 996, 0]]]
    h := ![![![13, 0, -2], ![120, 25, 0]], ![![-3366, 854, -9], ![-31060, 115, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {3} * I37N1 =  Ideal.span {B.equivFun.symm ![1, -5, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E37RS1 


noncomputable def E61RS0 : RelationCertificate Table 9 ![![61, 0, 0], ![19, 1, 0]]
  ![-21379, -5113, 1358] ![![9, 0, 0], ![-27, -2, 1]] where
    su := ![![549, 0, 0], ![171, 9, 0]]
    hsu := by decide
    w := ![![-192411, -46017, 12222], ![-367533, -88740, 23517]]
    hw := by decide
    g := ![![![-333, -1649, -749], ![1364, -92, 0]], ![![-169, -866, -400], ![656, -64, 0]]]
    h := ![![![-3504912, -199470, -2467], ![11251487, 50615, 0]], ![![-6694832, -381003, -4710], ![21491785, 96641, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N0 : Ideal.span {9} * I61N0 =  Ideal.span {B.equivFun.symm ![-21379, -5113, 1358]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E61RS0 


noncomputable def E61RS1 : RelationCertificate Table 9 ![![61, 0, 0], ![20, 1, 0]]
  ![-5, 1, 1] ![![9, 0, 0], ![-27, -2, 1]] where
    su := ![![549, 0, 0], ![180, 9, 0]]
    hsu := by decide
    w := ![![-45, 9, 9], ![135, 18, 9]]
    hw := by decide
    g := ![![![3254, 2861, 209], ![-10309, -2108, 0]], ![![1122, 978, 71], ![-3518, -720, 0]]]
    h := ![![![-465, -36, -2], ![1418, 41, 0]], ![![1275, 70, 1], ![-3888, -20, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {9} * I61N1 =  Ideal.span {B.equivFun.symm ![-5, 1, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E61RS1 


noncomputable def E61RS2 : RelationCertificate Table 9 ![![61, 0, 0], ![21, 1, 0]]
  ![-88055, -21161, 5614] ![![9, 0, 0], ![-27, -2, 1]] where
    su := ![![549, 0, 0], ![189, 9, 0]]
    hsu := by decide
    w := ![![-792495, -190449, 50526], ![-1531665, -368028, 97641]]
    hw := by decide
    g := ![![![2184185, 1930415, 141797], ![-6965702, -1422720, 0]], ![![781190, 690494, 50755], ![-2491305, -508820, 0]]]
    h := ![![![-10713569, -583135, -10811], ![31116174, 221695, 0]], ![![-20706241, -1127008, -20891], ![60138596, 428400, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N2 : Ideal.span {9} * I61N2 =  Ideal.span {B.equivFun.symm ![-88055, -21161, 5614]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E61RS2 


noncomputable def E67RS1 : RelationCertificate Table 3 ![![67, 0, 0], ![18, 1, 0]]
  ![-17, 1, 1] ![![3, 0, 0], ![-30, -2, 1]] where
    su := ![![201, 0, 0], ![54, 3, 0]]
    hsu := by decide
    w := ![![-51, 3, 3], ![510, 39, -6]]
    hw := by decide
    g := ![![![-13, -336, -33], ![535, 111, 0]], ![![-4, -95, -9], ![150, 31, 0]]]
    h := ![![![-11, -709, -125], ![40, 2792, 0]], ![![-34, 7059, 1246], ![136, -27828, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {3} * I67N1 =  Ideal.span {B.equivFun.symm ![-17, 1, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E67RS1 


noncomputable def E71RS1 : RelationCertificate Table 9 ![![71, 0, 0], ![28, 1, 0]]
  ![-3881, -2345, 535] ![![9, 0, 0], ![-27, -2, 1]] where
    su := ![![639, 0, 0], ![252, 9, 0]]
    hsu := by decide
    w := ![![-34929, -21105, 4815], ![-315693, -51318, 15129]]
    hw := by decide
    g := ![![![5174309, 4532113, 313632], ![-16495126, -3380412, 0]], ![![2047490, 1785650, 119913], ![-6525920, -1339517, 0]]]
    h := ![![![233461, 8068, -19], ![-592129, 628, 0]], ![![2145073, 74489, -205], ![-5440545, 5412, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {9} * I71N1 =  Ideal.span {B.equivFun.symm ![-3881, -2345, 535]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E71RS1 


noncomputable def E73RS0 : RelationCertificate Table 9 ![![73, 0, 0], ![0, 1, 0]]
  ![-19783, -7279, -1861] ![![9, 0, 0], ![-27, -2, 1]] where
    su := ![![657, 0, 0], ![0, 9, 0]]
    hsu := by decide
    w := ![![-178047, -65511, -16749], ![-256887, -94518, -24165]]
    hw := by decide
    g := ![![![-485, -515, -36], ![1634, 385, 0]], ![![-927, -836, -62], ![3039, 616, 0]]]
    h := ![![![-271, -16234, 48386], ![-210, -1178013, 0]], ![![-391, -23422, 69810], ![-301, -1699605, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N0 : Ideal.span {9} * I73N0 =  Ideal.span {B.equivFun.symm ![-19783, -7279, -1861]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E73RS0 
