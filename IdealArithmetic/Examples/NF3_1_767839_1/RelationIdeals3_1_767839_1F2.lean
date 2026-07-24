import IdealArithmetic.Examples.NF3_1_767839_1.PrimesBelow3_1_767839_1F2
import IdealArithmetic.Examples.NF3_1_767839_1.ClassGroupData3_1_767839_1

set_option linter.all false

noncomputable section


noncomputable def E97RS1 : RelationCertificate Table 27 ![![97, 0, 0], ![43, 1, 0]]
  ![259, -112, 11] ![![27, 0, 0], ![-7, 1, 0]] where
    su := ![![2619, 0, 0], ![1161, 27, 0]]
    hsu := by decide
    w := ![![6993, -3024, 297], ![-108, 702, -189]]
    hw := by decide
    g := ![![![225585, 25155354, -3598270], ![873217, 97152792, 0]], ![![103582, 11552421, -1652481], ![401020, 44616748, 0]]]
    h := ![![![97227, 3373, 26], ![-219320, -2511, 0]], ![![-1306, -70, -1], ![2946, 90, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {27} * I97N1 =  Ideal.span {B.equivFun.symm ![259, -112, 11]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E97RS1 


noncomputable def E101RS0 : RelationCertificate Table 27 ![![101, 0, 0], ![14, 1, 0]]
  ![-51259, -4175, -1175] ![![27, 0, 0], ![-7, 1, 0]] where
    su := ![![2727, 0, 0], ![378, 27, 0]]
    hsu := by decide
    w := ![![-1383993, -112725, -31725], ![176688, 14391, 4050]]
    hw := by decide
    g := ![![![-422754, -46982685, 6720440], ![-1630490, -181451905, 0]], ![![-56505, -6279866, 898277], ![-217924, -24253479, 0]]]
    h := ![![![-15778137, -1152766, -1851], ![113824327, 185776, 0]], ![![2014308, 147163, 236], ![-14531326, -23686, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N0 : Ideal.span {27} * I101N0 =  Ideal.span {B.equivFun.symm ![-51259, -4175, -1175]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E101RS0 


noncomputable def E101RS1 : RelationCertificate Table 27 ![![101, 0, 0], ![16, 1, 0]]
  ![-1906, -1535, 583] ![![27, 0, 0], ![-7, 1, 0]] where
    su := ![![2727, 0, 0], ![432, 27, 0]]
    hsu := by decide
    w := ![![-51462, -41445, 15741], ![103707, -9234, -5616]]
    hw := by decide
    g := ![![![785963, 80253, 18558], ![-200776, 17600, 0]], ![![152163, 15394, 3613], ![-38851, 2860, 0]]]
    h := ![![![-5450, -367, 5], ![34284, 78, 0]], ![![10909, 693, -1], ![-68623, -107, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {27} * I101N1 =  Ideal.span {B.equivFun.symm ![-1906, -1535, 583]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E101RS1 


noncomputable def E127RS1 : RelationCertificate Table 81 ![![127, 0, 0], ![34, 1, 0]]
  ![-24889, 883, 1723] ![![81, 0, 0], ![-7, 1, 0]] where
    su := ![![10287, 0, 0], ![2754, 81, 0]]
    hsu := by decide
    w := ![![-2016009, 71523, 139563], ![441288, -84483, -11178]]
    hw := by decide
    g := ![![![-895595, -49827, -24197], ![76819, 284722, 0]], ![![-264820, -15328, -7070], ![22733, 77314, 0]]]
    h := ![![![-49121549, -1578854, -3931], ![183482701, 500960, 0]], ![![10743100, 345309, 862], ![-40128478, -109612, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N1 : Ideal.span {81} * I127N1 =  Ideal.span {B.equivFun.symm ![-24889, 883, 1723]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E127RS1 


noncomputable def E131RS1 : RelationCertificate Table 3 ![![131, 0, 0], ![41, 1, 0]]
  ![-38651, -3148, -886] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![393, 0, 0], ![123, 3, 0]]
    hsu := by decide
    w := ![![-115953, -9444, -2658], ![-98679, -8037, -2262]]
    hw := by decide
    g := ![![![9920, 95599, -105234], ![28563, 315704, 0]], ![![3182, 30680, -33770], ![9169, 101308, 0]]]
    h := ![![![-180419, -4837, -17], ![575518, 1341, 0]], ![![-153531, -4138, -15], ![489748, 1211, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {3} * I131N1 =  Ideal.span {B.equivFun.symm ![-38651, -3148, -886]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E131RS1 


noncomputable def E137RS1 : RelationCertificate Table 9 ![![137, 0, 0], ![30, 1, 0]]
  ![-1, -2, 1] ![![9, 0, 0], ![2, 1, 0]] where
    su := ![![1233, 0, 0], ![270, 9, 0]]
    hsu := by decide
    w := ![![-9, -18, 9], ![153, -36, 0]]
    hw := by decide
    g := ![![![66988, -2846282, -1439884], ![-301365, 12958960, 0]], ![![14682, -623843, -315591], ![-66049, 2840320, 0]]]
    h := ![![![-53, -2, 0], ![242, 1, 0]], ![![61, 2, 0], ![-278, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {9} * I137N1 =  Ideal.span {B.equivFun.symm ![-1, -2, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E137RS1 
