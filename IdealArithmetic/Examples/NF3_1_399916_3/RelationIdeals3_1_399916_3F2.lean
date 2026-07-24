import IdealArithmetic.Examples.NF3_1_399916_3.PrimesBelow3_1_399916_3F2
import IdealArithmetic.Examples.NF3_1_399916_3.ClassGroupData3_1_399916_3

set_option linter.all false

noncomputable section


noncomputable def E97RS1 : RelationCertificate Table 11 ![![97, 0, 0], ![5, 1, 0]]
  ![120, -5, -4] ![![11, 0, 0], ![2, 1, 0]] where
    su := ![![1067, 0, 0], ![55, 11, 0]]
    hsu := by decide
    w := ![![1320, -55, -44], ![-253, 110, -22]]
    hw := by decide
    g := ![![![-18, -200, -210], ![-19, 1180, 0]], ![![3, -13, -14], ![0, 80, 0]]]
    h := ![![![-960, -4829, -1932], ![-92, 93700, 0]], ![![181, 934, 374], ![112, -18140, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {11} * I97N1 =  Ideal.span {B.equivFun.symm ![120, -5, -4]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E97RS1 


noncomputable def E101RS1 : RelationCertificate Table 121 ![![101, 0, 0], ![42, 1, 0]]
  ![102, 15, 1] ![![121, 0, 0], ![-31, 1, 0]] where
    su := ![![12221, 0, 0], ![5082, 121, 0]]
    hsu := by decide
    w := ![![12342, 1815, 121], ![-3025, -363, 0]]
    hw := by decide
    g := ![![![-287, 10616, -685], ![214, 41444, 0]], ![![-108, 4881, -315], ![192, 19058, 0]]]
    h := ![![![-2721, -162030, -7717], ![-2733, 389709, 0]], ![![653, 39725, 1892], ![704, -95546, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {121} * I101N1 =  Ideal.span {B.equivFun.symm ![102, 15, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E101RS1 


noncomputable def E107RS1 : RelationCertificate Table 121 ![![107, 0, 0], ![33, 1, 0]]
  ![-9139, -1376, -487] ![![121, 0, 0], ![-31, 1, 0]] where
    su := ![![12947, 0, 0], ![3993, 121, 0]]
    hsu := by decide
    w := ![![-1105819, -166496, -58927], ![222519, 33517, 11858]]
    hw := by decide
    g := ![![![76387558, -2700341979, 174237945], ![-41887168, -10541395698, 0]], ![![24611129, -870016557, 56137296], ![-13495486, -3396306416, 0]]]
    h := ![![![-11726634, -468247825, -28383187], ![-7992714, 1518500261, 0]], ![![2359675, 94222957, 5711394], ![1608368, -305559530, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {121} * I107N1 =  Ideal.span {B.equivFun.symm ![-9139, -1376, -487]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E107RS1 


noncomputable def E127RS1 : RelationCertificate Table 121 ![![127, 0, 0], ![-25, 1, 0]]
  ![25709, -6216, 723] ![![121, 0, 0], ![-31, 1, 0]] where
    su := ![![15367, 0, 0], ![-3025, 121, 0]]
    hsu := by decide
    w := ![![3110789, -752136, 87483], ![-714989, 218405, -34122]]
    hw := by decide
    g := ![![![-35088379085, 1240391504194, -80035521711], ![19240754186, 4842148839567, 0]], ![![6962415039, -246124928949, 15881063950], ![-3817849422, -960804336614, 0]]]
    h := ![![![-189946118, 5130878377, -410519271], ![77791655, 26067974070, 0]], ![![43699517, -1180423493, 94445152], ![-17896909, -5997267293, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N1 : Ideal.span {121} * I127N1 =  Ideal.span {B.equivFun.symm ![25709, -6216, 723]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E127RS1 
