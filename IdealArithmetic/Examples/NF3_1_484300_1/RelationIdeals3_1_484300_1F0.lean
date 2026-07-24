import IdealArithmetic.Examples.NF3_1_484300_1.PrimesBelow3_1_484300_1F0
import IdealArithmetic.Examples.NF3_1_484300_1.ClassGroupData3_1_484300_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 3 ![![2, 0, 0], ![1, 1, 0]]
  ![5, 1, 0] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![6, 0, 0], ![3, 3, 0]]
    hsu := by decide
    w := ![![15, 3, 0], ![6, 6, 3]]
    hw := by decide
    g := ![![![80, 0, -1], ![30, 0, 2]], ![![58, 5, -2], ![21, 0, 2]]]
    h := ![![![2, 0, 0], ![1, 0, 0]], ![![4, 4, -1], ![-7, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {3} * I2N0 =  Ideal.span {B.equivFun.symm ![5, 1, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS0 


noncomputable def E3RS0 : RelationCertificate Table 1 ![![3, 0, 0], ![1, 1, 0]]
  ![1, 0, 0] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![3, 0, 0], ![1, 1, 0]]
    hsu := by decide
    w := ![![3, 0, 0], ![1, 1, 0]]
    hw := by decide
    g := ![![![219, 6, -4], ![78, 0, 6]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![219, 6, -4], ![78, 0, 6]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {1} * I3N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 9 ![![3, 0, 0], ![-1, 1, 0]]
  ![-113, 14, 24] ![![9, 0, 0], ![4, 1, 0]] where
    su := ![![27, 0, 0], ![-9, 9, 0]]
    hsu := by decide
    w := ![![-1017, 126, 216], ![-3366, -441, 162]]
    hw := by decide
    g := ![![![-1703, -16130, -12164], ![-2544, 36664, -8]], ![![-1154, 6296, 4478], ![197, -13749, 3]]]
    h := ![![![-33, 0, 8], ![14, 0, 0]], ![![-114, -27, 6], ![32, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {9} * I3N1 =  Ideal.span {B.equivFun.symm ![-113, 14, 24]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E3RS1 


noncomputable def E5RS0 : RelationCertificate Table 9 ![![5, 0, 0], ![-2, 1, 0]]
  ![536, -41, 21] ![![9, 0, 0], ![4, 1, 0]] where
    su := ![![45, 0, 0], ![-18, 9, 0]]
    hsu := by decide
    w := ![![4824, -369, 189], ![-459, 36, -18]]
    hw := by decide
    g := ![![![13687936, 79604410, 60946334], ![14928471, -182839896, 536]], ![![3421821, 19900136, 15235843], ![3731938, -45707752, 134]]]
    h := ![![![-7090, 18282, -29379], ![6493, 48972, 0]], ![![677, -1742, 2798], ![-614, -4664, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {9} * I5N0 =  Ideal.span {B.equivFun.symm ![536, -41, 21]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E5RS0 


noncomputable def E11RS0 : RelationCertificate Table 9 ![![11, 0, 0], ![8, 2, 1]]
  ![68, -5, 3] ![![9, 0, 0], ![4, 1, 0]] where
    su := ![![99, 0, 0], ![72, 18, 9]]
    hsu := by decide
    w := ![![612, -45, 27], ![-99, 0, 0]]
    hw := by decide
    g := ![![![201, 20, -11], ![95, 3, 18]], ![![144, 14, -8], ![74, 2, 13]]]
    h := ![![![4, -1, 0], ![3, 0, 0]], ![![-1, 0, 0], ![0, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {9} * I11N0 =  Ideal.span {B.equivFun.symm ![68, -5, 3]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 3 ![![11, 0, 0], ![4, 1, 0]]
  ![-374, -49, 18] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![33, 0, 0], ![12, 3, 0]]
    hsu := by decide
    w := ![![-1122, -147, 54], ![-2619, -711, -111]]
    hw := by decide
    g := ![![![-53752, 8093, -1909], ![-15218, 0, -176]], ![![1662, -715, 196], ![319, 0, -56]]]
    h := ![![![-105, -388, -291], ![-73, 1073, 0]], ![![-237, -873, -653], ![-162, 2382, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {3} * I11N1 =  Ideal.span {B.equivFun.symm ![-374, -49, 18]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E11RS1 


noncomputable def E13RS0 : RelationCertificate Table 3 ![![13, 0, 0], ![14, -3, 1]]
  ![2219, -170, 87] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![39, 0, 0], ![42, -9, 3]]
    hsu := by decide
    w := ![![6657, -510, 261], ![-8565, 657, -336]]
    hw := by decide
    g := ![![![701, 22, -13], ![242, 0, 19]], ![![756, 23, -14], ![260, 0, 21]]]
    h := ![![![77, 7, 0], ![87, 0, 0]], ![![-113, -6, -1], ![-99, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {3} * I13N0 =  Ideal.span {B.equivFun.symm ![2219, -170, 87]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 9 ![![13, 0, 0], ![-5, 1, 0]]
  ![3965, 94, -465] ![![9, 0, 0], ![4, 1, 0]] where
    su := ![![117, 0, 0], ![-45, 9, 0]]
    hsu := by decide
    w := ![![35685, 846, -4185], ![72684, 11781, -2043]]
    hw := by decide
    g := ![![![-1064573, 2129234, 1416259], ![-236554, -4444616, 34]], ![![932809, -887151, -516959], ![316018, 1699412, -13]]]
    h := ![![![-4248, 30059, -18249], ![3947, 78924, 0]], ![![-8391, 59608, -36083], ![7825, 156284, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {9} * I13N1 =  Ideal.span {B.equivFun.symm ![3965, 94, -465]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E13RS1 


noncomputable def E29RS0 : RelationCertificate Table 3 ![![29, 0, 0], ![2, 1, 0]]
  ![2, 1, 0] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![87, 0, 0], ![6, 3, 0]]
    hsu := by decide
    w := ![![6, 3, 0], ![3, 3, 3]]
    hw := by decide
    g := ![![![815795, 25748, -14907], ![280517, 0, 22360]], ![![56917, 1796, -1040], ![19572, 0, 1560]]]
    h := ![![![-9, -18, -27], ![1, 261, 0]], ![![-5, -9, -13], ![10, 126, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N0 : Ideal.span {3} * I29N0 =  Ideal.span {B.equivFun.symm ![2, 1, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E29RS0 


noncomputable def E29RS1 : RelationCertificate Table 3 ![![29, 0, 0], ![13, 1, 0]]
  ![624419, -47846, 24489] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![87, 0, 0], ![39, 3, 0]]
    hsu := by decide
    w := ![![1873257, -143538, 73467], ![-2411085, 184749, -94560]]
    hw := by decide
    g := ![![![692956, 21827, -12709], ![238263, 0, 18980]], ![![322947, 10189, -5918], ![111048, 0, 8840]]]
    h := ![![![10425685, 202848464, 46905261], ![11668378, -453409360, 0]], ![![-13419005, -261087983, -60372160], ![-15018430, 583587040, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {3} * I29N1 =  Ideal.span {B.equivFun.symm ![624419, -47846, 24489]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E29RS1 
