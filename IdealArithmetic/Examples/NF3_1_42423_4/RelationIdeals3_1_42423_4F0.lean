import IdealArithmetic.Examples.NF3_1_42423_4.PrimesBelow3_1_42423_4F0
import IdealArithmetic.Examples.NF3_1_42423_4.ClassGroupData3_1_42423_4

set_option linter.all false

noncomputable section


noncomputable def E3RS0 : RelationCertificate Table 1 ![![3, 0, 0], ![5, 1, 1]]
  ![1, 0, 0] ![![3, 0, 0], ![5, 1, 1]] where
    su := ![![3, 0, 0], ![5, 1, 1]]
    hsu := by decide
    w := ![![3, 0, 0], ![5, 1, 1]]
    hw := by decide
    g := ![![![11, 22, -18], ![30, 0, -12]], ![![20, 34, -26], ![43, 0, -18]]]
    h := ![![![11, 22, -18], ![30, 0, -12]], ![![20, 34, -26], ![43, 0, -18]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {1} * I3N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 3 ![![3, 0, 0], ![3, 1, 1]]
  ![7, -2, 0] ![![3, 0, 0], ![5, 1, 1]] where
    su := ![![9, 0, 0], ![9, 3, 3]]
    hsu := by decide
    w := ![![21, -6, 0], ![-39, 9, 3]]
    hw := by decide
    g := ![![![166, 249, -185], ![299, 0, -130]], ![![204, 298, -224], ![373, 0, -156]]]
    h := ![![![383, -160, -66], ![310, -56, 0]], ![![-714, 296, 122], ![-573, 104, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {3} * I3N1 =  Ideal.span {B.equivFun.symm ![7, -2, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E3RS1 


noncomputable def E7RS1 : RelationCertificate Table 3 ![![7, 0, 0], ![-2, 1, 0]]
  ![2, -1, 0] ![![3, 0, 0], ![5, 1, 1]] where
    su := ![![21, 0, 0], ![-6, 3, 0]]
    hsu := by decide
    w := ![![6, -3, 0], ![-27, 3, 0]]
    hw := by decide
    g := ![![![464, 713, -527], ![836, 0, -372]], ![![-1, 0, 0], ![0, 0, 0]]]
    h := ![![![-16, -19, 54], ![6, -126, 0]], ![![69, 73, -216], ![-6, 504, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {3} * I7N1 =  Ideal.span {B.equivFun.symm ![2, -1, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E7RS1 


noncomputable def E7RS2 : RelationCertificate Table 3 ![![7, 0, 0], ![-1, 1, 0]]
  ![22, 3, 2] ![![3, 0, 0], ![4, 0, 1]] where
    su := ![![21, 0, 0], ![-3, 3, 0]]
    hsu := by decide
    w := ![![66, 9, 6], ![156, 21, 15]]
    hw := by decide
    g := ![![![-2, -1, -2], ![5, 0, 0]], ![![-1, 1, 0], ![-1, 0, 0]]]
    h := ![![![-358, -7, 1106], ![52, -2580, 0]], ![![-847, -16, 2615], ![119, -6100, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N2 : Ideal.span {3} * I7N2 =  Ideal.span {B.equivFun.symm ![22, 3, 2]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E7RS2 


noncomputable def E13RS0 : RelationCertificate Table 3 ![![13, 0, 0], ![6, 1, 0]]
  ![-223, -31, -21] ![![3, 0, 0], ![5, 1, 1]] where
    su := ![![39, 0, 0], ![18, 3, 0]]
    hsu := by decide
    w := ![![-669, -93, -63], ![-2577, -360, -243]]
    hw := by decide
    g := ![![![-14, -19, 14], ![-19, 0, 9]], ![![-7, -14, 8], ![-11, 0, 6]]]
    h := ![![![-975, 6514, 2793], ![57, -12110, 0]], ![![-3752, 25091, 10758], ![212, -46645, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {3} * I13N0 =  Ideal.span {B.equivFun.symm ![-223, -31, -21]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 3 ![![13, 0, 0], ![-5, 1, 0]]
  ![-5, 1, 0] ![![3, 0, 0], ![5, 1, 1]] where
    su := ![![39, 0, 0], ![-15, 3, 0]]
    hsu := by decide
    w := ![![-15, 3, 0], ![12, -6, -3]]
    hw := by decide
    g := ![![![-135, -200, 147], ![-234, 0, 104]], ![![56, 91, -69], ![111, 0, -48]]]
    h := ![![![2, 8, -6], ![1, 26, 0]], ![![-1, -7, 5], ![1, -22, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {3} * I13N1 =  Ideal.span {B.equivFun.symm ![-5, 1, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E13RS1 


noncomputable def E13RS2 : RelationCertificate Table 3 ![![13, 0, 0], ![-1, 1, 0]]
  ![11, 5, -9] ![![3, 0, 0], ![5, 1, 1]] where
    su := ![![39, 0, 0], ![-3, 3, 0]]
    hsu := by decide
    w := ![![33, 15, -27], ![105, -66, 39]]
    hw := by decide
    g := ![![![250, -31, -32], ![399, 0, 13]], ![![49, 2, -13], ![87, 0, -2]]]
    h := ![![![-368, -2, 1113], ![31, -4826, 0]], ![![-1281, -10, 3877], ![108, -16796, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N2 : Ideal.span {3} * I13N2 =  Ideal.span {B.equivFun.symm ![11, 5, -9]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E13RS2 


noncomputable def E23RS0 : RelationCertificate Table 3 ![![23, 0, 0], ![-11, 1, 0]]
  ![286, 40, 27] ![![3, 0, 0], ![5, 1, 1]] where
    su := ![![69, 0, 0], ![-33, 3, 0]]
    hsu := by decide
    w := ![![858, 120, 81], ![3315, 462, 312]]
    hw := by decide
    g := ![![![22, 47, -29], ![48, 0, -23]], ![![-15, -27, 14], ![-21, 0, 12]]]
    h := ![![![89, 695, -207], ![15, 1596, 0]], ![![310, 2689, -800], ![-13, 6168, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N0 : Ideal.span {3} * I23N0 =  Ideal.span {B.equivFun.symm ![286, 40, 27]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E23RS0 


noncomputable def E23RS1 : RelationCertificate Table 3 ![![23, 0, 0], ![-9, 1, 0]]
  ![26, -3, -5] ![![3, 0, 0], ![4, 0, 1]] where
    su := ![![69, 0, 0], ![-27, 3, 0]]
    hsu := by decide
    w := ![![78, -9, -15], ![105, -66, 39]]
    hw := by decide
    g := ![![![394, 149, -68], ![506, 0, 0]], ![![-97, -36, 16], ![-121, 0, 0]]]
    h := ![![![47, 370, -139], ![-1, 1064, 0]], ![![72, 547, -205], ![5, 1576, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {3} * I23N1 =  Ideal.span {B.equivFun.symm ![26, -3, -5]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E23RS1 


noncomputable def E29RS1 : RelationCertificate Table 3 ![![29, 0, 0], ![4, 1, 0]]
  ![4, 1, 0] ![![3, 0, 0], ![5, 1, 1]] where
    su := ![![87, 0, 0], ![12, 3, 0]]
    hsu := by decide
    w := ![![12, 3, 0], ![57, 3, 6]]
    hw := by decide
    g := ![![![-291, -446, 328], ![-519, 0, 232]], ![![-34, -47, 33], ![-51, 0, 24]]]
    h := ![![![-46, 209, 126], ![30, -1218, 0]], ![![-203, 1006, 604], ![17, -5838, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {3} * I29N1 =  Ideal.span {B.equivFun.symm ![4, 1, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E29RS1 


noncomputable def E29RS2 : RelationCertificate Table 3 ![![29, 0, 0], ![-7, 1, 0]]
  ![-308, -43, -29] ![![3, 0, 0], ![4, 0, 1]] where
    su := ![![87, 0, 0], ![-21, 3, 0]]
    hsu := by decide
    w := ![![-924, -129, -87], ![-2199, -306, -207]]
    hw := by decide
    g := ![![![-12, 9, 0], ![-8, 0, 0]], ![![-1, -2, 1], ![2, 0, 0]]]
    h := ![![![-2979, -17963, 8978], ![102, -86797, 0]], ![![-7088, -42755, 21369], ![253, -206590, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N2 : Ideal.span {3} * I29N2 =  Ideal.span {B.equivFun.symm ![-308, -43, -29]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E29RS2 
