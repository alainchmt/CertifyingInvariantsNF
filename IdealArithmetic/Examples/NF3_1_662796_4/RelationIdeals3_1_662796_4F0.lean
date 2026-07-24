import IdealArithmetic.Examples.NF3_1_662796_4.PrimesBelow3_1_662796_4F0
import IdealArithmetic.Examples.NF3_1_662796_4.ClassGroupData3_1_662796_4

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 13 ![![2, 0, 0], ![0, 1, 0]]
  ![-6, -1, 0] ![![13, 0, 0], ![-78, -6, 1]] where
    su := ![![26, 0, 0], ![0, 13, 0]]
    hsu := by decide
    w := ![![-78, -13, 0], ![-26, 0, 0]]
    hw := by decide
    g := ![![![78, 6, -1], ![12, 0, 0]], ![![77, 6, -1], ![16, 0, 0]]]
    h := ![![![-3, 0, 0], ![-1, 0, 0]], ![![-1, 0, 0], ![0, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {13} * I2N0 =  Ideal.span {B.equivFun.symm ![-6, -1, 0]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E2RS0 


noncomputable def E3RS0 : RelationCertificate Table 169 ![![3, 0, 0], ![1, 1, 0]]
  ![897, 64, -11] ![![169, 0, 0], ![-71, 1, 0]] where
    su := ![![507, 0, 0], ![169, 169, 0]]
    hsu := by decide
    w := ![![151593, 10816, -1859], ![-69121, -4901, 845]]
    hw := by decide
    g := ![![![35, -1208, 17], ![84, -2874, 0]], ![![38, -500, 7], ![93, -1188, 0]]]
    h := ![![![488, 235, 21], ![-567, -74, 0]], ![![-224, -109, -10], ![263, 35, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {169} * I3N0 =  Ideal.span {B.equivFun.symm ![897, 64, -11]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E3RS0 


noncomputable def E13RS0 : RelationCertificate Table 1 ![![13, 0, 0], ![0, 1, 0]]
  ![1, 0, 0] ![![13, 0, 0], ![0, 1, 0]] where
    su := ![![13, 0, 0], ![0, 1, 0]]
    hsu := by decide
    w := ![![13, 0, 0], ![0, 1, 0]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {1} * I13N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 169 ![![13, 0, 0], ![6, 1, 0]]
  ![355, 111, 9] ![![169, 0, 0], ![-26, 46, 1]] where
    su := ![![2197, 0, 0], ![1014, 169, 0]]
    hsu := by decide
    w := ![![59995, 18759, 1521], ![250120, 77740, 6253]]
    hw := by decide
    g := ![![![63, -13, -1], ![61, 0, 0]], ![![26, -45, -1], ![166, 0, 0]]]
    h := ![![![135757, 33102, 1746], ![-294081, -22689, 0]], ![![565816, 137982, 7280], ![-1225688, -94603, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {169} * I13N1 =  Ideal.span {B.equivFun.symm ![355, 111, 9]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E13RS1 


noncomputable def E13RS2 : RelationCertificate Table 1 ![![13, 0, 0], ![-6, 1, 0]]
  ![1, 0, 0] ![![13, 0, 0], ![-6, 1, 0]] where
    su := ![![13, 0, 0], ![-6, 1, 0]]
    hsu := by decide
    w := ![![13, 0, 0], ![-6, 1, 0]]
    hw := by decide
    g := ![![![79, -13, 0], ![169, 0, 0]], ![![-30, 11, -1], ![-64, 13, 0]]]
    h := ![![![79, -13, 0], ![169, 0, 0]], ![![-30, 11, -1], ![-64, 13, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N2 : Ideal.span {1} * I13N2 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E13RS2 


noncomputable def E17RS0 : RelationCertificate Table 169 ![![17, 0, 0], ![4, 1, 0]]
  ![-1199, -52, 12] ![![169, 0, 0], ![-52, 1, 0]] where
    su := ![![2873, 0, 0], ![676, 169, 0]]
    hsu := by decide
    w := ![![-202631, -8788, 2028], ![68276, 2873, -676]]
    hw := by decide
    g := ![![![81, 17888, -344], ![260, 58140, 0]], ![![28, 4629, -89], ![88, 15045, 0]]]
    h := ![![![-535291, -144391, -2645], ![2274687, 44977, 0]], ![![180348, 48647, 891], ![-766378, -15151, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N0 : Ideal.span {169} * I17N0 =  Ideal.span {B.equivFun.symm ![-1199, -52, 12]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E17RS0 


noncomputable def E17RS1 : RelationCertificate Table 169 ![![17, 0, 0], ![-2, 1, 0]]
  ![173, 13, -3] ![![169, 0, 0], ![-52, 1, 0]] where
    su := ![![2873, 0, 0], ![-338, 169, 0]]
    hsu := by decide
    w := ![![29237, 2197, -507], ![-10478, -845, 169]]
    hw := by decide
    g := ![![![27, -11492, 221], ![91, -37347, 0]], ![![38, 1143, -22], ![122, 3717, 0]]]
    h := ![![![64611, -32696, 198], ![549107, -3369, 0]], ![![-23150, 11717, -72], ![-196744, 1225, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {169} * I17N1 =  Ideal.span {B.equivFun.symm ![173, 13, -3]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E17RS1 


noncomputable def E19RS0 : RelationCertificate Table 169 ![![19, 0, 0], ![0, 1, 0]]
  ![-247, -75, -6] ![![169, 0, 0], ![-52, -6, 1]] where
    su := ![![3211, 0, 0], ![0, 169, 0]]
    hsu := by decide
    w := ![![-41743, -12675, -1014], ![-6422, -2028, -169]]
    hw := by decide
    g := ![![![-35083, -4437, 402], ![11043, 13164, 0]], ![![-64314, -8135, 737], ![20254, 24134, 0]]]
    h := ![![![-13, -4, 0], ![1, -6, 0]], ![![-2, -1, 0], ![7, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N0 : Ideal.span {169} * I19N0 =  Ideal.span {B.equivFun.symm ![-247, -75, -6]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E19RS0 


noncomputable def E31RS1 : RelationCertificate Table 169 ![![31, 0, 0], ![13, 1, 0]]
  ![3, -13, 1] ![![169, 0, 0], ![-26, -6, 1]] where
    su := ![![5239, 0, 0], ![2197, 169, 0]]
    hsu := by decide
    w := ![![507, -2197, 169], ![-9464, -1352, 169]]
    hw := by decide
    g := ![![![62362763, 11028265, -716997], ![-9990037, -21860421, 0]], ![![28170117, 4981620, -323878], ![-4512491, -9874645, 0]]]
    h := ![![![-15, -2, 0], ![36, 1, 0]], ![![-214, -30, -1], ![506, 32, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {169} * I31N1 =  Ideal.span {B.equivFun.symm ![3, -13, 1]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E31RS1 
