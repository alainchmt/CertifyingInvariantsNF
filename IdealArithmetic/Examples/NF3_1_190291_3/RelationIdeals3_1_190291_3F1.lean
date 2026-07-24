import IdealArithmetic.Examples.NF3_1_190291_3.PrimesBelow3_1_190291_3F1
import IdealArithmetic.Examples.NF3_1_190291_3.ClassGroupData3_1_190291_3

set_option linter.all false

noncomputable section


noncomputable def E37RS0 : RelationCertificate Table 12 ![![37, 0, 0], ![0, 1, 0]]
  ![-37, -7, 1] ![![12, 0, 0], ![-5, 1, 0]] where
    su := ![![444, 0, 0], ![0, 12, 0]]
    hsu := by decide
    w := ![![-444, -84, 12], ![444, 72, -12]]
    hw := by decide
    g := ![![![6, 4, -1], ![7, 11, 0]], ![![-1, 0, 0], ![-1, 0, 0]]]
    h := ![![![-1, 0, 0], ![-7, 1, 0]], ![![1, 0, 0], ![6, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N0 : Ideal.span {12} * I37N0 =  Ideal.span {B.equivFun.symm ![-37, -7, 1]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E37RS0 


noncomputable def E43RS1 : RelationCertificate Table 288 ![![43, 0, 0], ![-11, 1, 0]]
  ![-389, -47, 5] ![![288, 0, 0], ![67, 1, 0]] where
    su := ![![12384, 0, 0], ![-3168, 288, 0]]
    hsu := by decide
    w := ![![-112032, -13536, 1440], ![-24768, -3168, 288]]
    hw := by decide
    g := ![![![-1012972, 1321875922, 19729717], ![4354273, -5682158504, 0]], ![![282656, -368895102, -5505960], ![-1215001, 1585716483, 0]]]
    h := ![![![-557, 61, -1], ![-2142, 48, 0]], ![![-112, 21, -1], ![-430, 44, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {288} * I43N1 =  Ideal.span {B.equivFun.symm ![-389, -47, 5]} * (J0 ^ 5*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_2 E43RS1 


noncomputable def E53RS1 : RelationCertificate Table 96 ![![53, 0, 0], ![-19, 1, 0]]
  ![-95, -29, -1] ![![96, 0, 0], ![-29, 1, 0]] where
    su := ![![5088, 0, 0], ![-1824, 96, 0]]
    hsu := by decide
    w := ![![-9120, -2784, -96], ![2496, 672, 0]]
    hw := by decide
    g := ![![![9, -5077, 175], ![15, -16807, 0]], ![![21, 1769, -61], ![76, 5859, 0]]]
    h := ![![![-665, 53, -1], ![-1850, 52, 0]], ![![212, -11, 0], ![590, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {96} * I53N1 =  Ideal.span {B.equivFun.symm ![-95, -29, -1]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E53RS1 


noncomputable def E59RS1 : RelationCertificate Table 12 ![![59, 0, 0], ![-15, 1, 0]]
  ![-61, -7, 1] ![![12, 0, 0], ![-5, 1, 0]] where
    su := ![![708, 0, 0], ![-180, 12, 0]]
    hsu := by decide
    w := ![![-732, -84, 12], ![564, 48, -12]]
    hw := by decide
    g := ![![![21, 263, -53], ![23, 633, 0]], ![![-4, -65, 13], ![0, -155, 0]]]
    h := ![![![-89, 21, -1], ![-346, 60, 0]], ![![73, 10, -1], ![284, 58, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {12} * I59N1 =  Ideal.span {B.equivFun.symm ![-61, -7, 1]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E59RS1 


noncomputable def E61RS1 : RelationCertificate Table 4 ![![61, 0, 0], ![-13, 1, 0]]
  ![-69, -3, 1] ![![4, 0, 0], ![-1, 1, 0]] where
    su := ![![244, 0, 0], ![-52, 4, 0]]
    hsu := by decide
    w := ![![-276, -12, 4], ![328, 8, -4]]
    hw := by decide
    g := ![![![47, 651, -686], ![154, 2745, 0]], ![![-9, -142, 150], ![-33, -600, 0]]]
    h := ![![![-3691, 297, -1], ![-17314, 62, 0]], ![![4406, -352, 1], ![20668, -62, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {4} * I61N1 =  Ideal.span {B.equivFun.symm ![-69, -3, 1]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E61RS1 


noncomputable def E73RS1 : RelationCertificate Table 8 ![![73, 0, 0], ![30, 1, 0]]
  ![-41, -3, 1] ![![8, 0, 0], ![3, 1, 0]] where
    su := ![![584, 0, 0], ![240, 8, 0]]
    hsu := by decide
    w := ![![-328, -24, 8], ![136, 24, 0]]
    hw := by decide
    g := ![![![225, -5103, -1725], ![-550, 13797, 0]], ![![90, -2074, -701], ![-223, 5607, 0]]]
    h := ![![![-4427, -208, -2], ![10771, 147, 0]], ![![1799, 60, 0], ![-4377, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {8} * I73N1 =  Ideal.span {B.equivFun.symm ![-41, -3, 1]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E73RS1 
