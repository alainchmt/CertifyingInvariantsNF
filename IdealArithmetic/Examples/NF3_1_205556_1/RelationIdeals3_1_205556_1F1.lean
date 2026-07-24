import IdealArithmetic.Examples.NF3_1_205556_1.PrimesBelow3_1_205556_1F1
import IdealArithmetic.Examples.NF3_1_205556_1.ClassGroupData3_1_205556_1

set_option linter.all false

noncomputable section


noncomputable def E37RS0 : RelationCertificate Table 2 ![![37, 0, 0], ![3, 1, 0]]
  ![3, 1, 0] ![![2, 0, 0], ![-52, -5, 1]] where
    su := ![![74, 0, 0], ![6, 2, 0]]
    hsu := by decide
    w := ![![6, 2, 0], ![128, 12, -2]]
    hw := by decide
    g := ![![![43, 6, -1], ![3, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    h := ![![![9, 3, 0], ![-110, 0, 0]], ![![286, 95, 0], ![-3506, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N0 : Ideal.span {2} * I37N0 =  Ideal.span {B.equivFun.symm ![3, 1, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E37RS0 


noncomputable def E37RS1 : RelationCertificate Table 2 ![![37, 0, 0], ![7, 1, 0]]
  ![7, 1, 0] ![![2, 0, 0], ![-52, -5, 1]] where
    su := ![![74, 0, 0], ![14, 2, 0]]
    hsu := by decide
    w := ![![14, 2, 0], ![-80, -8, 2]]
    hw := by decide
    g := ![![![11, -1, 0], ![1, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    h := ![![![7, 1, 0], ![-36, 0, 0]], ![![-104, -22, -1], ![544, 38, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {2} * I37N1 =  Ideal.span {B.equivFun.symm ![7, 1, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E37RS1 


noncomputable def E41RS1 : RelationCertificate Table 2 ![![41, 0, 0], ![16, 1, 0]]
  ![4601080895, 1725687837, 167206010] ![![2, 0, 0], ![-52, -5, 1]] where
    su := ![![82, 0, 0], ![32, 2, 0]]
    hsu := by decide
    w := ![![9202161790, 3451375674, 334412020], ![13406604968, 5028300014, 487203980]]
    hw := by decide
    g := ![![![7331, -95960, 8480], ![54759, 0, 0]], ![![2216, -26845, 2419], ![11791, 0, 0]]]
    h := ![![![22995940551, 1733558879, 20405476], ![-58639530106, -669418506, 0]], ![![33502724468, 2525617299, 29728683], ![-85431775044, -975274013, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {2} * I41N1 =  Ideal.span {B.equivFun.symm ![4601080895, 1725687837, 167206010]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E41RS1 


noncomputable def E41RS2 : RelationCertificate Table 2 ![![41, 0, 0], ![17, 1, 0]]
  ![31, -3, 0] ![![2, 0, 0], ![-52, -5, 1]] where
    su := ![![82, 0, 0], ![34, 2, 0]]
    hsu := by decide
    w := ![![62, -6, 0], ![-2464, -236, 46]]
    hw := by decide
    g := ![![![47, 39, 6], ![-3, 0, 0]], ![![31, 26, 4], ![-2, 0, 0]]]
    h := ![![![427, 25, 0], ![-1028, 0, 0]], ![![-17958, -1373, -18], ![43238, 761, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N2 : Ideal.span {2} * I41N2 =  Ideal.span {B.equivFun.symm ![31, -3, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E41RS2 


noncomputable def E43RS1 : RelationCertificate Table 2 ![![43, 0, 0], ![-19, 1, 0]]
  ![140449, 52677, 5104] ![![2, 0, 0], ![-52, -5, 1]] where
    su := ![![86, 0, 0], ![-38, 2, 0]]
    hsu := by decide
    w := ![![280898, 105354, 10208], ![409240, 153490, 14872]]
    hw := by decide
    g := ![![![-45, 633, -65], ![299, 0, 0]], ![![61, -356, 36], ![-152, 0, 0]]]
    h := ![![![5489104, -328758, 2290], ![12415317, -93366, 0]], ![![7997098, -478963, 3336], ![18087926, -136012, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {2} * I43N1 =  Ideal.span {B.equivFun.symm ![140449, 52677, 5104]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E43RS1 


noncomputable def E71RS1 : RelationCertificate Table 2 ![![71, 0, 0], ![24, 1, 0]]
  ![1466503, 151057, -28404] ![![2, 0, 0], ![-52, -5, 1]] where
    su := ![![142, 0, 0], ![48, 2, 0]]
    hsu := by decide
    w := ![![2933006, 302114, -56808], ![6975712, -101132, -55690]]
    hw := by decide
    g := ![![![243263021, -2803163034, -567859159], ![399139921, 0, 0]], ![![117591044, -1355022500, -274497747], ![192940463, 0, 0]]]
    h := ![![![1466729, 68502, -145], ![-4277969, -18109, 0]], ![![3484912, 157618, 240], ![-10164204, -44885, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {2} * I71N1 =  Ideal.span {B.equivFun.symm ![1466503, 151057, -28404]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E71RS1 


noncomputable def E71RS2 : RelationCertificate Table 2 ![![71, 0, 0], ![-24, 1, 0]]
  ![429, 41, -8] ![![2, 0, 0], ![-52, -5, 1]] where
    su := ![![142, 0, 0], ![-48, 2, 0]]
    hsu := by decide
    w := ![![858, 82, -16], ![696, -150, 8]]
    hw := by decide
    g := ![![![27, 221, 43], ![-29, 0, 0]], ![![32, -39, -9], ![7, 0, 0]]]
    h := ![![![723, -8, -1], ![2121, 63, 0]], ![![564, -23, 0], ![1654, 4, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N2 : Ideal.span {2} * I71N2 =  Ideal.span {B.equivFun.symm ![429, 41, -8]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E71RS2 
