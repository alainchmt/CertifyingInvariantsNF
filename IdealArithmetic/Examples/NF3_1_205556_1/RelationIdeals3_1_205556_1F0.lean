import IdealArithmetic.Examples.NF3_1_205556_1.PrimesBelow3_1_205556_1F0
import IdealArithmetic.Examples.NF3_1_205556_1.ClassGroupData3_1_205556_1

set_option linter.all false

noncomputable section


noncomputable def E2RS1 : RelationCertificate Table 2 ![![2, 0, 0], ![1, 1, 0]]
  ![61791, 8142, -1369] ![![2, 0, 0], ![-52, -5, 1]] where
    su := ![![4, 0, 0], ![2, 2, 0]]
    hsu := by decide
    w := ![![123582, 16284, -2738], ![1043176, 62838, -15882]]
    hw := by decide
    g := ![![![933110, -10752206, -2178161], ![1530998, 0, 0]], ![![5281655, -60861411, -12329183], ![8666003, 0, 0]]]
    h := ![![![41194, 18954, 3900], ![-20597, -9169, 0]], ![![347724, 144148, 37538], ![-173860, -83017, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {2} * I2N1 =  Ideal.span {B.equivFun.symm ![61791, 8142, -1369]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS1 


noncomputable def E7RS0 : RelationCertificate Table 2 ![![7, 0, 0], ![-54, -5, 1]]
  ![-459797, -23277, 6572] ![![2, 0, 0], ![-52, -5, 1]] where
    su := ![![14, 0, 0], ![-108, -10, 2]]
    hsu := by decide
    w := ![![-919594, -46554, 13144], ![7966536, 941014, -165968]]
    hw := by decide
    g := ![![![-7147823, 82365828, 16685504], ![-11727997, 0, 0]], ![![-933058, 10752211, 2178160], ![-1530996, 0, 0]]]
    h := ![![![-1325, 2634, -253], ![8343, 0, 0]], ![![8040, 15271, -1466], ![-72722, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {2} * I7N0 =  Ideal.span {B.equivFun.symm ![-459797, -23277, 6572]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 2 ![![7, 0, 0], ![-2, 1, 0]]
  ![-5, -1, 0] ![![2, 0, 0], ![-52, -5, 1]] where
    su := ![![14, 0, 0], ![-4, 2, 0]]
    hsu := by decide
    w := ![![-10, -2, 0], ![-24, -2, 0]]
    hw := by decide
    g := ![![![1, 0, 0], ![-1, 0, 0]], ![![50, 5, -1], ![3, 0, 0]]]
    h := ![![![-17, 10, -1], ![-57, 7, 0]], ![![-44, 23, -1], ![-148, 7, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {2} * I7N1 =  Ideal.span {B.equivFun.symm ![-5, -1, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E7RS1 


noncomputable def E19RS1 : RelationCertificate Table 2 ![![19, 0, 0], ![-7, 1, 0]]
  ![7909337, 2966487, 287430] ![![2, 0, 0], ![-52, -5, 1]] where
    su := ![![38, 0, 0], ![-14, 2, 0]]
    hsu := by decide
    w := ![![15818674, 5932974, 574860], ![23046184, 8643734, 837512]]
    hw := by decide
    g := ![![![-341, 3253, -323], ![805, 0, 0]], ![![237, -2091, 205], ![-338, 0, 0]]]
    h := ![![![110446699, -17069741, 230448], ![298653992, -4091082, 0]], ![![160909490, -24868858, 335739], ![435108174, -5960285, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {2} * I19N1 =  Ideal.span {B.equivFun.symm ![7909337, 2966487, 287430]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E19RS1 


noncomputable def E19RS2 : RelationCertificate Table 2 ![![19, 0, 0], ![-3, 1, 0]]
  ![1207245, 452791, 43872] ![![2, 0, 0], ![-52, -5, 1]] where
    su := ![![38, 0, 0], ![-6, 2, 0]]
    hsu := by decide
    w := ![![2414490, 905582, 87744], ![3517664, 1319340, 127834]]
    hw := by decide
    g := ![![![131, -382, 55], ![-1405, 0, 0]], ![![-23, 228, -30], ![594, 0, 0]]]
    h := ![![![6715503, -2243371, 18936], ![42129104, -315912, 0]], ![![9783796, -3268364, 27589], ![61377764, -460274, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N2 : Ideal.span {2} * I19N2 =  Ideal.span {B.equivFun.symm ![1207245, 452791, 43872]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E19RS2 


noncomputable def E31RS0 : RelationCertificate Table 2 ![![31, 0, 0], ![14, 1, 0]]
  ![-57, -21, -2] ![![2, 0, 0], ![-52, -5, 1]] where
    su := ![![62, 0, 0], ![28, 2, 0]]
    hsu := by decide
    w := ![![-114, -42, -4], ![-160, -60, -6]]
    hw := by decide
    g := ![![![37, 8, -1], ![-9, 0, 0]], ![![46, 6, -1], ![-1, 0, 0]]]
    h := ![![![-705, -78, -2], ![1557, 60, 0]], ![![-988, -98, -2], ![2182, 59, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N0 : Ideal.span {2} * I31N0 =  Ideal.span {B.equivFun.symm ![-57, -21, -2]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E31RS0 


noncomputable def E31RS2 : RelationCertificate Table 2 ![![31, 0, 0], ![-2, 1, 0]]
  ![605, 227, 22] ![![2, 0, 0], ![-52, -5, 1]] where
    su := ![![62, 0, 0], ![-4, 2, 0]]
    hsu := by decide
    w := ![![1210, 454, 44], ![1768, 662, 64]]
    hw := by decide
    g := ![![![47, 38, -4], ![-9, 0, 0]], ![![34, -4, 0], ![5, 0, 0]]]
    h := ![![![1965, -968, 2], ![30155, -40, 0]], ![![2872, -1415, 3], ![44074, -61, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N2 : Ideal.span {2} * I31N2 =  Ideal.span {B.equivFun.symm ![605, 227, 22]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E31RS2 
