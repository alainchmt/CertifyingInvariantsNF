import IdealArithmetic.Examples.NF3_1_703404_2.PrimesBelow3_1_703404_2F4
import IdealArithmetic.Examples.NF3_1_703404_2.ClassGroupData3_1_703404_2

set_option linter.all false

noncomputable section


noncomputable def E197RS1 : RelationCertificate Table 14 ![![197, 0, 0], ![94, 1, 0]]
  ![-304, -65, 10] ![![14, 0, 0], ![-42, -4, 1]] where
    su := ![![2758, 0, 0], ![1316, 14, 0]]
    hsu := by decide
    w := ![![-4256, -910, 140], ![-14742, -364, 196]]
    hw := by decide
    g := ![![![4638, 322, 295], ![-13899, -2466, 0]], ![![2240, 158, 142], ![-6678, -1185, 0]]]
    h := ![![![-156408, -2515, -9], ![327788, 1783, 0]], ![![-540617, -8484, -29], ![1132984, 5727, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R197N1 : Ideal.span {14} * I197N1 =  Ideal.span {B.equivFun.symm ![-304, -65, 10]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E197RS1 


noncomputable def E197RS2 : RelationCertificate Table 98 ![![197, 0, 0], ![-95, 1, 0]]
  ![-3368, -66, 43] ![![98, 0, 0], ![38, 1, 0]] where
    su := ![![19306, 0, 0], ![-9310, 98, 0]]
    hsu := by decide
    w := ![![-330064, -6468, 4214], ![-116718, -3038, 1568]]
    hw := by decide
    g := ![![![-363047, 105562724, 2778220], ![936477, -272265283, 0]], ![![175652, -51084480, -1344451], ![-453083, 131756078, 0]]]
    h := ![![![-141814, 1703, -2], ![-294042, 437, 0]], ![![-50113, 630, -1], ![-103906, 213, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R197N2 : Ideal.span {98} * I197N2 =  Ideal.span {B.equivFun.symm ![-3368, -66, 43]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E197RS2 


noncomputable def E223RS1 : RelationCertificate Table 98 ![![223, 0, 0], ![18, 1, 0]]
  ![706, 53, -13] ![![98, 0, 0], ![-28, -4, 1]] where
    su := ![![21854, 0, 0], ![1764, 98, 0]]
    hsu := by decide
    w := ![![69188, 5194, -1274], ![7742, -784, 0]]
    hw := by decide
    g := ![![![-3474624, -504584, 47125], ![1013847, 1408020, 0]], ![![-275252, -39972, 3733], ![80340, 111543, 0]]]
    h := ![![![3346, 187, 0], ![-41414, -13, 0]], ![![361, 20, 0], ![-4468, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R223N1 : Ideal.span {98} * I223N1 =  Ideal.span {B.equivFun.symm ![706, 53, -13]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E223RS1 


noncomputable def E229RS1 : RelationCertificate Table 14 ![![229, 0, 0], ![-29, 1, 0]]
  ![-128, -48, -5] ![![14, 0, 0], ![-4, 1, 0]] where
    su := ![![3206, 0, 0], ![-406, 14, 0]]
    hsu := by decide
    w := ![![-1792, -672, -70], ![-798, -266, -28]]
    hw := by decide
    g := ![![![304953, 16161174, -4059352], ![1067243, 56830927, 0]], ![![-39946, -2117178, 531791], ![-139799, -7445074, 0]]]
    h := ![![![-1446, 78, -1], ![-11414, 224, 0]], ![![-648, 51, -1], ![-5115, 227, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R229N1 : Ideal.span {14} * I229N1 =  Ideal.span {B.equivFun.symm ![-128, -48, -5]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E229RS1 
