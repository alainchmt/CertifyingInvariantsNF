import IdealArithmetic.Examples.NF3_1_767839_1.PrimesBelow3_1_767839_1F4
import IdealArithmetic.Examples.NF3_1_767839_1.ClassGroupData3_1_767839_1

set_option linter.all false

noncomputable section


noncomputable def E197RS1 : RelationCertificate Table 243 ![![197, 0, 0], ![-61, 1, 0]]
  ![-8422496, -685987, -193069] ![![243, 0, 0], ![-88, 1, 0]] where
    su := ![![47871, 0, 0], ![-14823, 243, 0]]
    hsu := by decide
    w := ![![-2046666528, -166694841, -46915767], ![711253953, 57929499, 16304085]]
    hw := by decide
    g := ![![![133, -12205, 137], ![110, -33643, 0]], ![![-5, 2765, -31], ![69, 7616, 0]]]
    h := ![![![-158246068, 2747453, -3561], ![-510918900, 508448, 0]], ![![54993409, -954759, 1237], ![177553682, -176594, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R197N1 : Ideal.span {243} * I197N1 =  Ideal.span {B.equivFun.symm ![-8422496, -685987, -193069]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E197RS1 


noncomputable def E223RS1 : RelationCertificate Table 81 ![![223, 0, 0], ![111, 1, 0]]
  ![127, -160, 35] ![![81, 0, 0], ![-7, 1, 0]] where
    su := ![![18063, 0, 0], ![8991, 81, 0]]
    hsu := by decide
    w := ![![10287, -12960, 2835], ![4536, 162, -405]]
    hw := by decide
    g := ![![![429, 31240, -4450], ![415, 361180, 0]], ![![222, 15621, -2225], ![232, 180600, 0]]]
    h := ![![![233782, 4086, 18], ![-469669, -3979, 0]], ![![105284, 1839, 8], ![-211516, -1789, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R223N1 : Ideal.span {81} * I223N1 =  Ideal.span {B.equivFun.symm ![127, -160, 35]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E223RS1 


noncomputable def E229RS1 : RelationCertificate Table 3 ![![229, 0, 0], ![-103, 1, 0]]
  ![1931, -110, -122] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![687, 0, 0], ![-309, 3, 0]]
    hsu := by decide
    w := ![![5793, -330, -366], ![-20841, 5823, 12]]
    hw := by decide
    g := ![![![-3146410, -530741, -118614], ![871893, 119480, 0]], ![![1366329, 229975, 52068], ![-378784, -53560, 0]]]
    h := ![![![617354, -6873, 8], ![1372545, -1954, 0]], ![![-2222124, 25086, -34], ![-4940383, 7790, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R229N1 : Ideal.span {3} * I229N1 =  Ideal.span {B.equivFun.symm ![1931, -110, -122]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E229RS1 


noncomputable def E241RS1 : RelationCertificate Table 3 ![![241, 0, 0], ![-63, 1, 0]]
  ![-119, 101, -19] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![723, 0, 0], ![-189, 3, 0]]
    hsu := by decide
    w := ![![-357, 303, -57], ![-2826, 369, 120]]
    hw := by decide
    g := ![![![-85001, -15443, -1965], ![23189, -482, 0]], ![![20968, 3811, 482], ![-5717, 127, 0]]]
    h := ![![![-3563, 115, -1], ![-13628, 222, 0]], ![![-28356, 524, -1], ![-108458, 281, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R241N1 : Ideal.span {3} * I241N1 =  Ideal.span {B.equivFun.symm ![-119, 101, -19]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E241RS1 
