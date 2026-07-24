import IdealArithmetic.Examples.NF3_3_260820_1.PrimesBelow3_3_260820_1F2
import IdealArithmetic.Examples.NF3_3_260820_1.ClassGroupData3_3_260820_1

set_option linter.all false

noncomputable section


noncomputable def E83RS1 : RelationCertificate Table 25 ![![83, 0, 0], ![-15, 1, 0]]
  ![-477, -114, 23] ![![25, 0, 0], ![-7, 1, 0]] where
    su := ![![2075, 0, 0], ![-375, 25, 0]]
    hsu := by decide
    w := ![![-11925, -2850, 575], ![5225, 1425, -275]]
    hw := by decide
    g := ![![![31758, 3059508, -437726], ![113511, 10943093, 0]], ![![-2252, -217501, 31118], ![-8051, -777945, 0]]]
    h := ![![![-185979, 12776, -25], ![-1029052, 2098, 0]], ![![81493, -5584, 10], ![450914, -841, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {25} * I83N1 =  Ideal.span {B.equivFun.symm ![-477, -114, 23]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E83RS1 


noncomputable def E97RS1 : RelationCertificate Table 25 ![![97, 0, 0], ![33, 1, 0]]
  ![-847, -104, 28] ![![25, 0, 0], ![-7, 1, 0]] where
    su := ![![2425, 0, 0], ![825, 25, 0]]
    hsu := by decide
    w := ![![-21175, -2600, 700], ![8225, 1225, -300]]
    hw := by decide
    g := ![![![-17, 2638, -388], ![130, 9576, 0]], ![![-5, 919, -136], ![62, 3348, 0]]]
    h := ![![![-470437, -16411, -65], ![1382774, 6333, 0]], ![![182705, 6366, 25], ![-537032, -2437, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {25} * I97N1 =  Ideal.span {B.equivFun.symm ![-847, -104, 28]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E97RS1 


noncomputable def E101RS1 : RelationCertificate Table 25 ![![101, 0, 0], ![18, 1, 0]]
  ![151, 32, 1] ![![25, 0, 0], ![-7, 1, 0]] where
    su := ![![2525, 0, 0], ![450, 25, 0]]
    hsu := by decide
    w := ![![3775, 800, 25], ![-975, -25, 25]]
    hw := by decide
    g := ![![![8, -1029, 147], ![-41, -3708, 0]], ![![1, -203, 29], ![-5, -729, 0]]]
    h := ![![![50453, 2911, 6], ![-283089, -605, 0]], ![![-13029, -760, -2], ![73105, 203, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {25} * I101N1 =  Ideal.span {B.equivFun.symm ![151, 32, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E101RS1 


noncomputable def E103RS1 : RelationCertificate Table 5 ![![103, 0, 0], ![-11, 1, 0]]
  ![73, 6, -2] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![515, 0, 0], ![-55, 5, 0]]
    hsu := by decide
    w := ![![365, 30, -10], ![-310, -35, 10]]
    hw := by decide
    g := ![![![-31017, -449862, 232690], ![-77564, -1163448, 0]], ![![3089, 44787, -23166], ![7724, 115830, 0]]]
    h := ![![![4036, -367, 0], ![37785, -2, 0]], ![![-3398, 320, -1], ![-31812, 105, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {5} * I103N1 =  Ideal.span {B.equivFun.symm ![73, 6, -2]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E103RS1 
