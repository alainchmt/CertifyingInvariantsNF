import IdealArithmetic.Examples.NF3_1_933907_1.PrimesBelow3_1_933907_1F5
import IdealArithmetic.Examples.NF3_1_933907_1.ClassGroupData3_1_933907_1

set_option linter.all false

noncomputable section


noncomputable def E263RS0 : RelationCertificate Table 243 ![![263, 0, 0], ![11, 1, 0]]
  ![-86, 22, -3] ![![243, 0, 0], ![-89, 37, 1]] where
    su := ![![63909, 0, 0], ![2673, 243, 0]]
    hsu := by decide
    w := ![![-20898, 5346, -729], ![73629, -13608, 1458]]
    hw := by decide
    g := ![![![-63, 1, 1], ![34, 0, 0]], ![![2, -3, 0], ![23, 0, 0]]]
    h := ![![![-90, -14, -1], ![2144, 130, 0]], ![![291, 26, 0], ![-6930, 3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R263N0 : Ideal.span {243} * I263N0 =  Ideal.span {B.equivFun.symm ![-86, 22, -3]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E263RS0 


noncomputable def E263RS1 : RelationCertificate Table 9 ![![263, 0, 0], ![117, 1, 0]]
  ![-311734, 62676, -7199] ![![9, 0, 0], ![-80, 1, 1]] where
    su := ![![2367, 0, 0], ![1053, 9, 0]]
    hsu := by decide
    w := ![![-2805606, 564084, -64791], ![-19604961, 3941694, -452745]]
    hw := by decide
    g := ![![![-93, 1118, 64], ![1331, 0, 0]], ![![-1, 543, 30], ![665, 0, 0]]]
    h := ![![![7070026, 58810, -59], ![-15895116, 4159, 0]], ![![49404044, 411147, -409], ![-111072153, 28631, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R263N1 : Ideal.span {9} * I263N1 =  Ideal.span {B.equivFun.symm ![-311734, 62676, -7199]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E263RS1 


noncomputable def E263RS2 : RelationCertificate Table 243 ![![263, 0, 0], ![-129, 1, 0]]
  ![-8166447, 1641913, -188591] ![![243, 0, 0], ![-89, 37, 1]] where
    su := ![![63909, 0, 0], ![-31347, 243, 0]]
    hsu := by decide
    w := ![![-1984446621, 398984859, -45827613], ![4679024292, -940745826, 108054567]]
    hw := by decide
    g := ![![![16375, -659, -262], ![-6001, 0, 0]], ![![-7250, 277, 117], ![2834, 0, 0]]]
    h := ![![![-296339456295, 2676912461, -5933551], ![-604164874722, 780167661, 0]], ![![698723513362, -6311753592, 13990411], ![1424529184178, -1839516712, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R263N2 : Ideal.span {243} * I263N2 =  Ideal.span {B.equivFun.symm ![-8166447, 1641913, -188591]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E263RS2 


noncomputable def E271RS1 : RelationCertificate Table 243 ![![271, 0, 0], ![-90, 1, 0]]
  ![286633, -16460, -3576] ![![243, 0, 0], ![-89, 37, 1]] where
    su := ![![65853, 0, 0], ![-21870, 243, 0]]
    hsu := by decide
    w := ![![69651819, -3999780, -868968], ![85315599, -4596831, -1031535]]
    hw := by decide
    g := ![![![1843741, -313866, 51666], ![-722782, 0, 0]], ![![-730699, 124370, -20479], ![286693, 0, 0]]]
    h := ![![![22303, 19282835, -433342], ![63972, 58716053, 0]], ![![27273, 23591910, -530179], ![78221, 71837132, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R271N1 : Ideal.span {243} * I271N1 =  Ideal.span {B.equivFun.symm ![286633, -16460, -3576]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E271RS1 
