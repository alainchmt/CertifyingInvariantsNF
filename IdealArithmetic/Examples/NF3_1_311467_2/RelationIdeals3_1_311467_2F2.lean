import IdealArithmetic.Examples.NF3_1_311467_2.PrimesBelow3_1_311467_2F2
import IdealArithmetic.Examples.NF3_1_311467_2.ClassGroupData3_1_311467_2

set_option linter.all false

noncomputable section


noncomputable def E89RS1 : RelationCertificate Table 2 ![![89, 0, 0], ![-44, 1, 0]]
  ![-369056837557, 143106451315, -16666130627] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![178, 0, 0], ![-88, 2, 0]]
    hsu := by decide
    w := ![![-738113675114, 286212902630, -33332261254], ![2799909945336, -1085700454518, 126440320688]]
    hw := by decide
    g := ![![![-11029745, 381678, 239429], ![190839, 30175, 0]], ![![4972472, -189464, -110153], ![-94731, -14910, 0]]]
    h := ![![![-32799063909701, 889958815545, -3437529225], ![-66335173434678, 289273970398, 0]], ![![124417726340588, -3375908918327, 13039688314], ![251631311121356, -1097312099602, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {2} * I89N1 =  Ideal.span {B.equivFun.symm ![-369056837557, 143106451315, -16666130627]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E89RS1 


noncomputable def E97RS0 : RelationCertificate Table 4 ![![97, 0, 0], ![20, 1, 0]]
  ![-829541, 321665, -37461] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![388, 0, 0], ![80, 4, 0]]
    hsu := by decide
    w := ![![-3318164, 1286660, -149844], ![6293448, -2440364, 284204]]
    hw := by decide
    g := ![![![8665, -646, 2861], ![-161, -12408, 0]], ![![2204, -150, 1104], ![-36, -4653, 0]]]
    h := ![![![-5007813, -258643, -986], ![24246416, 58181, 0]], ![![9498106, 490535, 1869], ![-45987146, -110242, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N0 : Ideal.span {4} * I97N0 =  Ideal.span {B.equivFun.symm ![-829541, 321665, -37461]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E97RS0 


noncomputable def E97RS1 : RelationCertificate Table 4 ![![97, 0, 0], ![38, 1, 0]]
  ![-83, 27, 5] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![388, 0, 0], ![152, 4, 0]]
    hsu := by decide
    w := ![![-332, 108, 20], ![-840, 132, 32]]
    hw := by decide
    g := ![![![-281, 102, -95787], ![29, 383097, 0]], ![![-88, 32, -38779], ![9, 155100, 0]]]
    h := ![![![-697, -58, -1], ![1777, 102, 0]], ![![-1606, -83, -1], ![4094, 105, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {4} * I97N1 =  Ideal.span {B.equivFun.symm ![-83, 27, 5]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E97RS1 


noncomputable def E113RS1 : RelationCertificate Table 4 ![![113, 0, 0], ![30, 1, 0]]
  ![-300023, 17847, 7565] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![452, 0, 0], ![120, 4, 0]]
    hsu := by decide
    w := ![![-1200092, 71388, 30260], ![-1270920, 25272, 25412]]
    hw := by decide
    g := ![![![363087881, -132510036, 16395309], ![-33127508, 5085, 0]], ![![72017796, -26283116, 3251897], ![-6570777, 1335, 0]]]
    h := ![![![-3064861, -110494, -219], ![11534309, 32312, 0]], ![![-3246450, -117162, -247], ![12217704, 34264, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {4} * I113N1 =  Ideal.span {B.equivFun.symm ![-300023, 17847, 7565]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E113RS1 


noncomputable def E137RS1 : RelationCertificate Table 4 ![![137, 0, 0], ![21, 1, 0]]
  ![-331, 55, 13] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![548, 0, 0], ![84, 4, 0]]
    hsu := by decide
    w := ![![-1324, 220, 52], ![-2184, 228, 68]]
    hw := by decide
    g := ![![![-1073, 391, -132604], ![101, 530222, 0]], ![![-105, 38, -21367], ![11, 85449, 0]]]
    h := ![![![-19814, -987, -2], ![129247, 287, 0]], ![![-32634, -1619, -3], ![212872, 428, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {4} * I137N1 =  Ideal.span {B.equivFun.symm ![-331, 55, 13]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E137RS1 
