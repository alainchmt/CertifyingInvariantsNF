import IdealArithmetic.Examples.NF3_1_542700_3.PrimesBelow3_1_542700_3F3
import IdealArithmetic.Examples.NF3_1_542700_3.ClassGroupData3_1_542700_3

set_option linter.all false

noncomputable section


noncomputable def E139RS1 : RelationCertificate Table 12778713 ![![139, 0, 0], ![-51, 1, 0]]
  ![82777, 1942, 6030] ![![12778713, 0, 0], ![5757882, 3, 3]] where
    su := ![![1776241107, 0, 0], ![-651714363, 12778713, 0]]
    hsu := by decide
    w := ![![1057783526001, 24816260646, 77055639390], ![476620437474, 11181373875, 34719763221]]
    hw := by decide
    g := ![![![-21692853, -4841516880396, -12612950], ![-7841050, 10745152777186, 0]], ![![7146829, 1718727375660, 4477568], ![4013257, -3814504563349, 0]]]
    h := ![![![1373641, -29016, 250], ![3742222, -5744, 0]], ![![619004, -13079, 113], ![1686358, -2598, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N1 : Ideal.span {12778713} * I139N1 =  Ideal.span {B.equivFun.symm ![82777, 1942, 6030]} * (J0 ^ 5*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_0 E139RS1 


noncomputable def E179RS1 : RelationCertificate Table 751689 ![![179, 0, 0], ![2, 1, 0]]
  ![-5411, -2266, -1273] ![![751689, 0, 0], ![141690, 3, 0]] where
    su := ![![134552331, 0, 0], ![1503378, 751689, 0]]
    hsu := by decide
    w := ![![-4067389179, -1703327274, -956900097], ![-766722780, -320971203, -180405360]]
    hw := by decide
    g := ![![![-108688652960799, 149610839443177188831, 15838539005449762], ![576611368871833, -793710369764501743255, 0]], ![![-2042269458072, 2811200960675024129, 297607554596471], ![10834578916428, -14913888340471112635, 0]]]
    h := ![![![-8043813401, -4022414012, -1268292], ![719921296684, 45404599, 0]], ![![-1516298192, -758244727, -239080], ![135708687674, 8559016, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R179N1 : Ideal.span {751689} * I179N1 =  Ideal.span {B.equivFun.symm ![-5411, -2266, -1273]} * (J0 ^ 4*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_0 E179RS1 


noncomputable def E191RS1 : RelationCertificate Table 104907 ![![191, 0, 0], ![46, 1, 0]]
  ![-321347, -761, -10749] ![![104907, 0, 0], ![-15850, 1, 1]] where
    su := ![![20037237, 0, 0], ![4825722, 104907, 0]]
    hsu := by decide
    w := ![![-33711549729, -79834227, -1127645343], ![5093234850, 12064305, 170368968]]
    hw := by decide
    g := ![![![1790417, -2895628817, 911724], ![-218596, -19129202300, 0]], ![![448512, -718391370, 226194], ![-25651, -4745861680, 0]]]
    h := ![![![-3642857, -84153, -599], ![15118790, 20732, 0]], ![![550314, 12699, 89], ![-2283944, -3075, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R191N1 : Ideal.span {104907} * I191N1 =  Ideal.span {B.equivFun.symm ![-321347, -761, -10749]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E191RS1 
