import IdealArithmetic.Examples.NF3_1_410700_2.PrimesBelow3_1_410700_2F3
import IdealArithmetic.Examples.NF3_1_410700_2.ClassGroupData3_1_410700_2

set_option linter.all false

noncomputable section


noncomputable def E149RS1 : RelationCertificate Table 1458 ![![149, 0, 0], ![-57, 1, 0]]
  ![-54, -8, 3] ![![1458, 0, 0], ![-15795, -891, 567]] where
    su := ![![217242, 0, 0], ![-83106, 1458, 0]]
    hsu := by decide
    w := ![![-78732, -11664, 4374], ![-710046, 0, 13122]]
    hw := by decide
    g := ![![![49217160016, 9267667993, 67923004321], ![-512434972841, -71649416342, -78]], ![![-17048589838, -3210276078, -23528205454], ![177505035906, 24819016838, 27]]]
    h := ![![![-780, 70, -3], ![-2038, 150, 0]], ![![-7007, 180, -3], ![-18308, 152, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R149N1 : Ideal.span {1458} * I149N1 =  Ideal.span {B.equivFun.symm ![-54, -8, 3]} * (J0 ^ 8*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8J1_2 E149RS1 


noncomputable def E167RS1 : RelationCertificate Table 3 ![![167, 0, 0], ![-27, 1, 0]]
  ![-40, -1, 1] ![![3, 0, 0], ![-28, -2, 1]] where
    su := ![![501, 0, 0], ![-81, 3, 0]]
    hsu := by decide
    w := ![![-120, -3, 3], ![450, 54, -21]]
    hw := by decide
    g := ![![![-1126, 1417, -484], ![9469, 1336, 0]], ![![195, -237, 81], ![-1587, -224, 0]]]
    h := ![![![-2816, 113, -1], ![-17416, 56, 0]], ![![10668, -404, 1], ![65978, -58, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R167N1 : Ideal.span {3} * I167N1 =  Ideal.span {B.equivFun.symm ![-40, -1, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E167RS1 


noncomputable def E173RS1 : RelationCertificate Table 1458 ![![173, 0, 0], ![28, 1, 0]]
  ![18, -16, -3] ![![1458, 0, 0], ![7101, 765, -261]] where
    su := ![![252234, 0, 0], ![40824, 1458, 0]]
    hsu := by decide
    w := ![![26244, -23328, -4374], ![453438, 17496, -30618]]
    hw := by decide
    g := ![![![19282736, -20830660, -3690961], ![83648587, 11857300, -333]], ![![3126875, -3378149, -598558], ![13565405, 1922908, -54]]]
    h := ![![![194, 7, 0], ![-1198, -1, 0]], ![![3355, 121, 0], ![-20718, -7, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R173N1 : Ideal.span {1458} * I173N1 =  Ideal.span {B.equivFun.symm ![18, -16, -3]} * (J0 ^ 4*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_2 E173RS1 


noncomputable def E179RS1 : RelationCertificate Table 162 ![![179, 0, 0], ![-38, 1, 0]]
  ![-13, -1, 1] ![![162, 0, 0], ![-756, -54, 27]] where
    su := ![![28998, 0, 0], ![-6156, 162, 0]]
    hsu := by decide
    w := ![![-2106, -162, 162], ![-8262, 0, 162]]
    hw := by decide
    g := ![![![6242356831392, -1872623338044, 591002269405], ![-28408290388864, -4143712795405, 0]], ![![-1360066172454, 408001612953, -128765819734], ![6189513963865, 902819840910, 0]]]
    h := ![![![-25825, 692, -1], ![-121649, 60, 0]], ![![-101483, 2683, -1], ![-478037, 60, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R179N1 : Ideal.span {162} * I179N1 =  Ideal.span {B.equivFun.symm ![-13, -1, 1]} * (J0 ^ 7*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7J1_1 E179RS1 
