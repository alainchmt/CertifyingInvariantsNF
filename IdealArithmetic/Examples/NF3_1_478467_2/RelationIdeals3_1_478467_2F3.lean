import IdealArithmetic.Examples.NF3_1_478467_2.PrimesBelow3_1_478467_2F3
import IdealArithmetic.Examples.NF3_1_478467_2.ClassGroupData3_1_478467_2

set_option linter.all false

noncomputable section


noncomputable def E151RS1 : RelationCertificate Table 10 ![![151, 0, 0], ![-35, 1, 0]]
  ![-885451, -226826, -14625] ![![10, 0, 0], ![-119, -11, 1]] where
    su := ![![1510, 0, 0], ![-350, 10, 0]]
    hsu := by decide
    w := ![![-8854510, -2268260, -146250], ![43440680, 11128200, 717510]]
    hw := by decide
    g := ![![![21, 834, -60], ![-301, 0, 0]], ![![104, -215, 16], ![126, 0, 0]]]
    h := ![![![-354983076, 10571594, -12408], ![-1531473115, 1858983, 0]], ![![1741565548, -51864783, 60874], ![7513487248, -9120223, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N1 : Ideal.span {10} * I151N1 =  Ideal.span {B.equivFun.symm ![-885451, -226826, -14625]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E151RS1 


noncomputable def E157RS1 : RelationCertificate Table 10 ![![157, 0, 0], ![-41, 1, 0]]
  ![-32209, -8251, -532] ![![10, 0, 0], ![-119, -11, 1]] where
    su := ![![1570, 0, 0], ![-410, 10, 0]]
    hsu := by decide
    w := ![![-322090, -82510, -5320], ![1580210, 404800, 26100]]
    hw := by decide
    g := ![![![-81, 371, -11], ![617, 0, 0]], ![![76, -109, 3], ![-182, 0, 0]]]
    h := ![![![-274146, 6941, -11], ![-1048993, 1195, 0]], ![![1345332, -34022, 53], ![5147783, -5711, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R157N1 : Ideal.span {10} * I157N1 =  Ideal.span {B.equivFun.symm ![-32209, -8251, -532]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E157RS1 


noncomputable def E163RS1 : RelationCertificate Table 2 ![![163, 0, 0], ![-80, 1, 0]]
  ![8752433, 2242111, 144564] ![![2, 0, 0], ![-119, -7, 1]] where
    su := ![![326, 0, 0], ![-160, 2, 0]]
    hsu := by decide
    w := ![![17504866, 4484222, 289128], ![113583530, 29096696, 1876060]]
    hw := by decide
    g := ![![![339, -3977, 417], ![-6005, 0, 0]], ![![-81, 2172, -226], ![3199, 0, 0]]]
    h := ![![![1473429451, -21230730, 36228], ![3002003101, -5760600, 0]], ![![9560616695, -137759957, 235078], ![19479046619, -37379684, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R163N1 : Ideal.span {2} * I163N1 =  Ideal.span {B.equivFun.symm ![8752433, 2242111, 144564]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E163RS1 


noncomputable def E167RS1 : RelationCertificate Table 5 ![![167, 0, 0], ![-33, 1, 0]]
  ![-18437, -52, 80] ![![5, 0, 0], ![-119, -6, 1]] where
    su := ![![835, 0, 0], ![-165, 5, 0]]
    hsu := by decide
    w := ![![-92185, -260, 400], ![1694455, 96170, -13245]]
    hw := by decide
    g := ![![![-32912, 809690, 98547], ![-167071, 0, 0]], ![![3543, -84797, -10322], ![17502, 0, 0]]]
    h := ![![![-352996, 11039, -10], ![-1785815, 1750, 0]], ![![6487906, -202593, 171], ![32822467, -31206, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R167N1 : Ideal.span {5} * I167N1 =  Ideal.span {B.equivFun.symm ![-18437, -52, 80]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E167RS1 


noncomputable def E179RS1 : RelationCertificate Table 2 ![![179, 0, 0], ![66, 1, 0]]
  ![-70, -11, 1] ![![2, 0, 0], ![-119, -7, 1]] where
    su := ![![358, 0, 0], ![132, 2, 0]]
    hsu := by decide
    w := ![![-140, -22, 2], ![-8572, -502, 68]]
    hw := by decide
    g := ![![![92, -60, -9], ![7, 0, 0]], ![![30, -28, -4], ![3, 0, 0]]]
    h := ![![![-566, -75, -1], ![1534, 180, 0]], ![![-28078, -505, -1], ![76086, 213, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R179N1 : Ideal.span {2} * I179N1 =  Ideal.span {B.equivFun.symm ![-70, -11, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E179RS1 


noncomputable def E181RS1 : RelationCertificate Table 5 ![![181, 0, 0], ![40, 1, 0]]
  ![11587874, 2968466, 191397] ![![5, 0, 0], ![-119, -6, 1]] where
    su := ![![905, 0, 0], ![200, 5, 0]]
    hsu := by decide
    w := ![![57939370, 14842330, 956985], ![330101870, 84562205, 5452295]]
    hw := by decide
    g := ![![![716, 2767, 236], ![-17622, 0, 0]], ![![148, 522, 41], ![-3178, 0, 0]]]
    h := ![![![176327514, 4678570, 7447], ![-797592304, -1156510, 0]], ![![1004602814, 26655645, 42431], ![-4544177224, -6589552, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R181N1 : Ideal.span {5} * I181N1 =  Ideal.span {B.equivFun.symm ![11587874, 2968466, 191397]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E181RS1 


noncomputable def E191RS1 : RelationCertificate Table 2 ![![191, 0, 0], ![-69, 1, 0]]
  ![334, 25, -3] ![![2, 0, 0], ![-119, -7, 1]] where
    su := ![![382, 0, 0], ![-138, 2, 0]]
    hsu := by decide
    w := ![![668, 50, -6], ![3448, 150, -24]]
    hw := by decide
    g := ![![![2, 40, 5], ![-3, 0, 0]], ![![71, -7, -2], ![2, 0, 0]]]
    h := ![![![6698, -98, 0], ![18536, -3, 0]], ![![34168, -499, 0], ![94556, -12, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R191N1 : Ideal.span {2} * I191N1 =  Ideal.span {B.equivFun.symm ![334, 25, -3]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E191RS1 


noncomputable def E193RS1 : RelationCertificate Table 5 ![![193, 0, 0], ![-41, 1, 0]]
  ![29, 4, 0] ![![5, 0, 0], ![-119, -6, 1]] where
    su := ![![965, 0, 0], ![-205, 5, 0]]
    hsu := by decide
    w := ![![145, 20, 0], ![305, 70, 5]]
    hw := by decide
    g := ![![![92, 2, -1], ![21, 0, 0]], ![![7, 1, 0], ![-4, 0, 0]]]
    h := ![![![6438, -157, 0], ![30305, 0, 0]], ![![13460, -328, 0], ![63359, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R193N1 : Ideal.span {5} * I193N1 =  Ideal.span {B.equivFun.symm ![29, 4, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E193RS1 
