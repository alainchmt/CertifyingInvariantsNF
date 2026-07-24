import IdealArithmetic.Examples.NF3_1_662796_4.PrimesBelow3_1_662796_4F4
import IdealArithmetic.Examples.NF3_1_662796_4.ClassGroupData3_1_662796_4

set_option linter.all false

noncomputable section


noncomputable def E197RS1 : RelationCertificate Table 169 ![![197, 0, 0], ![92, 1, 0]]
  ![-415, -78, 9] ![![169, 0, 0], ![-26, -6, 1]] where
    su := ![![33293, 0, 0], ![15548, 169, 0]]
    hsu := by decide
    w := ![![-70135, -13182, 1521], ![-54418, -6084, 845]]
    hw := by decide
    g := ![![![2884243543, 510051206, -33160714], ![-462034169, -1011032480, 0]], ![![1351989170, 239086505, -15544085], ![-216578461, -473921475, 0]]]
    h := ![![![-2799, -127, -1], ![5989, 206, 0]], ![![-2162, -118, -1], ![4626, 202, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R197N1 : Ideal.span {169} * I197N1 =  Ideal.span {B.equivFun.symm ![-415, -78, 9]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E197RS1 


noncomputable def E197RS2 : RelationCertificate Table 169 ![![197, 0, 0], ![96, 1, 0]]
  ![2093, 129, -24] ![![169, 0, 0], ![-52, -6, 1]] where
    su := ![![33293, 0, 0], ![16224, 169, 0]]
    hsu := by decide
    w := ![![353717, 21801, -4056], ![26026, 0, -169]]
    hw := by decide
    g := ![![![-518251669, -65547697, 5941777], ![161824532, 194330792, 0]], ![![-266628346, -33722755, 3056905], ![83254994, 99978648, 0]]]
    h := ![![![33577, 362, 0], ![-68881, -24, 0]], ![![2450, 26, 0], ![-5026, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R197N2 : Ideal.span {169} * I197N2 =  Ideal.span {B.equivFun.symm ![2093, 129, -24]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E197RS2 


noncomputable def E199RS1 : RelationCertificate Table 13 ![![199, 0, 0], ![70, 1, 0]]
  ![-163, -13, 2] ![![13, 0, 0], ![0, 1, 0]] where
    su := ![![2587, 0, 0], ![910, 13, 0]]
    hsu := by decide
    w := ![![-2119, -169, 26], ![988, 65, -13]]
    hw := by decide
    g := ![![![13, 0, -695], ![11, 9032, 0]], ![![4, 0, -245], ![3, 3184, 0]]]
    h := ![![![-79047, -1410, -4], ![224717, 798, 0]], ![![36724, 595, 1], ![-104400, -200, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R199N1 : Ideal.span {13} * I199N1 =  Ideal.span {B.equivFun.symm ![-163, -13, 2]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E199RS1 


noncomputable def E211RS1 : RelationCertificate Table 169 ![![211, 0, 0], ![47, 1, 0]]
  ![-2275, -694, -55] ![![169, 0, 0], ![-71, 1, 0]] where
    su := ![![35659, 0, 0], ![7943, 169, 0]]
    hsu := by decide
    w := ![![-384475, -117286, -9295], ![134355, 40729, 3211]]
    hw := by decide
    g := ![![![-72933235, -34516954402, 486168755], ![-173601706, -82162519664, 0]], ![![-16898627, -7997583905, 112645379], ![-40223504, -19037069064, 0]]]
    h := ![![![-4568, -135, -1], ![20459, 156, 0]], ![![1512, 29, 0], ![-6771, 19, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R211N1 : Ideal.span {169} * I211N1 =  Ideal.span {B.equivFun.symm ![-2275, -694, -55]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E211RS1 
