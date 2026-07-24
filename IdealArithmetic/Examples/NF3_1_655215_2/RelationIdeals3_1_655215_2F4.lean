import IdealArithmetic.Examples.NF3_1_655215_2.PrimesBelow3_1_655215_2F4
import IdealArithmetic.Examples.NF3_1_655215_2.ClassGroupData3_1_655215_2

set_option linter.all false

noncomputable section


noncomputable def E211RS0 : RelationCertificate Table 2 ![![211, 0, 0], ![91, 1, 0]]
  ![-364816142, 111687183, 4557430] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![422, 0, 0], ![182, 2, 0]]
    hsu := by decide
    w := ![![-729632284, 223374366, 9114860], ![182075458, -300951826, 227931796]]
    hw := by decide
    g := ![![![212512549542283916, -34104210445292027, 6707156772858592], ![89204169548495947, 0, 151740]], ![![94805121715819580, -15214413592318902, 2992165947785308], ![39795354061750339, 0, 65754]]]
    h := ![![![-54945767336, -705796229, -2207638], ![127397715294, 235184524, 0]], ![![13704209910, 175558202, 1098392], ![-31774695091, -58897407, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R211N0 : Ideal.span {2} * I211N0 =  Ideal.span {B.equivFun.symm ![-364816142, 111687183, 4557430]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E211RS0 


noncomputable def E211RS1 : RelationCertificate Table 4 ![![211, 0, 0], ![-48, 1, 0]]
  ![18823, -11487, 5139] ![![4, 0, 0], ![24, 1, 1]] where
    su := ![![844, 0, 0], ![-192, 4, 0]]
    hsu := by decide
    w := ![![75292, -45948, 20556], ![-618348, 262168, -60680]]
    hw := by decide
    g := ![![![304316062, 3449599, -159112949], ![1786980665, 0, 0]], ![![-64713546, -733566, 33835745], ![-380005670, 0, 0]]]
    h := ![![![109021, -2386, 27], ![478846, -279, 0]], ![![-894585, 19687, -104], ![-3929226, 3387, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R211N1 : Ideal.span {4} * I211N1 =  Ideal.span {B.equivFun.symm ![18823, -11487, 5139]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E211RS1 


noncomputable def E211RS2 : RelationCertificate Table 2 ![![211, 0, 0], ![-44, 1, 0]]
  ![-193, -8, -5] ![![2, 0, 0], ![24, 2, 1]] where
    su := ![![422, 0, 0], ![-88, 2, 0]]
    hsu := by decide
    w := ![![-386, -16, -10], ![-6492, -264, -170]]
    hw := by decide
    g := ![![![-25, 12, 1], ![-1, 0, 0]], ![![-4, 25, 1], ![-14, 3, 0]]]
    h := ![![![-1675, 59, -1], ![-8028, 103, 0]], ![![-28826, 710, -3], ![-138160, 274, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R211N2 : Ideal.span {2} * I211N2 =  Ideal.span {B.equivFun.symm ![-193, -8, -5]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E211RS2 


noncomputable def E223RS1 : RelationCertificate Table 2 ![![223, 0, 0], ![57, 1, 0]]
  ![44698, 1825, 1166] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![446, 0, 0], ![114, 2, 0]]
    hsu := by decide
    w := ![![89396, 3650, 2332], ![184618, 7538, 4816]]
    hw := by decide
    g := ![![![17256857, -8016954, 163026], ![4619953, 0, -326106]], ![![4432075, -2058992, 41869], ![1186543, 0, -83754]]]
    h := ![![![915874, 17197, 44], ![-3582372, -4323, 0]], ![![1891403, 35547, 92], ![-7398080, -9054, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R223N1 : Ideal.span {2} * I223N1 =  Ideal.span {B.equivFun.symm ![44698, 1825, 1166]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E223RS1 
