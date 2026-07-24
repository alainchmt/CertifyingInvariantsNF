import IdealArithmetic.Examples.NF3_1_565068_1.PrimesBelow3_1_565068_1F4
import IdealArithmetic.Examples.NF3_1_565068_1.ClassGroupData3_1_565068_1

set_option linter.all false

noncomputable section


noncomputable def E197RS1 : RelationCertificate Table 363 ![![197, 0, 0], ![7, 1, 0]]
  ![-840, -593, -74] ![![363, 0, 0], ![112, 1, 0]] where
    su := ![![71511, 0, 0], ![2541, 363, 0]]
    hsu := by decide
    w := ![![-304920, -215259, -26862], ![-90750, -65703, -11253]]
    hw := by decide
    g := ![![![293, 58060, 2583], ![376, -186528, 0]], ![![-104, 4352, 193], ![374, -13984, 0]]]
    h := ![![![70, -424811, -265512], ![-2090, 10461158, 0]], ![![16, -126419, -79013], ![-486, 3113106, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R197N1 : Ideal.span {363} * I197N1 =  Ideal.span {B.equivFun.symm ![-840, -593, -74]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E197RS1 


noncomputable def E199RS0 : RelationCertificate Table 11 ![![199, 0, 0], ![72, 1, 0]]
  ![10, 3, -2] ![![11, 0, 0], ![2, 1, 0]] where
    su := ![![2189, 0, 0], ![792, 11, 0]]
    hsu := by decide
    w := ![![110, 33, -22], ![110, 77, 11]]
    hw := by decide
    g := ![![![55, -579, -968], ![-36, 2133, 0]], ![![19, -212, -354], ![-10, 780, 0]]]
    h := ![![![118, -42, -3], ![-326, 119, 0]], ![![118, -13, -1], ![-326, 40, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R199N0 : Ideal.span {11} * I199N0 =  Ideal.span {B.equivFun.symm ![10, 3, -2]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E199RS0 


noncomputable def E199RS1 : RelationCertificate Table 11 ![![199, 0, 0], ![-47, 1, 0]]
  ![46, 49, 37] ![![11, 0, 0], ![2, 1, 0]] where
    su := ![![2189, 0, 0], ![-517, 11, 0]]
    hsu := by decide
    w := ![![506, 539, 407], ![-1573, -880, 319]]
    hw := by decide
    g := ![![![208166, -12293378, -20651959], ![-1079725, 45435186, 0]], ![![-48871, 2879532, 4837392], ![252899, -10642476, 0]]]
    h := ![![![910, 1, -2], ![3852, 87, 0]], ![![-2551, 92, -4], ![-10798, 165, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R199N1 : Ideal.span {11} * I199N1 =  Ideal.span {B.equivFun.symm ![46, 49, 37]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E199RS1 


noncomputable def E199RS2 : RelationCertificate Table 11 ![![199, 0, 0], ![-26, 1, 0]]
  ![-131, -58, 57] ![![11, 0, 0], ![2, 1, 0]] where
    su := ![![2189, 0, 0], ![-286, 11, 0]]
    hsu := by decide
    w := ![![-1441, -638, 627], ![-2827, -1958, -176]]
    hw := by decide
    g := ![![![458, 1783929, 2999314], ![162260, -6596276, 0]], ![![-886, -195299, -328421], ![-17908, 722220, 0]]]
    h := ![![![-387, 26, -2], ![-2957, 91, 0]], ![![-789, 49, -4], ![-6029, 156, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R199N2 : Ideal.span {11} * I199N2 =  Ideal.span {B.equivFun.symm ![-131, -58, 57]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E199RS2 
