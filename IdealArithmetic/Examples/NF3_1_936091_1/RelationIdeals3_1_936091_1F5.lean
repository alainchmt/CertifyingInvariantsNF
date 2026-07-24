import IdealArithmetic.Examples.NF3_1_936091_1.PrimesBelow3_1_936091_1F5
import IdealArithmetic.Examples.NF3_1_936091_1.ClassGroupData3_1_936091_1

set_option linter.all false

noncomputable section


noncomputable def E263RS1 : RelationCertificate Table 2 ![![263, 0, 0], ![-80, 1, 0]]
  ![153, -37, 5] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![526, 0, 0], ![-160, 2, 0]]
    hsu := by decide
    w := ![![306, -74, 10], ![-970, 238, -32]]
    hw := by decide
    g := ![![![145, 10, 393], ![6, -789, 0]], ![![-43, -3, -121], ![-1, 243, 0]]]
    h := ![![![24591, -306, 0], ![80841, 5, 0]], ![![-77795, 1128, -2], ![-255745, 510, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R263N1 : Ideal.span {2} * I263N1 =  Ideal.span {B.equivFun.symm ![153, -37, 5]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E263RS1 


noncomputable def E269RS1 : RelationCertificate Table 9 ![![269, 0, 0], ![43, 1, 0]]
  ![-19285, 1758, 746] ![![9, 0, 0], ![2, 1, 0]] where
    su := ![![2421, 0, 0], ![387, 9, 0]]
    hsu := by decide
    w := ![![-173565, 15822, 6714], ![-183294, -3087, 3996]]
    hw := by decide
    g := ![![![-3349513, 922082, -115718], ![-641876, 5032, 0]], ![![-455765, 125434, -15762], ![-87339, 832, 0]]]
    h := ![![![-5297039, -127469, -97], ![33136842, 26839, 0]], ![![-5594924, -134657, -104], ![35000330, 28420, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R269N1 : Ideal.span {9} * I269N1 =  Ideal.span {B.equivFun.symm ![-19285, 1758, 746]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E269RS1 


noncomputable def E271RS1 : RelationCertificate Table 3 ![![271, 0, 0], ![44, 1, 0]]
  ![-5671, -1008, -19] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![813, 0, 0], ![132, 3, 0]]
    hsu := by decide
    w := ![![-17013, -3024, -57], ![9357, -4986, -1008]]
    hw := by decide
    g := ![![![-2753278, 406220, -102370], ![1053167, 0, 0]], ![![-382030, 56367, -14207], ![146134, 8, 0]]]
    h := ![![![-525793, -12346, -9], ![3238278, 2420, 0]], ![![288809, 6744, 3], ![-1778730, -1149, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R271N1 : Ideal.span {3} * I271N1 =  Ideal.span {B.equivFun.symm ![-5671, -1008, -19]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E271RS1 
