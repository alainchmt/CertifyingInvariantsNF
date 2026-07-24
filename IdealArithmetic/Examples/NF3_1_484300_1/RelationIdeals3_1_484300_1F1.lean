import IdealArithmetic.Examples.NF3_1_484300_1.PrimesBelow3_1_484300_1F1
import IdealArithmetic.Examples.NF3_1_484300_1.ClassGroupData3_1_484300_1

set_option linter.all false

noncomputable section


noncomputable def E53RS1 : RelationCertificate Table 3 ![![53, 0, 0], ![1, 1, 0]]
  ![-55, -2, 6] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![159, 0, 0], ![3, 3, 0]]
    hsu := by decide
    w := ![![-165, -6, 18], ![-789, -153, 6]]
    hw := by decide
    g := ![![![-4249, 352, -66], ![-1298, 0, -52]], ![![134, -32, 8], ![37, 0, -1]]]
    h := ![![![-4, -3, -6], ![49, 108, 0]], ![![-6, -2, -2], ![19, 36, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {3} * I53N1 =  Ideal.span {B.equivFun.symm ![-55, -2, 6]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E53RS1 


noncomputable def E59RS1 : RelationCertificate Table 3 ![![59, 0, 0], ![7, 1, 0]]
  ![-29, 8, 9] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![177, 0, 0], ![21, 3, 0]]
    hsu := by decide
    w := ![![-87, 24, 27], ![-1119, -165, 42]]
    hw := by decide
    g := ![![![-207981, -7542, 4089], ![-71840, 0, -5830]], ![![-38503, -1251, 714], ![-13250, 0, -1060]]]
    h := ![![![45, 356, 153], ![46, -3006, 0]], ![![613, 4471, 1918], ![168, -37716, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {3} * I59N1 =  Ideal.span {B.equivFun.symm ![-29, 8, 9]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E59RS1 


noncomputable def E61RS1 : RelationCertificate Table 9 ![![61, 0, 0], ![-30, 1, 0]]
  ![8080, 1001, -426] ![![9, 0, 0], ![4, 1, 0]] where
    su := ![![549, 0, 0], ![-270, 9, 0]]
    hsu := by decide
    w := ![![72720, 9009, -3834], ![85293, 18900, 873]]
    hw := by decide
    g := ![![![-45155620918, -262737873473, -201158327937], ![-49262261904, 603475309090, 3172]], ![![22577641687, 131368959812, 100579155816], ![24631058510, -301737653722, -1586]]]
    h := ![![![-3059, 156509, -15663], ![4122, 318339, 0]], ![![-3417, 174026, -17405], ![4534, 353934, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {9} * I61N1 =  Ideal.span {B.equivFun.symm ![8080, 1001, -426]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E61RS1 


noncomputable def E67RS1 : RelationCertificate Table 3 ![![67, 0, 0], ![-4, 1, 0]]
  ![-4, 1, 0] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![201, 0, 0], ![-12, 3, 0]]
    hsu := by decide
    w := ![![-12, 3, 0], ![-3, -3, 3]]
    hw := by decide
    g := ![![![1453, 46, -27], ![501, 0, 40]], ![![0, -1, 0], ![3, 0, 0]]]
    h := ![![![510, -2040, 1530], ![1, -34170, 0]], ![![127, -498, 373], ![45, -8330, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {3} * I67N1 =  Ideal.span {B.equivFun.symm ![-4, 1, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E67RS1 


noncomputable def E71RS1 : RelationCertificate Table 9 ![![71, 0, 0], ![-27, 1, 0]]
  ![-7688852, 589157, -301548] ![![9, 0, 0], ![4, 1, 0]] where
    su := ![![639, 0, 0], ![-243, 9, 0]]
    hsu := by decide
    w := ![![-69199668, 5302413, -2713932], ![6622605, -507456, 259731]]
    hw := by decide
    g := ![![![-4376015253388, -25460452149752, -19493158671815], ![-4773834795915, 58479476021788, -3692]], ![![1694935485261, 9861442733352, 7550167090665], ![1849020519379, -22650501274412, 1430]]]
    h := ![![![1031925112, -37271144625, 4142670597], ![-917367883, -98043304645, 0]], ![![-98758147, 3566954522, -396465356], ![87794769, 9383023045, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {9} * I71N1 =  Ideal.span {B.equivFun.symm ![-7688852, 589157, -301548]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E71RS1 
