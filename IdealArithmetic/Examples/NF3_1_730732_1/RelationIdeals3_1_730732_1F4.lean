import IdealArithmetic.Examples.NF3_1_730732_1.PrimesBelow3_1_730732_1F4
import IdealArithmetic.Examples.NF3_1_730732_1.ClassGroupData3_1_730732_1

set_option linter.all false

noncomputable section


noncomputable def E199RS1 : RelationCertificate Table 3 ![![199, 0, 0], ![61, 1, 0]]
  ![18, 17, 9] ![![3, 0, 0], ![24, -2, 1]] where
    su := ![![597, 0, 0], ![183, 3, 0]]
    hsu := by decide
    w := ![![54, 51, 27], ![-135, -231, -159]]
    hw := by decide
    g := ![![![-929, -1758, 775], ![-5810, 0, 0]], ![![-279, -515, 227], ![-1703, 0, 0]]]
    h := ![![![-18, -337, -11], ![41, 1099, 0]], ![![-1, 831, 27], ![47, -2713, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R199N1 : Ideal.span {3} * I199N1 =  Ideal.span {B.equivFun.symm ![18, 17, 9]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E199RS1 


noncomputable def E233RS1 : RelationCertificate Table 3 ![![233, 0, 0], ![-34, 1, 0]]
  ![-3517900, 1218241, 2253007] ![![3, 0, 0], ![24, -2, 1]] where
    su := ![![699, 0, 0], ![-102, 3, 0]]
    hsu := by decide
    w := ![![-10553700, 3654723, 6759021], ![101674359, -5330085, -38714721]]
    hw := by decide
    g := ![![![-51029683680263, -99167941312260, 43724780387769], ![-327550581771220, 0, 0]], ![![8025011576536, 15595312760331, -6876230528744], ![51511140595985, 0, 0]]]
    h := ![![![1740422897, -61747502441, 3632347025], ![-518977912, -423167301909, 0]], ![![-16740650743, 593932357161, -34938513579], ![4991907792, 4070330379500, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R233N1 : Ideal.span {3} * I233N1 =  Ideal.span {B.equivFun.symm ![-3517900, 1218241, 2253007]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E233RS1 
