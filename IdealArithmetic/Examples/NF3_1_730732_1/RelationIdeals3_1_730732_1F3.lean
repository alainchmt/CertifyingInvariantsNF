import IdealArithmetic.Examples.NF3_1_730732_1.PrimesBelow3_1_730732_1F3
import IdealArithmetic.Examples.NF3_1_730732_1.ClassGroupData3_1_730732_1

set_option linter.all false

noncomputable section


noncomputable def E139RS1 : RelationCertificate Table 3 ![![139, 0, 0], ![-56, 1, 0]]
  ![246, -11, 6] ![![3, 0, 0], ![24, -2, 1]] where
    su := ![![417, 0, 0], ![-168, 3, 0]]
    hsu := by decide
    w := ![![738, -33, 18], ![7938, -354, 195]]
    hw := by decide
    g := ![![![-10, 13, -3], ![5, 0, 0]], ![![-3, -4, 1], ![-1, 0, 0]]]
    h := ![![![-2180, 172745, -6170], ![2242, 428818, 0]], ![![-23854, 1858066, -66365], ![23108, 4612400, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N1 : Ideal.span {3} * I139N1 =  Ideal.span {B.equivFun.symm ![246, -11, 6]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E139RS1 


noncomputable def E173RS1 : RelationCertificate Table 3 ![![173, 0, 0], ![56, 1, 0]]
  ![338078, -15085, 8284] ![![3, 0, 0], ![24, -2, 1]] where
    su := ![![519, 0, 0], ![168, 3, 0]]
    hsu := by decide
    w := ![![1014234, -45255, 24852], ![10911096, -486852, 267357]]
    hw := by decide
    g := ![![![-54, -453, -44], ![-94, 0, 0]], ![![-17, -132, -21], ![-25, 0, 0]]]
    h := ![![![25016302, 1728617926, 61740140], ![18089925, -5340517968, 0]], ![![269125000, 18596414788, 664198395], ![194609440, -57453116608, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R173N1 : Ideal.span {3} * I173N1 =  Ideal.span {B.equivFun.symm ![338078, -15085, 8284]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E173RS1 
