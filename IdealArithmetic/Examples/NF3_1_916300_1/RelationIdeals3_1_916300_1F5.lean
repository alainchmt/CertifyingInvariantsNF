import IdealArithmetic.Examples.NF3_1_916300_1.PrimesBelow3_1_916300_1F5
import IdealArithmetic.Examples.NF3_1_916300_1.ClassGroupData3_1_916300_1

set_option linter.all false

noncomputable section


noncomputable def E263RS1 : RelationCertificate Table 11 ![![263, 0, 0], ![-87, 1, 0]]
  ![8254, 300, 157] ![![11, 0, 0], ![-2, 1, 0]] where
    su := ![![2893, 0, 0], ![-957, 11, 0]]
    hsu := by decide
    w := ![![90794, 3300, 1727], ![7513, 275, 143]]
    hw := by decide
    g := ![![![-114488, -7157433, 3607342], ![-629857, -39680787, 0]], ![![36999, 2313108, -1165805], ![203559, 12823863, 0]]]
    h := ![![![462008, -5692, 5], ![1396550, -1158, 0]], ![![38317, -436, 0], ![115824, 13, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R263N1 : Ideal.span {11} * I263N1 =  Ideal.span {B.equivFun.symm ![8254, 300, 157]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E263RS1 


noncomputable def E269RS1 : RelationCertificate Table 3 ![![269, 0, 0], ![5, 1, 0]]
  ![-209, -8, -4] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![807, 0, 0], ![15, 3, 0]]
    hsu := by decide
    w := ![![-627, -24, -12], ![-612, -21, -12]]
    hw := by decide
    g := ![![![-13, 7, -34688], ![3, 104060, 0]], ![![-1, 0, -2420], ![1, 7260, 0]]]
    h := ![![![-211, -47, -1], ![11310, 265, 0]], ![![-206, -46, -1], ![11042, 265, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R269N1 : Ideal.span {3} * I269N1 =  Ideal.span {B.equivFun.symm ![-209, -8, -4]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E269RS1 
