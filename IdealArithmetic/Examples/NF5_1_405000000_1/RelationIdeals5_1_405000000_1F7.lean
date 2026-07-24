import IdealArithmetic.Examples.NF5_1_405000000_1.PrimesBelow5_1_405000000_1F7
import IdealArithmetic.Examples.NF5_1_405000000_1.ClassGroupData5_1_405000000_1

set_option linter.all false

noncomputable section


noncomputable def E347RS1 : RelationCertificate Table 2 ![![347, 0, 0, 0, 0], ![56, 1, 0, 0, 0]]
  ![26059, 10207, -953, -274, -3045] ![![2, 0, 0, 0, 0], ![-27, 2, 0, 1, 1]] where
    su := ![![694, 0, 0, 0, 0], ![112, 2, 0, 0, 0]]
    hsu := by decide
    w := ![![52118, 20414, -1906, -548, -6090], ![-43128, 31712, -5396, 4416, -5622]]
    hw := by decide
    g := ![![![3075159881, 29738985863, 14561579399, 6219928514, 6834084356], ![-5248665827, 0, 0, 0, 0]], ![![526556387, 5092175230, 2493363905, 1065031809, 1170193067], ![-898723522, 0, 0, 0, 0]]]
    h := ![![![-25643111351, -15933877884, -912937431081, -32655963302, -3609095], ![158895708301, -5128505766, 5657043162320, 313088230, 0]], ![![-16544528148, -10280172306, -589006097992, -21068857124, -2327473], ![102516986532, -3308792642, 3649793299878, 201907580, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R347N1 : Ideal.span {2} * I347N1 =  Ideal.span {B.equivFun.symm ![26059, 10207, -953, -274, -3045]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E347RS1 
