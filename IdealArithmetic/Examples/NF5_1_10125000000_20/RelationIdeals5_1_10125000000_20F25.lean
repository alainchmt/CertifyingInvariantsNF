import IdealArithmetic.Examples.NF5_1_10125000000_20.PrimesBelow5_1_10125000000_20F25
import IdealArithmetic.Examples.NF5_1_10125000000_20.ClassGroupData5_1_10125000000_20

set_option linter.all false

noncomputable section


noncomputable def E1453RS1 : RelationCertificate Table 2 ![![1453, 0, 0, 0, 0], ![542, 1, 0, 0, 0]]
  ![8, 7, 5, 3, 19] ![![2, 0, 0, 0, 0], ![40, 27, 18, 11, 70]] where
    su := ![![2906, 0, 0, 0, 0], ![1084, 2, 0, 0, 0]]
    hsu := by decide
    w := ![![16, 14, 10, 6, 38], ![102, 108, 78, 46, 294]]
    hw := by decide
    g := ![![![-566, 137, 69, 24, 177], ![93, 0, 0, 0, 0]], ![![-201, 56, 29, 11, 79], ![34, 0, 0, 0, 0]]]
    h := ![![![698289396464, 4961722399, -15602209365875, -28802530883, -37450497], ![-1871953383692, -9877440464, 41826575995722, 27454880, 0]], ![![4587317754701, 32595367134, -102496604254884, -189214331139, -246025975], ![-12297544594644, -64888516956, 274774034025414, 180361121, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1453N1 : Ideal.span {2} * I1453N1 =  Ideal.span {B.equivFun.symm ![8, 7, 5, 3, 19]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E1453RS1 
