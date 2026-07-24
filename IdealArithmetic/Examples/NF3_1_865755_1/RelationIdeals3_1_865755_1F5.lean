import IdealArithmetic.Examples.NF3_1_865755_1.PrimesBelow3_1_865755_1F5
import IdealArithmetic.Examples.NF3_1_865755_1.ClassGroupData3_1_865755_1

set_option linter.all false

noncomputable section


noncomputable def E263RS1 : RelationCertificate Table 32 ![![263, 0, 0], ![-103, 1, 0]]
  ![29565, 6160, 1733] ![![32, 0, 0], ![-15, 1, 0]] where
    su := ![![8416, 0, 0], ![-3296, 32, 0]]
    hsu := by decide
    w := ![![946080, 197120, 55456], ![52352, 10912, 3072]]
    hw := by decide
    g := ![![![3120, -32569, 11666], ![-2455, -74581, 0]], ![![-1191, 12654, -4533], ![968, 28977, 0]]]
    h := ![![![181382835, -11545740280, 565989091], ![-114935880, -29771025840, 0]], ![![10037007, -638891202, 31319382], ![-6359881, -1647399474, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R263N1 : Ideal.span {32} * I263N1 =  Ideal.span {B.equivFun.symm ![29565, 6160, 1733]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E263RS1 
