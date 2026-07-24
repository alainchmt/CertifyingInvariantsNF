import IdealArithmetic.Examples.NF3_1_551980_3.PrimesBelow3_1_551980_3F2
import IdealArithmetic.Examples.NF3_1_551980_3.ClassGroupData3_1_551980_3

set_option linter.all false

noncomputable section


noncomputable def E127RS1 : RelationCertificate Table 9 ![![127, 0, 0], ![-27, 1, 0]]
  ![346834055468, -49811192084, -16734613295] ![![9, 0, 0], ![-2, 1, 0]] where
    su := ![![1143, 0, 0], ![-243, 9, 0]]
    hsu := by decide
    w := ![![3121506499212, -448300728756, -150611519655], ![1900196949789, 95029560441, -33076578789]]
    hw := by decide
    g := ![![![-934272472769706454896, 264589012149227782560, -39973663766844112794], ![237014884187626743600, -3403673, 0]], ![![244808017714299317827, -69330429249630167617, 10474324859993185392], ![-62105162742025422578, 658112, 0]]]
    h := ![![![93020856365846, -3574918041800, 4661197041], ![437529700903962, -608706637502, 0]], ![![56595336528513, -2174770246025, 2889261023], ![266199874300990, -370611325342, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N1 : Ideal.span {9} * I127N1 =  Ideal.span {B.equivFun.symm ![346834055468, -49811192084, -16734613295]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E127RS1 
