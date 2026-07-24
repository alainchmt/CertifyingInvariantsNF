import IdealArithmetic.Examples.NF3_1_356631_2.PrimesBelow3_1_356631_2F3
import IdealArithmetic.Examples.NF3_1_356631_2.ClassGroupData3_1_356631_2

set_option linter.all false

noncomputable section


noncomputable def E139RS1 : RelationCertificate Table 3 ![![139, 0, 0], ![-62, 1, 0]]
  ![15, 2, 0] ![![3, 0, 0], ![-25, -2, 1]] where
    su := ![![417, 0, 0], ![-186, 3, 0]]
    hsu := by decide
    w := ![![45, 6, 0], ![3, -6, 3]]
    hw := by decide
    g := ![![![925, -2435, 370], ![-5798, 0, 391]], ![![-377, 1080, -165], ![2569, 0, -173]]]
    h := ![![![3225, -52, 0], ![7230, 0, 0]], ![![215, 38, -2], ![482, 93, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N1 : Ideal.span {3} * I139N1 =  Ideal.span {B.equivFun.symm ![15, 2, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E139RS1 


noncomputable def E149RS1 : RelationCertificate Table 3 ![![149, 0, 0], ![71, 1, 0]]
  ![321, -9, -4] ![![3, 0, 0], ![-25, -3, 1]] where
    su := ![![447, 0, 0], ![213, 3, 0]]
    hsu := by decide
    w := ![![963, -27, -12], ![-7458, -879, 354]]
    hw := by decide
    g := ![![![3, 734, 500], ![-565, 0, 0]], ![![7, 412, 280], ![-316, 0, 0]]]
    h := ![![![2754, -8, -2], ![-5775, 98, 0]], ![![-22284, -429, -4], ![46730, 238, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R149N1 : Ideal.span {3} * I149N1 =  Ideal.span {B.equivFun.symm ![321, -9, -4]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E149RS1 


noncomputable def E151RS0 : RelationCertificate Table 3 ![![151, 0, 0], ![-62, 1, 0]]
  ![1011, -10, -17] ![![3, 0, 0], ![-25, -3, 1]] where
    su := ![![453, 0, 0], ![-186, 3, 0]]
    hsu := by decide
    w := ![![3033, -30, -51], ![-17526, -2337, 897]]
    hw := by decide
    g := ![![![23, 5334, 3633], ![-4105, 0, 0]], ![![21, -1745, -1192], ![1349, 0, 0]]]
    h := ![![![207827, -3685, 16], ![506143, -811, 0]], ![![-1199774, 21577, -106], ![-2921936, 5435, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N0 : Ideal.span {3} * I151N0 =  Ideal.span {B.equivFun.symm ![1011, -10, -17]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E151RS0 


noncomputable def E151RS2 : RelationCertificate Table 3 ![![151, 0, 0], ![-30, 1, 0]]
  ![-663, -22, 18] ![![3, 0, 0], ![-25, -2, 1]] where
    su := ![![453, 0, 0], ![-90, 3, 0]]
    hsu := by decide
    w := ![![-1989, -66, 54], ![5613, 864, -315]]
    hw := by decide
    g := ![![![-1189455, 3196502, -486528], ![7619006, 0, -513324]], ![![236022, -634263, 96512], ![-1511682, 0, 101850]]]
    h := ![![![-59733, 2082, -9], ![-300634, 459, 0]], ![![168641, -5806, 18], ![848764, -941, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N2 : Ideal.span {3} * I151N2 =  Ideal.span {B.equivFun.symm ![-663, -22, 18]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E151RS2 
