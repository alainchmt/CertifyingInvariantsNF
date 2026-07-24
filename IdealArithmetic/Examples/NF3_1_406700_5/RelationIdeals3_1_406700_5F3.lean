import IdealArithmetic.Examples.NF3_1_406700_5.PrimesBelow3_1_406700_5F3
import IdealArithmetic.Examples.NF3_1_406700_5.ClassGroupData3_1_406700_5

set_option linter.all false

noncomputable section


noncomputable def E139RS1 : RelationCertificate Table 289 ![![139, 0, 0], ![-58, 1, 0]]
  ![66, -16, 1] ![![289, 0, 0], ![-83, 14, 1]] where
    su := ![![40171, 0, 0], ![-16762, 289, 0]]
    hsu := by decide
    w := ![![19074, -4624, 289], ![-5491, 2312, -289]]
    hw := by decide
    g := ![![![72, -870, 101], ![-61, -1941, 0]], ![![10, 351, -42], ![163, 798, 0]]]
    h := ![![![598, -10, 0], ![1432, 1, 0]], ![![-137, 60, -1], ![-328, 138, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N1 : Ideal.span {289} * I139N1 =  Ideal.span {B.equivFun.symm ![66, -16, 1]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E139RS1 


noncomputable def E149RS1 : RelationCertificate Table 289 ![![149, 0, 0], ![-66, 1, 0]]
  ![-114, 34, 3] ![![289, 0, 0], ![84, 1, 0]] where
    su := ![![43061, 0, 0], ![-19074, 289, 0]]
    hsu := by decide
    w := ![![-32946, 9826, 867], ![-9537, 2601, 289]]
    hw := by decide
    g := ![![![82, -137673, -1639], ![-287, 473664, 0]], ![![-95, 56698, 675], ![329, -195072, 0]]]
    h := ![![![-4914, 142, -1], ![-11092, 152, 0]], ![![-1353, 87, -1], ![-3054, 150, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R149N1 : Ideal.span {289} * I149N1 =  Ideal.span {B.equivFun.symm ![-114, 34, 3]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E149RS1 


noncomputable def E157RS1 : RelationCertificate Table 17 ![![157, 0, 0], ![14, 1, 0]]
  ![-1, 0, -4] ![![17, 0, 0], ![-1, 1, 0]] where
    su := ![![2669, 0, 0], ![238, 17, 0]]
    hsu := by decide
    w := ![![-17, 0, -68], ![-51, 187, 0]]
    hw := by decide
    g := ![![![-156, -10637, 10672], ![-607, -181468, 0]], ![![-56, -13298, 13343], ![-766, -226835, 0]]]
    h := ![![![-215, -29, -1], ![2411, 153, 0]], ![![-617, -58, -1], ![6919, 157, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R157N1 : Ideal.span {17} * I157N1 =  Ideal.span {B.equivFun.symm ![-1, 0, -4]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E157RS1 


noncomputable def E163RS1 : RelationCertificate Table 17 ![![163, 0, 0], ![-69, 1, 0]]
  ![-3, 9, 1] ![![17, 0, 0], ![36, -3, 1]] where
    su := ![![2771, 0, 0], ![-1173, 17, 0]]
    hsu := by decide
    w := ![![-51, 153, 17], ![-17, 17, -34]]
    hw := by decide
    g := ![![![-90, -19, 0], ![-140, 0, 0]], ![![2, 11, -1], ![76, 0, 0]]]
    h := ![![![33, 0, 0], ![78, 1, 0]], ![![11, 68, -1], ![26, 161, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R163N1 : Ideal.span {17} * I163N1 =  Ideal.span {B.equivFun.symm ![-3, 9, 1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E163RS1 


noncomputable def E167RS0 : RelationCertificate Table 289 ![![167, 0, 0], ![35, 1, 0]]
  ![-21, 36, 2] ![![289, 0, 0], ![-83, 14, 1]] where
    su := ![![48263, 0, 0], ![10115, 289, 0]]
    hsu := by decide
    w := ![![-6069, 10404, 578], ![2601, -6358, 289]]
    hw := by decide
    g := ![![![-4822647, 60319628, -6998718], ![4283048, 134556424, 0]], ![![-1499688, 18757927, -2176431], ![1332049, 41843766, 0]]]
    h := ![![![-157738, -4787, -8], ![752635, 1338, 0]], ![![67422, 2031, 3], ![-321699, -500, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R167N0 : Ideal.span {289} * I167N0 =  Ideal.span {B.equivFun.symm ![-21, 36, 2]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E167RS0 


noncomputable def E167RS1 : RelationCertificate Table 289 ![![167, 0, 0], ![37, 1, 0]]
  ![588, -5, 12] ![![289, 0, 0], ![-83, 14, 1]] where
    su := ![![48263, 0, 0], ![10693, 289, 0]]
    hsu := by decide
    w := ![![169932, -1445, 3468], ![-46529, 578, -867]]
    hw := by decide
    g := ![![![10, 553, -66], ![230, 1255, 0]], ![![-10, 129, -15], ![10, 288, 0]]]
    h := ![![![3774140, 109919, 214], ![-17034616, -35726, 0]], ![![-1033399, -30112, -59], ![4664256, 9850, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R167N1 : Ideal.span {289} * I167N1 =  Ideal.span {B.equivFun.symm ![588, -5, 12]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E167RS1 


noncomputable def E167RS2 : RelationCertificate Table 289 ![![167, 0, 0], ![-73, 1, 0]]
  ![211, 5, 5] ![![289, 0, 0], ![-83, 14, 1]] where
    su := ![![48263, 0, 0], ![-21097, 289, 0]]
    hsu := by decide
    w := ![![60979, 1445, 1445], ![-16473, -1156, -289]]
    hw := by decide
    g := ![![![-65, 1291, -151], ![224, 2895, 0]], ![![58, -547, 63], ![13, -1215, 0]]]
    h := ![![![4762464, -74946, 133], ![10894949, -22206, 0]], ![![-1286294, 20321, -37], ![-2942617, 6178, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R167N2 : Ideal.span {289} * I167N2 =  Ideal.span {B.equivFun.symm ![211, 5, 5]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E167RS2 


noncomputable def E179RS1 : RelationCertificate Table 17 ![![179, 0, 0], ![-42, 1, 0]]
  ![-929, 14, -20] ![![17, 0, 0], ![-2, 1, 0]] where
    su := ![![3043, 0, 0], ![-714, 17, 0]]
    hsu := by decide
    w := ![![-15793, 238, -340], ![1598, -17, 34]]
    hw := by decide
    g := ![![![-61849, -9060855, 4545890], ![-525711, -77280138, 0]], ![![14408, 2110560, -1058882], ![122467, 18000996, 0]]]
    h := ![![![-21913, 559, -1], ![-93369, 159, 0]], ![![2246, -53, 0], ![9570, 2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R179N1 : Ideal.span {17} * I179N1 =  Ideal.span {B.equivFun.symm ![-929, 14, -20]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E179RS1 
