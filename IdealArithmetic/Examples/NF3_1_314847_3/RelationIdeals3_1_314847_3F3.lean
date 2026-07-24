import IdealArithmetic.Examples.NF3_1_314847_3.PrimesBelow3_1_314847_3F3
import IdealArithmetic.Examples.NF3_1_314847_3.ClassGroupData3_1_314847_3

set_option linter.all false

noncomputable section


noncomputable def E149RS1 : RelationCertificate Table 4 ![![149, 0, 0], ![27, 1, 0]]
  ![2443, -71, -76] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![596, 0, 0], ![108, 4, 0]]
    hsu := by decide
    w := ![![9772, -284, -304], ![-3692, 1688, -512]]
    hw := by decide
    g := ![![![11341699, -244392, 389187], ![5609755, 0, -505196]], ![![2145498, -45661, 73997], ![1061336, 0, -95320]]]
    h := ![![![254460, 3471160, 534096], ![69559, -19895095, 0]], ![![-96473, -1315520, -202416], ![-26162, 7539964, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R149N1 : Ideal.span {4} * I149N1 =  Ideal.span {B.equivFun.symm ![2443, -71, -76]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E149RS1 


noncomputable def E157RS1 : RelationCertificate Table 5 ![![157, 0, 0], ![49, 1, 0]]
  ![-22108149, -3706300, -1785834] ![![5, 0, 0], ![-1, 1, 0]] where
    su := ![![785, 0, 0], ![245, 5, 0]]
    hsu := by decide
    w := ![![-110540745, -18531500, -8929170], ![-183532025, -30768055, -14825200]]
    hw := by decide
    g := ![![![2173, 2686, -1538], ![106, 566, 0]], ![![-32, 750, -424], ![161, 177, 0]]]
    h := ![![![-1824296221, -50445641286, -4204285606], ![-890676094, 165017763577, 0]], ![![-3028899237, -83755457751, -6980422024], ![-1478799440, 273980823182, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R157N1 : Ideal.span {5} * I157N1 =  Ideal.span {B.equivFun.symm ![-22108149, -3706300, -1785834]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E157RS1 
