import IdealArithmetic.Examples.NF3_1_732108_1.PrimesBelow3_1_732108_1F4
import IdealArithmetic.Examples.NF3_1_732108_1.ClassGroupData3_1_732108_1

set_option linter.all false

noncomputable section


noncomputable def E197RS1 : RelationCertificate Table 75 ![![197, 0, 0], ![58, 1, 0]]
  ![-536, 469, 80] ![![75, 0, 0], ![27, 1, 0]] where
    su := ![![14775, 0, 0], ![4350, 75, 0]]
    hsu := by decide
    w := ![![-40200, 35175, 6000], ![-12450, 10425, 4425]]
    hw := by decide
    g := ![![![-38295537835820253081, 586508810461021472523, 101108493122824234907], ![-5966276148081671471, -1516627396842363144814, -73481]], ![![-11080434908885472701, 169700520349461701592, 29254741938499062574], ![-1726282962539280773, -438821129077485829046, -21261]]]
    h := ![![![1377680, -42987054, -3582175], ![187447, 141137711, 0]], ![![425768, -13285113, -1107068], ![57940, 43618491, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R197N1 : Ideal.span {75} * I197N1 =  Ideal.span {B.equivFun.symm ![-536, 469, 80]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E197RS1 


noncomputable def E211RS0 : RelationCertificate Table 3 ![![211, 0, 0], ![63, 1, 0]]
  ![70, 1, 2] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![633, 0, 0], ![189, 3, 0]]
    hsu := by decide
    w := ![![210, 3, 6], ![72, 6, 3]]
    hw := by decide
    g := ![![![-377, 342, 954], ![115, -573, 0]], ![![-114, 103, 288], ![36, -173, 0]]]
    h := ![![![-23270, 787256, 60557], ![-3190, -2555505, 0]], ![![-7978, 269638, 20741], ![-1066, -875270, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R211N0 : Ideal.span {3} * I211N0 =  Ideal.span {B.equivFun.symm ![70, 1, 2]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E211RS0 


noncomputable def E211RS1 : RelationCertificate Table 3 ![![211, 0, 0], ![-57, 1, 0]]
  ![-8, 7, 2] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![633, 0, 0], ![-171, 3, 0]]
    hsu := by decide
    w := ![![-24, 21, 6], ![60, -60, 33]]
    hw := by decide
    g := ![![![354299, -317711, -882531], ![-105902, 529542, 0]], ![![-92706, 83128, 230913], ![27711, -138554, 0]]]
    h := ![![![295, 7898, -718], ![29, 30300, 0]], ![![-693, -19811, 1801], ![101, -76000, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R211N1 : Ideal.span {3} * I211N1 =  Ideal.span {B.equivFun.symm ![-8, 7, 2]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E211RS1 


noncomputable def E211RS2 : RelationCertificate Table 3 ![![211, 0, 0], ![-7, 1, 0]]
  ![-33733, -436, -1034] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![633, 0, 0], ![-21, 3, 0]]
    hsu := by decide
    w := ![![-101199, -1308, -3102], ![-37386, -483, -1146]]
    hw := by decide
    g := ![![![179, -158, -501], ![-52, 285, 0]], ![![-9, 7, 13], ![4, -7, 0]]]
    h := ![![![5844506, 14622577, -14621994], ![-124483, 617047940, 0]], ![![2159142, 5402027, -5401812], ![-45908, 227956390, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R211N2 : Ideal.span {3} * I211N2 =  Ideal.span {B.equivFun.symm ![-33733, -436, -1034]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E211RS2 


noncomputable def E227RS1 : RelationCertificate Table 15 ![![227, 0, 0], ![-24, 1, 0]]
  ![4731, 61, 145] ![![15, 0, 0], ![20, 1, 1]] where
    su := ![![3405, 0, 0], ![-360, 15, 0]]
    hsu := by decide
    w := ![![70965, 915, 2175], ![100815, 1305, 3090]]
    hw := by decide
    g := ![![![5558920, -9885457, -6896228], ![6293139, 0, -7473097]], ![![-569838, 1013315, 706902], ![-645070, 0, 766035]]]
    h := ![![![-14360265, -158918490, 36117020], ![818353, -1639712679, 0]], ![![-20400619, -225764246, 51308893], ![1162507, -2329423701, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R227N1 : Ideal.span {15} * I227N1 =  Ideal.span {B.equivFun.symm ![4731, 61, 145]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E227RS1 


noncomputable def E233RS1 : RelationCertificate Table 5 ![![233, 0, 0], ![20, 1, 0]]
  ![-1571172, -20307, -48160] ![![5, 0, 0], ![2, 1, 0]] where
    su := ![![1165, 0, 0], ![100, 5, 0]]
    hsu := by decide
    w := ![![-7855860, -101535, -240800], ![-4883650, -63120, -149695]]
    hw := by decide
    g := ![![![-41463446, 41584429, -1209906], ![-8268489, 0, 6050097]], ![![-3671435, 3682146, -107132], ![-732142, 0, 535716]]]
    h := ![![![17864652, -197237010, -44826110], ![686955, 2088887094, 0]], ![![11105682, -122613759, -27866463], ![427087, 1298571188, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R233N1 : Ideal.span {5} * I233N1 =  Ideal.span {B.equivFun.symm ![-1571172, -20307, -48160]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E233RS1 
