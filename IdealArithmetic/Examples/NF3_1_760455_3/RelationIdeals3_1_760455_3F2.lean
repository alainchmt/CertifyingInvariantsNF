import IdealArithmetic.Examples.NF3_1_760455_3.PrimesBelow3_1_760455_3F2
import IdealArithmetic.Examples.NF3_1_760455_3.ClassGroupData3_1_760455_3

set_option linter.all false

noncomputable section


noncomputable def E83RS1 : RelationCertificate Table 25 ![![83, 0, 0], ![36, 1, 0]]
  ![-56, 48, -29] ![![25, 0, 0], ![8, 1, 0]] where
    su := ![![2075, 0, 0], ![900, 25, 0]]
    hsu := by decide
    w := ![![-1400, 1200, -725], ![-1425, 1150, 75]]
    hw := by decide
    g := ![![![22405, 83559, 84037], ![10521, -299921, 0]], ![![9618, 35742, 35948], ![4509, -128291, 0]]]
    h := ![![![296, 7284, 1457], ![276, -17280, 0]], ![![301, 7402, 1481], ![280, -17560, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {25} * I83N1 =  Ideal.span {B.equivFun.symm ![-56, 48, -29]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E83RS1 


noncomputable def E97RS1 : RelationCertificate Table 5 ![![97, 0, 0], ![8, 1, 0]]
  ![4, -2, 1] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![485, 0, 0], ![40, 5, 0]]
    hsu := by decide
    w := ![![20, -10, 5], ![25, -20, -15]]
    hw := by decide
    g := ![![![251, -356, 912], ![-169, -650, 0]], ![![24, -34, 87], ![-16, -62, 0]]]
    h := ![![![3212, 11349, 11353], ![385, -157320, 0]], ![![4029, 14236, 14241], ![484, -197340, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {5} * I97N1 =  Ideal.span {B.equivFun.symm ![4, -2, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E97RS1 


noncomputable def E97RS2 : RelationCertificate Table 25 ![![97, 0, 0], ![-10, 1, 0]]
  ![-2434, -3, -81] ![![25, 0, 0], ![8, 1, 0]] where
    su := ![![2425, 0, 0], ![-250, 25, 0]]
    hsu := by decide
    w := ![![-60850, -75, -2025], ![-22475, -25, -750]]
    hw := by decide
    g := ![![![-3332757, -13395085, -13459177], ![-1602261, 48068488, 0]], ![![340417, 1368224, 1374771], ![163671, -4909896, 0]]]
    h := ![![![64398, -360085, 229212], ![-10343, -3176235, 0]], ![![23793, -132999, 84660], ![-3748, -1173150, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N2 : Ideal.span {25} * I97N2 =  Ideal.span {B.equivFun.symm ![-2434, -3, -81]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E97RS2 


noncomputable def E101RS1 : RelationCertificate Table 5 ![![101, 0, 0], ![45, 1, 0]]
  ![813, 1, 27] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![505, 0, 0], ![225, 5, 0]]
    hsu := by decide
    w := ![![4065, 5, 135], ![-625, 0, -20]]
    hw := by decide
    g := ![![![-1482, 2679, -6788], ![1132, 4848, 0]], ![![-652, 1180, -2991], ![502, 2136, 0]]]
    h := ![![![3823, 111523, 17747], ![2818, -256060, 0]], ![![-625, -17150, -2729], ![-350, 39375, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {5} * I101N1 =  Ideal.span {B.equivFun.symm ![813, 1, 27]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E101RS1 


noncomputable def E109RS0 : RelationCertificate Table 5 ![![109, 0, 0], ![5, 1, 0]]
  ![3958, -3499, 3302] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![545, 0, 0], ![25, 5, 0]]
    hsu := by decide
    w := ![![19790, -17495, 16510], ![107260, -84605, -27795]]
    hw := by decide
    g := ![![![392685185, 30690570, 15057797], ![-150935959, 5014, 0]], ![![22453336, 1754809, 861100], ![-8630371, 207, 0]]]
    h := ![![![-49678, -99719, -174472], ![-3128, 2717250, 0]], ![![-268117, -538198, -941901], ![-17139, 14665950, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N0 : Ideal.span {5} * I109N0 =  Ideal.span {B.equivFun.symm ![3958, -3499, 3302]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E109RS0 


noncomputable def E109RS1 : RelationCertificate Table 25 ![![109, 0, 0], ![12, 1, 0]]
  ![-803, -1, -27] ![![25, 0, 0], ![8, 1, 0]] where
    su := ![![2725, 0, 0], ![300, 25, 0]]
    hsu := by decide
    w := ![![-20075, -25, -675], ![-7425, 0, -250]]
    hw := by decide
    g := ![![![-494, -1984, -1994], ![-237, 7120, 0]], ![![-60, -232, -233], ![-21, 832, 0]]]
    h := ![![![-3923143, -21954862, -13974973], ![-633233, 217610290, 0]], ![![-1451049, -8120393, -5168890], ![-234163, 80487000, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {25} * I109N1 =  Ideal.span {B.equivFun.symm ![-803, -1, -27]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E109RS1 


noncomputable def E113RS1 : RelationCertificate Table 25 ![![113, 0, 0], ![-12, 1, 0]]
  ![-21, 18, -14] ![![25, 0, 0], ![8, 1, 0]] where
    su := ![![2825, 0, 0], ![-300, 25, 0]]
    hsu := by decide
    w := ![![-525, 450, -350], ![-650, 525, 0]]
    hw := by decide
    g := ![![![-559, -926, -945], ![-191, 3333, 0]], ![![36, 33, 35], ![23, -121, 0]]]
    h := ![![![49059, -324357, 174692], ![-8031, -2820030, 0]], ![![60678, -401170, 216062], ![-9923, -3487858, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {25} * I113N1 =  Ideal.span {B.equivFun.symm ![-21, 18, -14]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E113RS1 


noncomputable def E127RS0 : RelationCertificate Table 5 ![![127, 0, 0], ![19, 1, 0]]
  ![5024472704, 5549123, 167069476] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![635, 0, 0], ![95, 5, 0]]
    hsu := by decide
    w := ![![25122363520, 27745615, 835347380], ![-3856276550, -4258945, -128225615]]
    hw := by decide
    g := ![![![-96147, 165311, -396711], ![71526, 285570, 0]], ![![-16016, 28403, -70133], ![12092, 50768, 0]]]
    h := ![![![376926927328, 3504406379253, 1363083171618], ![83984393732, -24730199389430, 0]], ![![-57858189580, -537925507337, -209232927715], ![-12891583458, 3796079453526, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N0 : Ideal.span {5} * I127N0 =  Ideal.span {B.equivFun.symm ![5024472704, 5549123, 167069476]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E127RS0 


noncomputable def E127RS2 : RelationCertificate Table 25 ![![127, 0, 0], ![-4, 1, 0]]
  ![17942849069, 19816423, 596620296] ![![25, 0, 0], ![8, 1, 0]] where
    su := ![![3175, 0, 0], ![-100, 25, 0]]
    hsu := by decide
    w := ![![448571226725, 495410575, 14915507400], ![165657376350, 182955150, 5508297625]]
    hw := by decide
    g := ![![![5158102, 20750219, 20844673], ![2480611, -74449998, 0]], ![![-38709, -154679, -155346], ![-18568, 555597, 0]]]
    h := ![![![750543786547, -1878729654967, 2630650096584], ![-38432321248, -47727423663696, 0]], ![![277175857718, -693814955063, 971499211567], ![-14193058153, -17625739933872, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N2 : Ideal.span {25} * I127N2 =  Ideal.span {B.equivFun.symm ![17942849069, 19816423, 596620296]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E127RS2 
