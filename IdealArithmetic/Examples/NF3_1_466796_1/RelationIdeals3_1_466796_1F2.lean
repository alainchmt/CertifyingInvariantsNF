import IdealArithmetic.Examples.NF3_1_466796_1.PrimesBelow3_1_466796_1F2
import IdealArithmetic.Examples.NF3_1_466796_1.ClassGroupData3_1_466796_1

set_option linter.all false

noncomputable section


noncomputable def E83RS1 : RelationCertificate Table 121 ![![83, 0, 0], ![-28, 1, 0]]
  ![1024, -53, -10] ![![121, 0, 0], ![30, 1, 0]] where
    su := ![![10043, 0, 0], ![-3388, 121, 0]]
    hsu := by decide
    w := ![![123904, -6413, -1210], ![37510, -1936, -363]]
    hw := by decide
    g := ![![![-380941, 197324782, 6577916], ![1536455, -795927835, 0]], ![![70353, -36452365, -1215157], ![-283755, 147033997, 0]]]
    h := ![![![1664, -63, 0], ![4896, -10, 0]], ![![530, -20, 0], ![1560, -3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {121} * I83N1 =  Ideal.span {B.equivFun.symm ![1024, -53, -10]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E83RS1 


noncomputable def E89RS1 : RelationCertificate Table 539 ![![89, 0, 0], ![35, 1, 0]]
  ![4181, -108, -32] ![![539, 0, 0], ![63, 1, 0]] where
    su := ![![47971, 0, 0], ![18865, 539, 0]]
    hsu := by decide
    w := ![![2253559, -58212, -17248], ![285131, -7007, -2156]]
    hw := by decide
    g := ![![![-4021183704302, 18796799826663533, 298362915158354], ![34403460581263, -160817611270352790, 0]], ![![-1558773456561, 7286399924012969, 115657534388076], ![13336172906136, -62339411035172960, 0]]]
    h := ![![![36189, 1184, 4], ![-91904, -388, 0]], ![![4541, 131, 0], ![-11532, -4, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {539} * I89N1 =  Ideal.span {B.equivFun.symm ![4181, -108, -32]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E89RS1 


noncomputable def E89RS2 : RelationCertificate Table 847 ![![89, 0, 0], ![-43, 1, 0]]
  ![-365, -37, 9] ![![847, 0, 0], ![-91, 1, 0]] where
    su := ![![75383, 0, 0], ![-36421, 847, 0]]
    hsu := by decide
    w := ![![-309155, -31339, 7623], ![27104, 4235, -847]]
    hw := by decide
    g := ![![![-85, -968240, 10640], ![-797, -9012088, 0]], ![![123, 466192, -5123], ![1147, 4339184, 0]]]
    h := ![![![-7790, 228, -1], ![-16115, 98, 0]], ![![756, -18, 0], ![1564, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N2 : Ideal.span {847} * I89N2 =  Ideal.span {B.equivFun.symm ![-365, -37, 9]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E89RS2 


noncomputable def E97RS0 : RelationCertificate Table 49 ![![97, 0, 0], ![0, 1, 0]]
  ![-97, 30, -2] ![![49, 0, 0], ![14, 1, 0]] where
    su := ![![4753, 0, 0], ![0, 49, 0]]
    hsu := by decide
    w := ![![-4753, 1470, -98], ![0, 49, 0]]
    hw := by decide
    g := ![![![13, 1, 0], ![-19, -2, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![-1, 0, 0], ![30, -2, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N0 : Ideal.span {49} * I97N0 =  Ideal.span {B.equivFun.symm ![-97, 30, -2]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E97RS0 


noncomputable def E97RS1 : RelationCertificate Table 121 ![![97, 0, 0], ![44, 1, 0]]
  ![-1348, 109, 16] ![![121, 0, 0], ![30, 1, 0]] where
    su := ![![11737, 0, 0], ![5324, 121, 0]]
    hsu := by decide
    w := ![![-163108, 13189, 1936], ![-51304, 4114, 605]]
    hw := by decide
    g := ![![![7499271, -3884874315, -129504143], ![-30247050, 15670001304, 0]], ![![3453965, -1789281428, -59646552], ![-13930988, 7217232792, 0]]]
    h := ![![![-2383004, -81973, -632], ![5253410, 61320, 0]], ![![-749592, -25794, -199], ![1652500, 19308, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {121} * I97N1 =  Ideal.span {B.equivFun.symm ![-1348, 109, 16]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E97RS1 


noncomputable def E97RS2 : RelationCertificate Table 77 ![![97, 0, 0], ![-45, 1, 0]]
  ![379, -89, 5] ![![77, 0, 0], ![-14, 1, 0]] where
    su := ![![7469, 0, 0], ![-3465, 77, 0]]
    hsu := by decide
    w := ![![29183, -6853, 385], ![-8701, 2310, -154]]
    hw := by decide
    g := ![![![-32, -1897, 136], ![18, -10444, 0]], ![![16, 879, -63], ![12, 4840, 0]]]
    h := ![![![1599142, -40665, 114], ![3447031, -11053, 0]], ![![-476804, 12170, -35], ![-1027775, 3393, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N2 : Ideal.span {77} * I97N2 =  Ideal.span {B.equivFun.symm ![379, -89, 5]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E97RS2 


noncomputable def E101RS1 : RelationCertificate Table 49 ![![101, 0, 0], ![-36, 1, 0]]
  ![246, -19, -2] ![![49, 0, 0], ![14, 1, 0]] where
    su := ![![4949, 0, 0], ![-1764, 49, 0]]
    hsu := by decide
    w := ![![12054, -931, -98], ![4802, -294, -49]]
    hw := by decide
    g := ![![![-454773, 84355778, 6027733], ![1591661, -295358910, 0]], ![![158675, -29434488, -2103273], ![-555350, 103060375, 0]]]
    h := ![![![470886, -14413, 37], ![1321090, -3739, 0]], ![![187618, -5716, 14], ![526370, -1415, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {49} * I101N1 =  Ideal.span {B.equivFun.symm ![246, -19, -2]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E101RS1 


noncomputable def E103RS0 : RelationCertificate Table 77 ![![103, 0, 0], ![34, 1, 0]]
  ![-295, 26, 2] ![![77, 0, 0], ![-14, 1, 0]] where
    su := ![![7931, 0, 0], ![2618, 77, 0]]
    hsu := by decide
    w := ![![-22715, 2002, 154], ![2772, -385, 0]]
    hw := by decide
    g := ![![![17, -563, 40], ![29, -3090, 0]], ![![18, -184, 13], ![73, -1005, 0]]]
    h := ![![![-325505, -11818, -66], ![986080, 6800, 0]], ![![39680, 1439, 8], ![-120206, -824, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N0 : Ideal.span {77} * I103N0 =  Ideal.span {B.equivFun.symm ![-295, 26, 2]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E103RS0 


noncomputable def E107RS1 : RelationCertificate Table 5929 ![![107, 0, 0], ![-26, 1, 0]]
  ![1577, 74, -18] ![![5929, 0, 0], ![-2632, 1, 0]] where
    su := ![![634403, 0, 0], ![-154154, 5929, 0]]
    hsu := by decide
    w := ![![9350033, 438746, -106722], ![-4138442, -195657, 47432]]
    hw := by decide
    g := ![![![21290313527, 340389916628448, -129327478996], ![47959828610, 766782622967286, 0]], ![![-4953676676, -79199510075792, 30090999984], ![-11158947193, -178409538905136, 0]]]
    h := ![![![281607739, -11352266, 20046], ![1158924096, -2144940, 0]], ![![-124642898, 5024657, -8873], ![-512953438, 949419, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {5929} * I107N1 =  Ideal.span {B.equivFun.symm ![1577, 74, -18]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E107RS1 


noncomputable def E109RS1 : RelationCertificate Table 121 ![![109, 0, 0], ![8, 1, 0]]
  ![404, -28, -3] ![![121, 0, 0], ![30, 1, 0]] where
    su := ![![13189, 0, 0], ![968, 121, 0]]
    hsu := by decide
    w := ![![48884, -3388, -363], ![14157, -847, -121]]
    hw := by decide
    g := ![![![-2046054, 1059907817, 35332534], ![8252399, -4275236607, 0]], ![![-213085, 110382337, 3679648], ![859440, -445237407, 0]]]
    h := ![![![1140, 142, 0], ![-15482, -3, 0]], ![![321, 40, 0], ![-4359, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {121} * I109N1 =  Ideal.span {B.equivFun.symm ![404, -28, -3]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E109RS1 


noncomputable def E127RS1 : RelationCertificate Table 539 ![![127, 0, 0], ![52, 1, 0]]
  ![-1404, 118, 15] ![![539, 0, 0], ![63, 1, 0]] where
    su := ![![68453, 0, 0], ![28028, 539, 0]]
    hsu := by decide
    w := ![![-756756, 63602, 8085], ![-98637, 8085, 1078]]
    hw := by decide
    g := ![![![15019505, -70207887001, -1114414689], ![-128500193, 600669517360, 0]], ![![6465342, -30222166592, -479718559], ![-55314585, 258568303296, 0]]]
    h := ![![![-11180, -272, -1], ![27278, 142, 0]], ![![-1473, -81, -1], ![3594, 129, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N1 : Ideal.span {539} * I127N1 =  Ideal.span {B.equivFun.symm ![-1404, 118, 15]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E127RS1 


noncomputable def E131RS1 : RelationCertificate Table 77 ![![131, 0, 0], ![-26, 1, 0]]
  ![514, -127, 8] ![![77, 0, 0], ![-14, 1, 0]] where
    su := ![![10087, 0, 0], ![-2002, 77, 0]]
    hsu := by decide
    w := ![![39578, -9779, 616], ![-12628, 3388, -231]]
    hw := by decide
    g := ![![![-33, -4374, 313], ![-9, -24072, 0]], ![![17, 824, -59], ![70, 4539, 0]]]
    h := ![![![1044258, -41645, 57], ![5261434, -7459, 0]], ![![-333172, 13308, -19], ![-1678668, 2486, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {77} * I131N1 =  Ideal.span {B.equivFun.symm ![514, -127, 8]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E131RS1 


noncomputable def E137RS0 : RelationCertificate Table 539 ![![137, 0, 0], ![28, 1, 0]]
  ![6359, -526, -76] ![![539, 0, 0], ![63, 1, 0]] where
    su := ![![73843, 0, 0], ![15092, 539, 0]]
    hsu := by decide
    w := ![![3427501, -283514, -40964], ![452221, -37191, -5390]]
    hw := by decide
    g := ![![![-12253107, 57276352776, 909151544], ![104832146, -490032682200, 0]], ![![-2604529, 12174481417, 193246393], ![22283193, -104159805825, 0]]]
    h := ![![![70344763, 2649635, 4904], ![-344186649, -671924, 0]], ![![9281235, 349590, 647], ![-45411727, -88649, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N0 : Ideal.span {539} * I137N0 =  Ideal.span {B.equivFun.symm ![6359, -526, -76]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E137RS0 


noncomputable def E137RS1 : RelationCertificate Table 847 ![![137, 0, 0], ![47, 1, 0]]
  ![15822, -1081, -172] ![![847, 0, 0], ![-91, 1, 0]] where
    su := ![![116039, 0, 0], ![39809, 847, 0]]
    hsu := by decide
    w := ![![13401234, -915607, -145684], ![-1323014, 90629, 14399]]
    hw := by decide
    g := ![![![130805267, 1043121519731, -11462889639], ![1217495166, 9709067524260, 0]], ![![45584872, 363521804305, -3994750607], ![424289960, 3383553764136, 0]]]
    h := ![![![160192, 3786, 7], ![-466606, -1131, 0]], ![![-15848, -389, -1], ![46162, 154, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {847} * I137N1 =  Ideal.span {B.equivFun.symm ![15822, -1081, -172]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E137RS1 
