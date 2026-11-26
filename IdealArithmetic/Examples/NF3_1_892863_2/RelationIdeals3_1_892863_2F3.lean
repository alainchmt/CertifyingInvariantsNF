import IdealArithmetic.Examples.NF3_1_892863_2.PrimesBelow3_1_892863_2F3
import IdealArithmetic.Examples.NF3_1_892863_2.ClassGroupData3_1_892863_2

set_option linter.all false

noncomputable section


noncomputable def E139RS1 : RelationCertificate Table 2 ![![139, 0, 0], ![19, 1, 0]]
  ![-92, 13, 8] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![278, 0, 0], ![38, 2, 0]]
    hsu := by decide
    w := ![![-184, 26, 16], ![1126, -282, 52]]
    hw := by decide
    g := ![![![-39090, 6145, -1466], ![-16471, 0, 0]], ![![-6666, 1048, -250], ![-2809, 0, 0]]]
    h := ![![![815, 8498, 1700], ![251, -59073, 0]], ![![-5091, -52265, -10454], ![-966, 363283, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N1 : Ideal.span {2} * I139N1 =  Ideal.span {B.equivFun.symm ![-92, 13, 8]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E139RS1 


noncomputable def E149RS1 : RelationCertificate Table 2 ![![149, 0, 0], ![-66, 1, 0]]
  ![396259, 17504, 12275] ![![2, 0, 0], ![18, 2, 1]] where
    su := ![![298, 0, 0], ![-132, 2, 0]]
    hsu := by decide
    w := ![![792518, 35008, 24550], ![12388524, 547240, 383762]]
    hw := by decide
    g := ![![![15, -58, -148], ![53, 0, 0]], ![![-20, 27, 70], ![-10, -3, 0]]]
    h := ![![![636555, -27294106, 1679919], ![-465112, -62573914, 0]], ![![9950366, -426657420, 26260245], ![-7270940, -978146156, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R149N1 : Ideal.span {2} * I149N1 =  Ideal.span {B.equivFun.symm ![396259, 17504, 12275]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E149RS1 


noncomputable def E151RS0 : RelationCertificate Table 8 ![![151, 0, 0], ![-56, 1, 0]]
  ![5, 1, 1] ![![8, 0, 0], ![20, 1, 1]] where
    su := ![![1208, 0, 0], ![-448, 8, 0]]
    hsu := by decide
    w := ![![40, 8, 8], ![312, 16, 0]]
    hw := by decide
    g := ![![![7711, -4482, -1249], ![18617, -2874, 0]], ![![-2874, 1660, 462], ![-6892, 1065, 0]]]
    h := ![![![3985, -132906, 9667], ![-2288, -364929, 0]], ![![31017, -1039159, 75584], ![-18269, -2853296, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N0 : Ideal.span {8} * I151N0 =  Ideal.span {B.equivFun.symm ![5, 1, 1]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E151RS0 


noncomputable def E163RS0 : RelationCertificate Table 8 ![![163, 0, 0], ![12, 1, 0]]
  ![-123, 45, -23] ![![8, 0, 0], ![-33, 1, -2]] where
    su := ![![1304, 0, 0], ![96, 8, 0]]
    hsu := by decide
    w := ![![-984, 360, -184], ![-16736, 3512, 56]]
    hw := by decide
    g := ![![![-2540, -603, 2228], ![9875, -580, 0]], ![![-213, -90, 182], ![876, -43, 0]]]
    h := ![![![128001, 838902, 258151], ![14586, -10519659, 0]], ![![2172098, 14235594, 4380649], ![247402, -178511445, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R163N0 : Ideal.span {8} * I163N0 =  Ideal.span {B.equivFun.symm ![-123, 45, -23]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E163RS0 


noncomputable def E163RS1 : RelationCertificate Table 32 ![![163, 0, 0], ![67, 1, 0]]
  ![-6672977, 1187899, 281435] ![![32, 0, 0], ![107, 5, 6]] where
    su := ![![5216, 0, 0], ![2144, 32, 0]]
    hsu := by decide
    w := ![![-213535264, 38012768, 9005920], ![420923552, -56454720, -40293376]]
    hw := by decide
    g := ![![![-47110970064, -752341322, 11587847806], ![-155472138017, 7434, 0]], ![![-20724188016, -330956600, 5097511952], ![-68392432061, 3093, 0]]]
    h := ![![![107746956, 4684988718, 275615225], ![73030945, -11231250060, 0]], ![![-212264894, -9229568919, -542974828], ![-143872945, 22125909449, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R163N1 : Ideal.span {32} * I163N1 =  Ideal.span {B.equivFun.symm ![-6672977, 1187899, 281435]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E163RS1 


noncomputable def E163RS2 : RelationCertificate Table 16 ![![163, 0, 0], ![-79, 1, 0]]
  ![-3645, -161, -113] ![![16, 0, 0], ![12, 1, 1]] where
    su := ![![2608, 0, 0], ![-1264, 16, 0]]
    hsu := by decide
    w := ![![-58320, -2576, -1808], ![-74944, -3312, -2320]]
    hw := by decide
    g := ![![![-45680, 8679, 694], ![-33669, 7518, 0]], ![![21636, -4114, -330], ![15973, -3563, 0]]]
    h := ![![![63369, -3448643, 176869], ![-51672, -7207440, 0]], ![![81373, -4431668, 227285], ![-66523, -9261900, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R163N2 : Ideal.span {16} * I163N2 =  Ideal.span {B.equivFun.symm ![-3645, -161, -113]} * (J0 ^ 4*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_0 E163RS2 


noncomputable def E167RS1 : RelationCertificate Table 2 ![![167, 0, 0], ![-68, 1, 0]]
  ![2218792, 98011, 68732] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![334, 0, 0], ![-136, 2, 0]]
    hsu := by decide
    w := ![![4437584, 196022, 137464], ![12655882, 559050, 392044]]
    hw := by decide
    g := ![![![4957, -1926, -58], ![1517, 0, 0]], ![![-2080, 825, -4], ![-626, 0, 0]]]
    h := ![![![-149509418, 6358183021, -379627944], ![98951119, 15849483845, 0]], ![![-426397253, 18133383852, -1082689694], ![282206151, 45202343730, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R167N1 : Ideal.span {2} * I167N1 =  Ideal.span {B.equivFun.symm ![2218792, 98011, 68732]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E167RS1 


noncomputable def E181RS1 : RelationCertificate Table 2 ![![181, 0, 0], ![62, 1, 0]]
  ![-9, 1, 1] ![![2, 0, 0], ![18, 1, 1]] where
    su := ![![362, 0, 0], ![124, 2, 0]]
    hsu := by decide
    w := ![![-18, 2, 2], ![50, 0, -16]]
    hw := by decide
    g := ![![![-141851, 762319, 245378], ![-772745, 93990, 0]], ![![-49115, 263879, 84938], ![-267488, 32535, 0]]]
    h := ![![![133, 5496, 349], ![121, -15792, 0]], ![![-465, -15245, -968], ![-55, 43800, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R181N1 : Ideal.span {2} * I181N1 =  Ideal.span {B.equivFun.symm ![-9, 1, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E181RS1 


noncomputable def E191RS1 : RelationCertificate Table 2 ![![191, 0, 0], ![73, 1, 0]]
  ![-330, -161, 282] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![382, 0, 0], ![146, 2, 0]]
    hsu := by decide
    w := ![![-660, -322, 564], ![41366, -8266, -644]]
    hw := by decide
    g := ![![![32459156, -5103093, 1217348], ![13678033, 0, 0]], ![![13205260, -2076076, 495250], ![5564593, 0, 0]]]
    h := ![![![-149943, -6863152, -371006], ![-93047, 17715607, 0]], ![![9434963, 432043187, 23355346], ![5868198, -1115217852, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R191N1 : Ideal.span {2} * I191N1 =  Ideal.span {B.equivFun.symm ![-330, -161, 282]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E191RS1 


noncomputable def E193RS1 : RelationCertificate Table 4 ![![193, 0, 0], ![-72, 1, 0]]
  ![12873, -2885, 181] ![![4, 0, 0], ![35, 1, 2]] where
    su := ![![772, 0, 0], ![-288, 4, 0]]
    hsu := by decide
    w := ![![51492, -11540, 724], ![-419832, 75844, 16356]]
    hw := by decide
    g := ![![![2564400, -1381958, -5335745], ![19425233, -530792, 0]], ![![-909004, 553732, 1900839], ![-6864852, 195961, 0]]]
    h := ![![![117409, -5093264, 286965], ![-70069, -13846016, 0]], ![![-956270, 41500259, -2338183], ![571966, 112818352, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R193N1 : Ideal.span {4} * I193N1 =  Ideal.span {B.equivFun.symm ![12873, -2885, 181]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E193RS1 
