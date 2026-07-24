import IdealArithmetic.Examples.NF3_1_462051_1.PrimesBelow3_1_462051_1F1
import IdealArithmetic.Examples.NF3_1_462051_1.ClassGroupData3_1_462051_1

set_option linter.all false

noncomputable section


noncomputable def E37RS1 : RelationCertificate Table 2 ![![37, 0, 0], ![3, 1, 0]]
  ![3, 1, 0] ![![2, 0, 0], ![-23, -3, 1]] where
    su := ![![74, 0, 0], ![6, 2, 0]]
    hsu := by decide
    w := ![![6, 2, 0], ![86, 4, 0]]
    hw := by decide
    g := ![![![21, 3, -1], ![3, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    h := ![![![9, 3, 0], ![-110, 0, 0]], ![![193, 64, 0], ![-2366, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {2} * I37N1 =  Ideal.span {B.equivFun.symm ![3, 1, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E37RS1 


noncomputable def E41RS1 : RelationCertificate Table 260642 ![![41, 0, 0], ![7, 1, 0]]
  ![143123, 9087, -3738] ![![260642, 0, 0], ![-129559, -3, 1]] where
    su := ![![10686322, 0, 0], ![1824494, 260642, 0]]
    hsu := by decide
    w := ![![37303864966, 2368453854, -974279796], ![-18539726102, -1177580556, 484272836]]
    hw := by decide
    g := ![![![1048865913418606, -1087827024780467379, -25194198650703], ![-508845707875758, -2189058390141468735, 0]], ![![251897894449774, -261254878770399199, -6050692954181], ![-122205479982680, -525728972814542190, 0]]]
    h := ![![![142855, 20713, -8], ![-816276, -3410, 0]], ![![-71011, -10303, 3], ![405760, 1735, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {260642} * I41N1 =  Ideal.span {B.equivFun.symm ![143123, 9087, -3738]} * (J0 ^ 4*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_1 E41RS1 


noncomputable def E43RS1 : RelationCertificate Table 19 ![![43, 0, 0], ![-19, 1, 0]]
  ![-48, -16, 3] ![![19, 0, 0], ![-1, 1, 0]] where
    su := ![![817, 0, 0], ![-361, 19, 0]]
    hsu := by decide
    w := ![![-912, -304, 57], ![513, 76, -19]]
    hw := by decide
    g := ![![![6, 66, -65], ![18, 1239, 0]], ![![-1, -26, 25], ![9, -476, 0]]]
    h := ![![![-19686, 1189, -8], ![-44550, 347, 0]], ![![11109, -661, 4], ![25140, -173, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {19} * I43N1 =  Ideal.span {B.equivFun.symm ![-48, -16, 3]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E43RS1 


noncomputable def E47RS0 : RelationCertificate Table 19 ![![47, 0, 0], ![22, 1, 0]]
  ![-66, -22, -3] ![![19, 0, 0], ![-1, 1, 0]] where
    su := ![![893, 0, 0], ![418, 19, 0]]
    hsu := by decide
    w := ![![-1254, -418, -57], ![-399, -152, -19]]
    hw := by decide
    g := ![![![-6, 204, -205], ![24, 3897, 0]], ![![-2, 97, -98], ![20, 1863, 0]]]
    h := ![![![-374, -38, -1], ![796, 44, 0]], ![![-117, -27, -1], ![249, 46, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N0 : Ideal.span {19} * I47N0 =  Ideal.span {B.equivFun.symm ![-66, -22, -3]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E47RS0 


noncomputable def E47RS1 : RelationCertificate Table 13718 ![![47, 0, 0], ![-18, 1, 0]]
  ![37019, 13562, 1801] ![![13718, 0, 0], ![-6097, -3, 1]] where
    su := ![![644746, 0, 0], ![-246924, 13718, 0]]
    hsu := by decide
    w := ![![507826642, 186043516, 24706118], ![-224440198, -82225692, -10919528]]
    hw := by decide
    g := ![![![-10865208512715, 506866532790337, 250538170395], ![4718240802653, 1147200287427064, 0]], ![![4086452957683, -190634743721268, -94228513457], ![-1774551216255, -431467099606452, 0]]]
    h := ![![![10781300287, -663890785, 3607260], ![28151170915, -169539419, 0]], ![![-4764927181, 293414639, -1594273], ![-12441753397, 74930035, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {13718} * I47N1 =  Ideal.span {B.equivFun.symm ![37019, 13562, 1801]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E47RS1 


noncomputable def E47RS2 : RelationCertificate Table 722 ![![47, 0, 0], ![-4, 1, 0]]
  ![287, -88, 7] ![![722, 0, 0], ![-321, -3, 1]] where
    su := ![![33934, 0, 0], ![-2888, 722, 0]]
    hsu := by decide
    w := ![![207214, -63536, 5054], ![-109022, 24548, -1444]]
    hw := by decide
    g := ![![![-29609846561, 65039126312, 666198031], ![12895165836, 164630048069, 0]], ![![2038031801, -4476612235, -45854095], ![-887567934, -11331408175, 0]]]
    h := ![![![337, -84, 0], ![3888, 7, 0]], ![![-169, 46, -1], ![-1948, 45, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N2 : Ideal.span {722} * I47N2 =  Ideal.span {B.equivFun.symm ![287, -88, 7]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E47RS2 


noncomputable def E53RS1 : RelationCertificate Table 19 ![![53, 0, 0], ![10, 1, 0]]
  ![127, -2, -2] ![![19, 0, 0], ![-1, 1, 0]] where
    su := ![![1007, 0, 0], ![190, 19, 0]]
    hsu := by decide
    w := ![![2413, -38, -38], ![-437, 57, 0]]
    hw := by decide
    g := ![![![19, 9032, -9060], ![480, 172134, 0]], ![![7, 3010, -3020], ![173, 57378, 0]]]
    h := ![![![339, 34, 0], ![-1784, -2, 0]], ![![-71, -17, -1], ![374, 53, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {19} * I53N1 =  Ideal.span {B.equivFun.symm ![127, -2, -2]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E53RS1 


noncomputable def E61RS1 : RelationCertificate Table 2 ![![61, 0, 0], ![24, 1, 0]]
  ![-2637, -963, -128] ![![2, 0, 0], ![-23, -3, 1]] where
    su := ![![122, 0, 0], ![48, 2, 0]]
    hsu := by decide
    w := ![![-5274, -1926, -256], ![-29094, -10624, -1412]]
    hw := by decide
    g := ![![![26, -118, 20], ![-49, 0, 0]], ![![25, -36, 6], ![-17, 0, 0]]]
    h := ![![![-20145, -1019, -9], ![51092, 421, 0]], ![![-110991, -5600, -49], ![281496, 2283, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {2} * I61N1 =  Ideal.span {B.equivFun.symm ![-2637, -963, -128]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E61RS1 


noncomputable def E67RS1 : RelationCertificate Table 13718 ![![67, 0, 0], ![-15, 1, 0]]
  ![1507, 1636, -245] ![![13718, 0, 0], ![-6097, -3, 1]] where
    su := ![![919106, 0, 0], ![-205770, 13718, 0]]
    hsu := by decide
    w := ![![20673026, 22442648, -3360910], ![-8820674, -9931832, 1481544]]
    hw := by decide
    g := ![![![2303376245281, -107453467407939, -53112986133], ![-1000246211205, -243201396661190, 0]], ![![-314297588616, 14662114480675, 7247310876], ![136484433206, 33185031676720, 0]]]
    h := ![![![4186, -263, -3], ![18597, -44, 0]], ![![-1744, 114, 1], ![-7747, 41, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {13718} * I67N1 =  Ideal.span {B.equivFun.symm ![1507, 1636, -245]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E67RS1 


noncomputable def E71RS1 : RelationCertificate Table 6859 ![![71, 0, 0], ![22, 1, 0]]
  ![-97328, -2524, 2055] ![![6859, 0, 0], ![-2205, 1, 0]] where
    su := ![![486989, 0, 0], ![150898, 6859, 0]]
    hsu := by decide
    w := ![![-667572752, -17312116, 14095245], ![214926765, 5542072, -4533799]]
    hw := by decide
    g := ![![![17440504993, 410566905663550, -186198146744], ![54251439267, 1277133088525020, 0]], ![![5595070371, 131713517726591, -59734022795], ![17404348121, 409715662354200, 0]]]
    h := ![![![-9777572112, -502901586, -2657540], ![31554887392, 188687395, 0]], ![![3147908937, 161910188, 855601], ![-10159159236, -60748332, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {6859} * I71N1 =  Ideal.span {B.equivFun.symm ![-97328, -2524, 2055]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E71RS1 


noncomputable def E73RS1 : RelationCertificate Table 130321 ![![73, 0, 0], ![-2, 1, 0]]
  ![124858, -16185, -54] ![![130321, 0, 0], ![-36500, 1, 0]] where
    su := ![![9513433, 0, 0], ![-260642, 130321, 0]]
    hsu := by decide
    w := ![![16271619418, -2109245385, -7037334], ![-4557325370, 590875414, 1954815]]
    hw := by decide
    g := ![![![86106, 27913959575, -764766], ![307435, 99665071947, 0]], ![![25591, -449168957, 12306], ![91371, -1603730070, 0]]]
    h := ![![![33424835162, -16724619089, 6101070], ![1220006420984, -445378164, 0]], ![![-9361566806, 4684200780, -1708777], ![-341697170934, 124740736, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {130321} * I73N1 =  Ideal.span {B.equivFun.symm ![124858, -16185, -54]} * (J0 ^ 4*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_0 E73RS1 
