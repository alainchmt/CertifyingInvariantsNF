import IdealArithmetic.Examples.NF3_3_670761_3.PrimesBelow3_3_670761_3F0
import IdealArithmetic.Examples.NF3_3_670761_3.ClassGroupData3_3_670761_3

set_option linter.all false

noncomputable section


noncomputable def E3RS0 : RelationCertificate Table 1445 ![![3, 0, 0], ![1, 1, 0]]
  ![266, 11, -15] ![![1445, 0, 0], ![-477, 1, 0]] where
    su := ![![4335, 0, 0], ![1445, 1445, 0]]
    hsu := by decide
    w := ![![384370, 15895, -21675], ![-131495, -5780, 7225]]
    hw := by decide
    g := ![![![848033, -236607394, 2485375], ![-442640, -718273376, 0]], ![![441580, -123118383, 1293262], ![-229396, -373752716, 0]]]
    h := ![![![72, -13, -30], ![20, 15, 0]], ![![-25, 4, 10], ![-6, -5, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {1445} * I3N0 =  Ideal.span {B.equivFun.symm ![266, 11, -15]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E3RS0 


noncomputable def E5RS0 : RelationCertificate Table 5 ![![5, 0, 0], ![-34, -1, 1]]
  ![6, 1, 0] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![25, 0, 0], ![-170, -5, 5]]
    hsu := by decide
    w := ![![30, 5, 0], ![-10, 5, 5]]
    hw := by decide
    g := ![![![20185, 5415, -223], ![-6988, 0, -372]], ![![-148044, -39717, 1636], ![51278, 0, 2728]]]
    h := ![![![33, 47, 13], ![-203, -23, 0]], ![![-9, -18, -5], ![80, 9, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {5} * I5N0 =  Ideal.span {B.equivFun.symm ![6, 1, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 5 ![![5, 0, 0], ![-71, -4, 2]]
  ![-11, -1, 0] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![25, 0, 0], ![-355, -20, 10]]
    hsu := by decide
    w := ![![-55, -5, 0], ![20, -10, -5]]
    hw := by decide
    g := ![![![-2610, -700, 29], ![906, 0, 48]], ![![37978, 10188, -419], ![-13152, 0, -700]]]
    h := ![![![-43, 21, 84], ![736, 86, 0]], ![![76, -6, -37], ![-304, -36, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {5} * I5N1 =  Ideal.span {B.equivFun.symm ![-11, -1, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E5RS1 


noncomputable def E5RS2 : RelationCertificate Table 1 ![![5, 0, 0], ![-2, 1, 0]]
  ![1, 0, 0] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![5, 0, 0], ![-2, 1, 0]]
    hsu := by decide
    w := ![![5, 0, 0], ![-2, 1, 0]]
    hw := by decide
    g := ![![![545, 145, -6], ![-185, 0, -10]], ![![-271, -73, 3], ![96, 0, 5]]]
    h := ![![![545, 145, -6], ![-185, 0, -10]], ![![-271, -73, 3], ![96, 0, 5]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N2 : Ideal.span {1} * I5N2 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E5RS2 


noncomputable def E7RS0 : RelationCertificate Table 425 ![![7, 0, 0], ![0, 1, 0]]
  ![-468, -43, 20] ![![425, 0, 0], ![33, 1, 0]] where
    su := ![![2975, 0, 0], ![0, 425, 0]]
    hsu := by decide
    w := ![![-198900, -18275, 8500], ![-9350, -850, 425]]
    hw := by decide
    g := ![![![536174765441, 9198346051204, 1352719842523], ![63275561055, -114981186709566, 14861]], ![![-76596344554, -1314048568908, -193245564290], ![-9039359550, 16425872978238, -2123]]]
    h := ![![![397332, 194719, 993500], ![27820, -1390896, 0]], ![![18678, 9153, 46703], ![1311, -65384, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {425} * I7N0 =  Ideal.span {B.equivFun.symm ![-468, -43, 20]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E7RS0 


noncomputable def E13RS0 : RelationCertificate Table 85 ![![13, 0, 0], ![0, 1, 0]]
  ![-438, -13, 10] ![![85, 0, 0], ![33, 1, 0]] where
    su := ![![1105, 0, 0], ![0, 85, 0]]
    hsu := by decide
    w := ![![-37230, -1105, 850], ![-11390, -340, 255]]
    hw := by decide
    g := ![![![6391, 136378, 20059], ![4087, -341086, 13]], ![![-502, -10484, -1542], ![-286, 26220, -1]]]
    h := ![![![74022, 36809, 185140], ![2832, -481362, 0]], ![![22646, 11261, 56641], ![869, -147266, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {85} * I13N0 =  Ideal.span {B.equivFun.symm ![-438, -13, 10]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E13RS0 


noncomputable def E17RS0 : RelationCertificate Table 17 ![![17, 0, 0], ![0, 1, 0]]
  ![-37, -3, 1] ![![17, 0, 0], ![-1, 1, 0]] where
    su := ![![289, 0, 0], ![0, 17, 0]]
    hsu := by decide
    w := ![![-629, -51, 17], ![340, 17, -17]]
    hw := by decide
    g := ![![![-64988, -225, -163019], ![3822, 554265, 0]], ![![-1723, -6, -4328], ![103, 14715, 0]]]
    h := ![![![1221, 609, 3058], ![41, -10397, 0]], ![![-660, -330, -1653], ![-9, 5620, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N0 : Ideal.span {17} * I17N0 =  Ideal.span {B.equivFun.symm ![-37, -3, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E17RS0 


noncomputable def E17RS1 : RelationCertificate Table 17 ![![17, 0, 0], ![1, 1, 0]]
  ![20, 3, -1] ![![17, 0, 0], ![-1, 1, 0]] where
    su := ![![289, 0, 0], ![17, 17, 0]]
    hsu := by decide
    w := ![![340, 51, -17], ![-323, -34, 17]]
    hw := by decide
    g := ![![![-2, -1, -2], ![17, 7, 0]], ![![1, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 2], ![17, -7, 0]], ![![-2, -1, -2], ![1, 7, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {17} * I17N1 =  Ideal.span {B.equivFun.symm ![20, 3, -1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E17RS1 


noncomputable def E17RS2 : RelationCertificate Table 1 ![![17, 0, 0], ![-1, 1, 0]]
  ![1, 0, 0] ![![17, 0, 0], ![-1, 1, 0]] where
    su := ![![17, 0, 0], ![-1, 1, 0]]
    hsu := by decide
    w := ![![17, 0, 0], ![-1, 1, 0]]
    hw := by decide
    g := ![![![289, 0, 720], ![0, -2448, 0]], ![![-17, -1, -45], ![18, 153, 0]]]
    h := ![![![289, 0, 720], ![0, -2448, 0]], ![![-17, -1, -45], ![18, 153, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N2 : Ideal.span {1} * I17N2 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E17RS2 


noncomputable def E29RS0 : RelationCertificate Table 7225 ![![29, 0, 0], ![-11, 1, 0]]
  ![-1711, -11, 15] ![![7225, 0, 0], ![-3367, 1, 0]] where
    su := ![![209525, 0, 0], ![-79475, 7225, 0]]
    hsu := by decide
    w := ![![-12361975, -79475, 108375], ![5765550, 36125, -50575]]
    hw := by decide
    g := ![![![-1876886, 4313274919, -6407135], ![1471956, 9258292561, -26]], ![![578431, -1327217959, 1971510], ![-450991, -2848826561, 8]]]
    h := ![![![-10172, 61724, -30965], ![5993, 179600, 0]], ![![4756, -28789, 14442], ![-2764, -83765, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N0 : Ideal.span {7225} * I29N0 =  Ideal.span {B.equivFun.symm ![-1711, -11, 15]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E29RS0 


noncomputable def E29RS1 : RelationCertificate Table 7225 ![![29, 0, 0], ![-10, 1, 0]]
  ![-3041, -66, 90] ![![7225, 0, 0], ![-3367, 1, 0]] where
    su := ![![209525, 0, 0], ![-72250, 7225, 0]]
    hsu := by decide
    w := ![![-21971225, -476850, 650250], ![10266725, 223975, -303450]]
    hw := by decide
    g := ![![![-818346801000278745, 1880530076896795550930, -2793419735155195702], ![641647578666399352, 4036491517298552128728, -1047596]], ![![310407407214704944, -713304511785586060819, 1059573002780774260], ![-243383564273696548, -1531082989017951141312, 397364]]]
    h := ![![![-965787699, 5119159033, -2853738790], ![509552977, 16551685000, 0]], ![![451291819, -2392072858, 1333490727], ![-238103112, -7734246225, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {7225} * I29N1 =  Ideal.span {B.equivFun.symm ![-3041, -66, 90]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E29RS1 


noncomputable def E29RS2 : RelationCertificate Table 7225 ![![29, 0, 0], ![-8, 1, 0]]
  ![4752, 77, -105] ![![7225, 0, 0], ![-3367, 1, 0]] where
    su := ![![209525, 0, 0], ![-57800, 7225, 0]]
    hsu := by decide
    w := ![![34333200, 556325, -758625], ![-16032275, -260100, 354025]]
    hw := by decide
    g := ![![![42039245376175, -96604604357059508, 143500632820210], ![-32962040624810, -207358377729903103, 54476396]], ![![-9701364315962, 22293370236264904, -33115530650848], ![7606624763067, 47851933322329125, -12571476]]]
    h := ![![![10748, -41103, 29465], ![-4362, -170918, 0]], ![![-5015, 19193, -13759], ![2051, 79812, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N2 : Ideal.span {7225} * I29N2 =  Ideal.span {B.equivFun.symm ![4752, 77, -105]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E29RS2 
