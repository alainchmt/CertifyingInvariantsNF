import IdealArithmetic.Examples.NF3_1_865755_1.PrimesBelow3_1_865755_1F4
import IdealArithmetic.Examples.NF3_1_865755_1.ClassGroupData3_1_865755_1

set_option linter.all false

noncomputable section


noncomputable def E199RS0 : RelationCertificate Table 256 ![![199, 0, 0], ![48, 1, 0]]
  ![-547963, -18960, 16493] ![![256, 0, 0], ![-111, 1, 0]] where
    su := ![![50944, 0, 0], ![12288, 256, 0]]
    hsu := by decide
    w := ![![-140278528, -4853760, 4222208], ![65387520, 2180864, -1942016]]
    hw := by decide
    g := ![![![-3587215036, 258442241245, -11747845118], ![2564934323, 601489004703, 0]], ![![-870044019, 62681527561, -2849275714], ![622095517, 145882699998, 0]]]
    h := ![![![-79824241, -2132588463, -217626343], ![-29970573, 8661531750, 0]], ![![37208442, 994063000, 101442121], ![13970236, -4037397933, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R199N0 : Ideal.span {256} * I199N0 =  Ideal.span {B.equivFun.symm ![-547963, -18960, 16493]} * (J0 ^ 8) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8 E199RS0 


noncomputable def E199RS1 : RelationCertificate Table 16 ![![199, 0, 0], ![72, 1, 0]]
  ![-77, -16, -5] ![![16, 0, 0], ![1, 1, 0]] where
    su := ![![3184, 0, 0], ![1152, 16, 0]]
    hsu := by decide
    w := ![![-1232, -256, -80], ![-1504, -304, -80]]
    hw := by decide
    g := ![![![-18151694, -18151660, -45733670], ![-2268948, 146347747, 0]], ![![-6589702, -6589691, -16602930], ![-823703, 53129377, 0]]]
    h := ![![![523, 25110, 1720], ![455, -68457, 0]], ![![676, 30658, 2100], ![452, -83581, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R199N1 : Ideal.span {16} * I199N1 =  Ideal.span {B.equivFun.symm ![-77, -16, -5]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E199RS1 


noncomputable def E199RS2 : RelationCertificate Table 64 ![![199, 0, 0], ![79, 1, 0]]
  ![317219, 9552, -9093] ![![64, 0, 0], ![17, 1, 0]] where
    su := ![![12736, 0, 0], ![5056, 64, 0]]
    hsu := by decide
    w := ![![20302016, 611328, -581952], ![2874880, 134528, -97728]]
    hw := by decide
    g := ![![![-51723218, -506318269, -140738828], ![-21650147, 1800551482, 0]], ![![-14152004903709, -141548749626455, -39345012160191], ![-5970825515453, 503616155214651, 0]]]
    h := ![![![-4200146426, -211332944869, -13209166317], ![-2729369357, 525724817598, 0]], ![![-594688697, -29922125341, -1870254213], ![-386444799, 74436117372, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R199N2 : Ideal.span {64} * I199N2 =  Ideal.span {B.equivFun.symm ![317219, 9552, -9093]} * (J0 ^ 6) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6 E199RS2 


noncomputable def E223RS1 : RelationCertificate Table 64 ![![223, 0, 0], ![4, 1, 0]]
  ![8955, 208, -237] ![![64, 0, 0], ![17, 1, 0]] where
    su := ![![14272, 0, 0], ![256, 64, 0]]
    hsu := by decide
    w := ![![573120, 13312, -15168], ![86528, 3456, -2752]]
    hw := by decide
    g := ![![![-1441, -4980, -1386], ![-439, 16970, 0]], ![![-3248907, -32494758, -9032271], ![-1370710, 115612997, 0]]]
    h := ![![![-64016907, -160117688, -160126059], ![-1866288, 7141622184, 0]], ![![-9662204, -24166888, -24168151], ![-281552, 1077899526, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R223N1 : Ideal.span {64} * I223N1 =  Ideal.span {B.equivFun.symm ![8955, 208, -237]} * (J0 ^ 6) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6 E223RS1 


noncomputable def E239RS0 : RelationCertificate Table 8 ![![239, 0, 0], ![46, 1, 0]]
  ![195, 40, 11] ![![8, 0, 0], ![1, 1, 0]] where
    su := ![![1912, 0, 0], ![368, 8, 0]]
    hsu := by decide
    w := ![![1560, 320, 88], ![3344, 704, 200]]
    hw := by decide
    g := ![![![-106, -5, 4], ![-9, 0, 0]], ![![-1, 14, 40], ![6, -63, 0]]]
    h := ![![![-1943, -47478, -5051], ![-398, 241440, 0]], ![![-4116, -101751, -10825], ![-1103, 517440, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R239N0 : Ideal.span {8} * I239N0 =  Ideal.span {B.equivFun.symm ![195, 40, 11]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E239RS0 


noncomputable def E239RS1 : RelationCertificate Table 256 ![![239, 0, 0], ![70, 1, 0]]
  ![-113219, -3984, 3429] ![![256, 0, 0], ![-111, 1, 0]] where
    su := ![![61184, 0, 0], ![17920, 256, 0]]
    hsu := by decide
    w := ![![-28984064, -1019904, 877824], ![13516032, 458752, -403968]]
    hw := by decide
    g := ![![![-8122, 15380, -1344], ![3817, 40416, 0]], ![![-3088419, 222309959, -10105624], ![2207562, 517397639, 0]]]
    h := ![![![7146483547, 287977722908, 20281093131], ![3298040300, -969436250976, 0]], ![![-3332623151, -134292789291, -9457691862], ![-1537976507, 452077670688, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R239N1 : Ideal.span {256} * I239N1 =  Ideal.span {B.equivFun.symm ![-113219, -3984, 3429]} * (J0 ^ 8) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8 E239RS1 


noncomputable def E239RS2 : RelationCertificate Table 128 ![![239, 0, 0], ![-116, 1, 0]]
  ![1861175, 387792, 109103] ![![128, 0, 0], ![17, 1, 0]] where
    su := ![![30592, 0, 0], ![-14848, 128, 0]]
    hsu := by decide
    w := ![![238230400, 49637376, 13965184], ![62855296, 13096448, 3684608]]
    hw := by decide
    g := ![![![420564009, 3887464687, 1080038408], ![86227057, -27648983652, 0]], ![![14629861744781, 135230683602639, 37570588149676], ![2999518228648, -961807056631501, 0]]]
    h := ![![![57997474511, -4664974480739, 202833649612], ![-47668123382, -9695448429633, 0]], ![![15302196645, -1230818366630, 53516130119], ![-12576875179, -2558071013931, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R239N2 : Ideal.span {128} * I239N2 =  Ideal.span {B.equivFun.symm ![1861175, 387792, 109103]} * (J0 ^ 7) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7 E239RS2 


noncomputable def E241RS0 : RelationCertificate Table 256 ![![241, 0, 0], ![53, 1, 0]]
  ![212269, 11120, -7595] ![![256, 0, 0], ![-111, 1, 0]] where
    su := ![![61696, 0, 0], ![13568, 256, 0]]
    hsu := by decide
    w := ![![54340864, 2846720, -1944320], ![-25658624, -1307136, 906240]]
    hw := by decide
    g := ![![![-29871, -213847, 7065], ![12347, -478674, 0]], ![![5981285725, -430947125881, 19589264335], ![-4276835155, -1002970367809, 0]]]
    h := ![![![11266847, 326933146, 30273025], ![3834430, -1459161324, 0]], ![![-5320055, -154372188, -14294400], ![-1810350, 688990788, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R241N0 : Ideal.span {256} * I241N0 =  Ideal.span {B.equivFun.symm ![212269, 11120, -7595]} * (J0 ^ 8) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8 E241RS0 


noncomputable def E241RS1 : RelationCertificate Table 2 ![![241, 0, 0], ![73, 1, 0]]
  ![-21, -2, 1] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![482, 0, 0], ![146, 2, 0]]
    hsu := by decide
    w := ![![-42, -4, 2], ![254, 14, -10]]
    hw := by decide
    g := ![![![-17332, -17337, -65004], ![-17333, 26001, 0]], ![![-5779, -5779, -21668], ![-5778, 8667, 0]]]
    h := ![![![-11961, -505382, -34149], ![-5608, 1645982, 0]], ![![72161, 3056945, 206560], ![34544, -9956193, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R241N1 : Ideal.span {2} * I241N1 =  Ideal.span {B.equivFun.symm ![-21, -2, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E241RS1 


noncomputable def E251RS0 : RelationCertificate Table 64 ![![251, 0, 0], ![89, 1, 0]]
  ![8839, 1680, -705] ![![64, 0, 0], ![17, 1, 0]] where
    su := ![![16064, 0, 0], ![5696, 64, 0]]
    hsu := by decide
    w := ![![565696, 107520, -45120], ![-43072, 11584, -2880]]
    hw := by decide
    g := ![![![-157432325, -1574516014, -437653850], ![-66419771, 5601958879, 0]], ![![-57062406, -570686372, -158628485], ![-24074136, 2030440225, 0]]]
    h := ![![![-360286, -19488715, -1082755], ![-205255, 54354160, 0]], ![![27509, 1490071, 82785], ![15800, -4155816, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R251N0 : Ideal.span {64} * I251N0 =  Ideal.span {B.equivFun.symm ![8839, 1680, -705]} * (J0 ^ 6) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6 E251RS0 


noncomputable def E251RS1 : RelationCertificate Table 256 ![![251, 0, 0], ![-50, 1, 0]]
  ![4087, 848, 239] ![![256, 0, 0], ![-111, 1, 0]] where
    su := ![![64256, 0, 0], ![-12800, 256, 0]]
    hsu := by decide
    w := ![![1046272, 217088, 61184], ![-385280, -79872, -22528]]
    hw := by decide
    g := ![![![-730, 59854, -2721], ![797, 139304, 0]], ![![-175996830, 12680423570, -576405234], ![125844218, 29511947983, 0]]]
    h := ![![![-9455699, 245622924, -25064726], ![2862281, 1258249293, 0]], ![![3482159, -90451737, 9230197], ![-1053768, -463355907, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R251N1 : Ideal.span {256} * I251N1 =  Ideal.span {B.equivFun.symm ![4087, 848, 239]} * (J0 ^ 8) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8 E251RS1 


noncomputable def E251RS2 : RelationCertificate Table 16 ![![251, 0, 0], ![-39, 1, 0]]
  ![127549, 26576, 7477] ![![16, 0, 0], ![1, 1, 0]] where
    su := ![![4016, 0, 0], ![-624, 16, 0]]
    hsu := by decide
    w := ![![2040784, 425216, 119632], ![2266784, 472304, 132880]]
    hw := by decide
    g := ![![![1033, 1899, 4717], ![192, -15071, 0]], ![![-142, -287, -705], ![-17, 2254, 0]]]
    h := ![![![564102430, -11106803393, 1461490687], ![-131899477, -73366830992, 0]], ![![626572138, -12336790327, 1623338735], ![-146506172, -81491602836, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R251N2 : Ideal.span {16} * I251N2 =  Ideal.span {B.equivFun.symm ![127549, 26576, 7477]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E251RS2 


noncomputable def E257RS1 : RelationCertificate Table 16 ![![257, 0, 0], ![122, 1, 0]]
  ![-71, 0, 1] ![![16, 0, 0], ![1, 1, 0]] where
    su := ![![4112, 0, 0], ![1952, 16, 0]]
    hsu := by decide
    w := ![![-1136, 0, 16], ![208, -32, 0]]
    hw := by decide
    g := ![![![11105080, 11105084, 27979608], ![1388145, -89534746, 0]], ![![6682635, 6682637, 16837114], ![835336, -53878765, 0]]]
    h := ![![![141, 21474, 873], ![438, -44872, 0]], ![![-63, -3936, -160], ![-2, 8224, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R257N1 : Ideal.span {16} * I257N1 =  Ideal.span {B.equivFun.symm ![-71, 0, 1]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E257RS1 
