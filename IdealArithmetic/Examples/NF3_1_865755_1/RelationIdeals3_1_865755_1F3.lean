import IdealArithmetic.Examples.NF3_1_865755_1.PrimesBelow3_1_865755_1F3
import IdealArithmetic.Examples.NF3_1_865755_1.ClassGroupData3_1_865755_1

set_option linter.all false

noncomputable section


noncomputable def E139RS1 : RelationCertificate Table 64 ![![139, 0, 0], ![10, 1, 0]]
  ![111, 272, -89] ![![64, 0, 0], ![17, 1, 0]] where
    su := ![![8896, 0, 0], ![640, 64, 0]]
    hsu := by decide
    w := ![![7104, 17408, -5696], ![-22400, 1536, -64]]
    hw := by decide
    g := ![![![-133, -5828, -1619], ![-111, 21096, 0]], ![![-3568, -36549, -10159], ![-1514, 130107, 0]]]
    h := ![![![-161893, -897425, -407981], ![-18047, 11341854, 0]], ![![621794, 3446902, 1567001], ![69554, -43562628, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N1 : Ideal.span {64} * I139N1 =  Ideal.span {B.equivFun.symm ![111, 272, -89]} * (J0 ^ 6) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6 E139RS1 


noncomputable def E149RS1 : RelationCertificate Table 128 ![![149, 0, 0], ![-40, 1, 0]]
  ![22781, -272, -347] ![![128, 0, 0], ![17, 1, 0]] where
    su := ![![19072, 0, 0], ![-5120, 128, 0]]
    hsu := by decide
    w := ![![2915968, -34816, -44416], ![289920, 4352, -6912]]
    hw := by decide
    g := ![![![-5991, -23913, -6647], ![-865, 164866, 0]], ![![64261455, 593993971, 165026918], ![13175338, -4224688275, 0]]]
    h := ![![![1545889, -33486563, 4293697], ![-639745, -127952240, 0]], ![![153701, -3328570, 426794], ![-63444, -12718472, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R149N1 : Ideal.span {128} * I149N1 =  Ideal.span {B.equivFun.symm ![22781, -272, -347]} * (J0 ^ 7) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7 E149RS1 


noncomputable def E151RS1 : RelationCertificate Table 128 ![![151, 0, 0], ![-50, 1, 0]]
  ![-5103, 3632, -1063] ![![128, 0, 0], ![17, 1, 0]] where
    su := ![![19328, 0, 0], ![-6400, 128, 0]]
    hsu := by decide
    w := ![![-653184, 464896, -136064], ![-376064, 18816, 1152]]
    hw := by decide
    g := ![![![-256206019, -2368455989, -658018422], ![-52530888, 16845309393, 0]], ![![80939229, 748208582, 207871727], ![16595203, -5321524527, 0]]]
    h := ![![![2349, -67579, 6892], ![-1138, -208351, 0]], ![![1104, -31982, 3264], ![-550, -98571, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N1 : Ideal.span {128} * I151N1 =  Ideal.span {B.equivFun.symm ![-5103, 3632, -1063]} * (J0 ^ 7) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7 E151RS1 


noncomputable def E163RS1 : RelationCertificate Table 32 ![![163, 0, 0], ![68, 1, 0]]
  ![-1149, -16, 27] ![![32, 0, 0], ![-15, 1, 0]] where
    su := ![![5216, 0, 0], ![2176, 32, 0]]
    hsu := by decide
    w := ![![-36768, -512, 864], ![24736, 128, -512]]
    hw := by decide
    g := ![![![-406824, 3860280, -1382136], ![311367, 8845700, 0]], ![![1242740784, -11789827396, 4221266116], ![-950966832, -27016103127, 0]]]
    h := ![![![-3875, -169051, -12251], ![-2475, 399388, 0]], ![![2503, 113812, 8248], ![1920, -268888, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R163N1 : Ideal.span {32} * I163N1 =  Ideal.span {B.equivFun.symm ![-1149, -16, 27]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E163RS1 


noncomputable def E167RS1 : RelationCertificate Table 8 ![![167, 0, 0], ![31, 1, 0]]
  ![-31, 0, 1] ![![8, 0, 0], ![1, 1, 0]] where
    su := ![![1336, 0, 0], ![248, 8, 0]]
    hsu := by decide
    w := ![![-248, 0, 8], ![248, 8, 0]]
    hw := by decide
    g := ![![![2344225, 2344224, 6043703], ![586064, -9669925, 0]], ![![435171, 435171, 1121925], ![108793, -1795080, 0]]]
    h := ![![![43369, 731112, 114248], ![12552, -3815883, 0]], ![![-43390, -730870, -114210], ![-12357, 3814614, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R167N1 : Ideal.span {8} * I167N1 =  Ideal.span {B.equivFun.symm ![-31, 0, 1]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E167RS1 


noncomputable def E173RS1 : RelationCertificate Table 128 ![![173, 0, 0], ![69, 1, 0]]
  ![23, -48, 15] ![![128, 0, 0], ![17, 1, 0]] where
    su := ![![22144, 0, 0], ![8832, 128, 0]]
    hsu := by decide
    w := ![![2944, -6144, 1920], ![4480, -256, 0]]
    hw := by decide
    g := ![![![309083593, 2857004917, 793750000], ![63370627, -20319999994, 0]], ![![5989513373, 55363885387, 15381522010], ![1228012673, -393766963453, 0]]]
    h := ![![![791440, 34921897, 2494635], ![517531, -86314368, 0]], ![![1189991, 52507822, 3750880], ![778152, -129780448, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R173N1 : Ideal.span {128} * I173N1 =  Ideal.span {B.equivFun.symm ![23, -48, 15]} * (J0 ^ 7) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7 E173RS1 


noncomputable def E181RS1 : RelationCertificate Table 16 ![![181, 0, 0], ![-84, 1, 0]]
  ![-531, 16, 5] ![![16, 0, 0], ![1, 1, 0]] where
    su := ![![2896, 0, 0], ![-1344, 16, 0]]
    hsu := by decide
    w := ![![-8496, 256, 80], ![896, -304, 80]]
    hw := by decide
    g := ![![![327363, 327511, 825260], ![40936, -2640867, 0]], ![![-132100, -132155, -333000], ![-16515, 1065613, 0]]]
    h := ![![![6817, -382186, 23025], ![-5150, -833504, 0]], ![![-700, 40750, -2455], ![607, 88872, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R181N1 : Ideal.span {16} * I181N1 =  Ideal.span {B.equivFun.symm ![-531, 16, 5]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E181RS1 
