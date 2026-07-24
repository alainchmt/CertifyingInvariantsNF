import IdealArithmetic.Examples.NF3_1_161700_2.PrimesBelow3_1_161700_2F1
import IdealArithmetic.Examples.NF3_1_161700_2.ClassGroupData3_1_161700_2

set_option linter.all false

noncomputable section


noncomputable def E53RS1 : RelationCertificate Table 2 ![![53, 0, 0], ![-15, 1, 0]]
  ![28904728936050, 3542972530932, 2806704344881] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![106, 0, 0], ![-30, 2, 0]]
    hsu := by decide
    w := ![![57809457872100, 7085945061864, 5613408689762], ![218922938900718, 26834292777220, 21257835185592]]
    hw := by decide
    g := ![![![-27293164, 2742197, 160462], ![1371099, 0, 0]], ![![7960632, -1141171, 342633], ![-570584, 0, 0]]]
    h := ![![![820204910929740, -58059875385434, 1545565833485], ![2896130370022678, -13184714138304, 0]], ![![3106095026851968, -219871263621131, 5853018294702], ![10967571663580263, -49930175337735, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {2} * I53N1 =  Ideal.span {B.equivFun.symm ![28904728936050, 3542972530932, 2806704344881]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E53RS1 


noncomputable def E59RS0 : RelationCertificate Table 2 ![![59, 0, 0], ![7, 1, 0]]
  ![817, -75, -30] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![118, 0, 0], ![14, 2, 0]]
    hsu := by decide
    w := ![![1634, -150, -60], ![-2340, 802, -450]]
    hw := by decide
    g := ![![![297677, 29190, 28905], ![14595, 0, 0]], ![![73531, 7210, 7140], ![3606, 0, 0]]]
    h := ![![![928, 130, 0], ![-7705, -5, 0]], ![![-1342, -189, -9], ![11144, 51, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N0 : Ideal.span {2} * I59N0 =  Ideal.span {B.equivFun.symm ![817, -75, -30]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E59RS0 


noncomputable def E59RS1 : RelationCertificate Table 2 ![![59, 0, 0], ![15, 1, 0]]
  ![1163973, 142673, 113024] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![118, 0, 0], ![30, 2, 0]]
    hsu := by decide
    w := ![![2327946, 285346, 226048], ![8815872, 1080598, 856038]]
    hw := by decide
    g := ![![![-3779, -137, 611], ![-67, 0, 0]], ![![-153, -105, 138], ![-52, 0, 0]]]
    h := ![![![141177, 15641, 3838], ![-477698, -18903, 0]], ![![534654, 59283, 14553], ![-1809110, -71768, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {2} * I59N1 =  Ideal.span {B.equivFun.symm ![1163973, 142673, 113024]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E59RS1 


noncomputable def E59RS2 : RelationCertificate Table 2 ![![59, 0, 0], ![-23, 1, 0]]
  ![-18805, -2305, -1826] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![118, 0, 0], ![-46, 2, 0]]
    hsu := by decide
    w := ![![-37610, -4610, -3652], ![-142428, -17458, -13830]]
    hw := by decide
    g := ![![![-417, -26, 79], ![-11, 0, 0]], ![![267, 1, -34], ![2, 0, 0]]]
    h := ![![![-493781, 22131, -226], ![-1265838, 1918, 0]], ![![-1869950, 83763, -843], ![-4793732, 7137, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N2 : Ideal.span {2} * I59N2 =  Ideal.span {B.equivFun.symm ![-18805, -2305, -1826]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E59RS2 


noncomputable def E61RS1 : RelationCertificate Table 2 ![![61, 0, 0], ![26, 1, 0]]
  ![953622042777171, 116889409685379, 92598520358335] ![![2, 0, 0], ![1, 0, 1]] where
    su := ![![122, 0, 0], ![52, 2, 0]]
    hsu := by decide
    w := ![![1907244085554342, 233778819370758, 185197040716670], ![8867215233578378, 1086891354972976, 861023522418836]]
    hw := by decide
    g := ![![![30900786, -15524336, 1486252], ![16193519, -26730, 0]], ![![23637417, -6563205, -2680369], ![10478524, -11421, 0]]]
    h := ![![![16370011459091397, 922719031784118, 66359844427339], ![-38369887575453771, -659225331618224, 0]], ![![76107938193824987, 4289932430211646, 308522138231188], ![-178390408546405193, -3064889778482175, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {2} * I61N1 =  Ideal.span {B.equivFun.symm ![953622042777171, 116889409685379, 92598520358335]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E61RS1 


noncomputable def E67RS1 : RelationCertificate Table 2 ![![67, 0, 0], ![25, 1, 0]]
  ![31813, -4735, 488] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![134, 0, 0], ![50, 2, 0]]
    hsu := by decide
    w := ![![63626, -9470, 976], ![38064, 26102, -28410]]
    hw := by decide
    g := ![![![627091557, 61492170, 60891787], ![30746087, 0, 0]], ![![304878333, 29896161, 29604268], ![14948082, 0, 0]]]
    h := ![![![668039, 34409, 1802], ![-1789072, -20041, 0]], ![![406596, 21071, 855], ![-1088916, -11915, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {2} * I67N1 =  Ideal.span {B.equivFun.symm ![31813, -4735, 488]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E67RS1 


noncomputable def E73RS1 : RelationCertificate Table 2 ![![73, 0, 0], ![-18, 1, 0]]
  ![-53, 7, 0] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![146, 0, 0], ![-36, 2, 0]]
    hsu := by decide
    w := ![![-106, 14, 0], ![0, -46, 42]]
    hw := by decide
    g := ![![![1513, 148, 147], ![75, 0, 0]], ![![-216, -22, -21], ![-9, 0, 0]]]
    h := ![![![-1889, 122, -6], ![-7658, 73, 0]], ![![36, 7, -3], ![146, 40, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {2} * I73N1 =  Ideal.span {B.equivFun.symm ![-53, 7, 0]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E73RS1 
