import IdealArithmetic.Examples.NF3_1_410267_1.PrimesBelow3_1_410267_1F2
import IdealArithmetic.Examples.NF3_1_410267_1.ClassGroupData3_1_410267_1

set_option linter.all false

noncomputable section


noncomputable def E83RS1 : RelationCertificate Table 2097152 ![![83, 0, 0], ![25, 1, 0]]
  ![-245799, -17794, -10987] ![![2097152, 0, 0], ![525283, 1, 0]] where
    su := ![![174063616, 0, 0], ![52428800, 2097152, 0]]
    hsu := by decide
    w := ![![-515477864448, -37316722688, -23041409024], ![-129115357184, -9347006464, -5771362304]]
    hw := by decide
    g := ![![![-527196, -20787799129, -197872], ![1788794, 82993532103, 0]], ![![-180704, -6300886638, -59976], ![625667, 25155757674, 0]]]
    h := ![![![-721864, -10697625, -2058129], ![-346263, 34162744, 0]], ![![-180807, -2679509, -515514], ![-86742, 8556982, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {2097152} * I83N1 =  Ideal.span {B.equivFun.symm ![-245799, -17794, -10987]} * (J0 ^ 21) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_21 E83RS1 


noncomputable def E89RS1 : RelationCertificate Table 2 ![![89, 0, 0], ![-26, 1, 0]]
  ![-5, 0, 1] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![178, 0, 0], ![-52, 2, 0]]
    hsu := by decide
    w := ![![-10, 0, 2], ![112, -18, 0]]
    hw := by decide
    g := ![![![16875, 16794, 63017], ![16835, -25205, 0]], ![![-4750, -4732, -17751], ![-4739, 7100, 0]]]
    h := ![![![-199, 2829, -566], ![94, 10075, 0]], ![![2254, -31764, 6355], ![-988, -113119, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {2} * I89N1 =  Ideal.span {B.equivFun.symm ![-5, 0, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E89RS1 


noncomputable def E103RS1 : RelationCertificate Table 2097152 ![![103, 0, 0], ![-46, 1, 0]]
  ![-27681, 1170, 6851] ![![2097152, 0, 0], ![525283, 1, 0]] where
    su := ![![216006656, 0, 0], ![-96468992, 2097152, 0]]
    hsu := by decide
    w := ![![-58051264512, 2453667840, 14367588352], ![-14539554816, 614465536, 3598712832]]
    hw := by decide
    g := ![![![47226114587025758, 13608614723315820494509, 129535781818259791], ![18318028389040994, -54331244782345431442971, 0]], ![![-20960163247054438, -6039852921536418767349, -57491308716240124], ![-8130011724852041, 24113602611376081705341, 0]]]
    h := ![![![-380665, 11375533, -1264183], ![280571, 26043540, 0]], ![![-95317, 2849122, -316628], ![70327, 6522880, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {2097152} * I103N1 =  Ideal.span {B.equivFun.symm ![-27681, 1170, 6851]} * (J0 ^ 21) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_21 E103RS1 


noncomputable def E107RS1 : RelationCertificate Table 8 ![![107, 0, 0], ![25, 1, 0]]
  ![13, -2, 1] ![![8, 0, 0], ![3, 1, 0]] where
    su := ![![856, 0, 0], ![200, 8, 0]]
    hsu := by decide
    w := ![![104, -16, 8], ![152, -8, -8]]
    hw := by decide
    g := ![![![-260, -645, -834], ![-173, 1335, 0]], ![![-65, -161, -208], ![-42, 333, 0]]]
    h := ![![![-5649, -79422, -15277], ![-1976, 326928, 0]], ![![-8212, -115688, -22253], ![-2949, 476214, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {8} * I107N1 =  Ideal.span {B.equivFun.symm ![13, -2, 1]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E107RS1 


noncomputable def E113RS0 : RelationCertificate Table 262144 ![![113, 0, 0], ![17, 1, 0]]
  ![-35811, -2890, -2359] ![![262144, 0, 0], ![995, 1, 0]] where
    su := ![![29622272, 0, 0], ![4456448, 262144, 0]]
    hsu := by decide
    w := ![![-9387638784, -757596160, -618397696], ![-35913728, -2883584, -2359296]]
    hw := by decide
    g := ![![![-9885478, -4922846333, -24713084], ![64391, 1295677338407, 0]], ![![-1523722, -758608978, -3808278], ![108230, 199663445603, 0]]]
    h := ![![![438813, 4089670, 1136257], ![102240, -25679880, 0]], ![![1663, 15645, 4347], ![496, -98244, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N0 : Ideal.span {262144} * I113N0 =  Ideal.span {B.equivFun.symm ![-35811, -2890, -2359]} * (J0 ^ 18) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_18 E113RS0 


noncomputable def E113RS1 : RelationCertificate Table 4 ![![113, 0, 0], ![26, 1, 0]]
  ![25, 2, 1] ![![4, 0, 0], ![-1, 1, 0]] where
    su := ![![452, 0, 0], ![104, 4, 0]]
    hsu := by decide
    w := ![![100, 8, 4], ![96, 12, 8]]
    hw := by decide
    g := ![![![328531, 19324, 869619], ![-77301, -695695, 0]], ![![78507, 4617, 207805], ![-18469, -166244, 0]]]
    h := ![![![1291, 19095, 3537], ![539, -79936, 0]], ![![1240, 18323, 3394], ![512, -76704, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {4} * I113N1 =  Ideal.span {B.equivFun.symm ![25, 2, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E113RS1 


noncomputable def E113RS2 : RelationCertificate Table 32 ![![113, 0, 0], ![-43, 1, 0]]
  ![-23, -2, 5] ![![32, 0, 0], ![3, 1, 0]] where
    su := ![![3616, 0, 0], ![-1376, 32, 0]]
    hsu := by decide
    w := ![![-736, -64, 160], ![512, -96, 0]]
    hw := by decide
    g := ![![![19136052, 38741607, 48544380], ![3004697, -310684035, 0]], ![![-7062879, -14299044, -17917125], ![-1108990, 114669601, 0]]]
    h := ![![![24748, -639359, 76130], ![-14989, -1720537, 0]], ![![-17421, 450608, -53655], ![10619, 1212603, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N2 : Ideal.span {32} * I113N2 =  Ideal.span {B.equivFun.symm ![-23, -2, 5]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E113RS2 


noncomputable def E131RS0 : RelationCertificate Table 16 ![![131, 0, 0], ![41, 1, 0]]
  ![33, -2, -3] ![![16, 0, 0], ![3, 1, 0]] where
    su := ![![2096, 0, 0], ![656, 16, 0]]
    hsu := by decide
    w := ![![528, -32, -48], ![-256, 64, -16]]
    hw := by decide
    g := ![![![-7683, -16164, -20396], ![-2437, 65270, 0]], ![![-2375, -4997, -6305], ![-749, 20177, 0]]]
    h := ![![![14560, 353895, 42137], ![7333, -1103990, 0]], ![![-7190, -173610, -20671], ![-3446, 541580, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N0 : Ideal.span {16} * I131N0 =  Ideal.span {B.equivFun.symm ![33, -2, -3]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E131RS0 


noncomputable def E131RS1 : RelationCertificate Table 8388608 ![![131, 0, 0], ![-40, 1, 0]]
  ![-255563, 47622, -767] ![![8388608, 0, 0], ![525283, 1, 0]] where
    su := ![![1098907648, 0, 0], ![-335544320, 8388608, 0]]
    hsu := by decide
    w := ![![-2143817826304, 399482290176, -6434062336], ![-134242893824, 25014829056, -402653184]]
    hw := by decide
    g := ![![![2083397398224614293626, 550412342340001226985961410, 5239188156692613907856], ![196073720201454391091, -8789899136947382913670420622, 0]], ![![-637287926529382157766, -168364969969220694777446448, -1602608969331141292746], ![-59976754651110344882, 2688731684200593299491887443, 0]]]
    h := ![![![135472241906747, -3025007835063303, 387884599360193], ![-64457232910875, -10162576503237210, 0]], ![![8483083229347, -189421780233849, 24288793729542], ![-4036222209189, -636366395714010, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {8388608} * I131N1 =  Ideal.span {B.equivFun.symm ![-255563, 47622, -767]} * (J0 ^ 23) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_23 E131RS1 


noncomputable def E131RS2 : RelationCertificate Table 8388608 ![![131, 0, 0], ![-1, 1, 0]]
  ![135583, 15634, -1661] ![![8388608, 0, 0], ![525283, 1, 0]] where
    su := ![![1098907648, 0, 0], ![-8388608, 8388608, 0]]
    hsu := by decide
    w := ![![1137352638464, 131147497472, -13933477888], ![71219281920, 8212447232, -872415232]]
    hw := by decide
    g := ![![![238394656, 63096435518123, 600593541], ![29428317, -1007628756556149, 0]], ![![299549, 152864787862, 1455068], ![4511090, -2441199013071, 0]]]
    h := ![![![295432159211041, 17214320082, 738623433824909], ![-2255075915108, -19351933966212948, 0]], ![![18499509376144, 1077934361, 46251468276081], ![-141209400312, -1211788468833343, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N2 : Ideal.span {8388608} * I131N2 =  Ideal.span {B.equivFun.symm ![135583, 15634, -1661]} * (J0 ^ 23) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_23 E131RS2 


noncomputable def E137RS1 : RelationCertificate Table 32 ![![137, 0, 0], ![18, 1, 0]]
  ![115, 10, 7] ![![32, 0, 0], ![3, 1, 0]] where
    su := ![![4384, 0, 0], ![576, 32, 0]]
    hsu := by decide
    w := ![![3680, 320, 224], ![1184, 64, 64]]
    hw := by decide
    g := ![![![41801, 84633, 106048], ![6575, -678706, 0]], ![![5340, 10812, 13548], ![844, -86707, 0]]]
    h := ![![![699099, 6817158, 1794261], ![141614, -49162750, 0]], ![![225001, 2194076, 577476], ![45588, -15822842, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {32} * I137N1 =  Ideal.span {B.equivFun.symm ![115, 10, 7]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E137RS1 
