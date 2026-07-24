import IdealArithmetic.Examples.NF3_1_797796_1.PrimesBelow3_1_797796_1F4
import IdealArithmetic.Examples.NF3_1_797796_1.ClassGroupData3_1_797796_1

set_option linter.all false

noncomputable section


noncomputable def E199RS1 : RelationCertificate Table 4 ![![199, 0, 0], ![-86, 1, 0]]
  ![2654, 187, -38] ![![4, 0, 0], ![-79, -3, 1]] where
    su := ![![796, 0, 0], ![-344, 4, 0]]
    hsu := by decide
    w := ![![10616, 748, -152], ![4044, -1008, 88]]
    hw := by decide
    g := ![![![40585, -401930, -52851], ![-513171, 0, 19092]], ![![-13480, 133962, 17613], ![171064, 0, -6364]]]
    h := ![![![133118, -1641, 2], ![307998, -218, 0]], ![![50787, -587, 0], ![117507, 11, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R199N1 : Ideal.span {4} * I199N1 =  Ideal.span {B.equivFun.symm ![2654, 187, -38]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E199RS1 


noncomputable def E211RS1 : RelationCertificate Table 8 ![![211, 0, 0], ![77, 1, 0]]
  ![4834, 897, -132] ![![8, 0, 0], ![-75, -5, 1]] where
    su := ![![1688, 0, 0], ![616, 8, 0]]
    hsu := by decide
    w := ![![38672, 7176, -1056], ![742920, 43864, -9680]]
    hw := by decide
    g := ![![![-338876, 114412, -20471], ![3103117, 0, -67500]], ![![-135502, 49719, -7210], ![1238525, 0, -27000]]]
    h := ![![![101098, 1495, 4], ![-276972, -488, 0]], ![![1942013, 29004, 92], ![-5320414, -10311, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R211N1 : Ideal.span {8} * I211N1 =  Ideal.span {B.equivFun.symm ![4834, 897, -132]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E211RS1 


noncomputable def E229RS1 : RelationCertificate Table 4 ![![229, 0, 0], ![104, 1, 0]]
  ![-356614, -78887, -8902] ![![4, 0, 0], ![-79, -3, 1]] where
    su := ![![916, 0, 0], ![416, 4, 0]]
    hsu := by decide
    w := ![![-1426456, -315548, -35608], ![-8876004, -1963472, -221568]]
    hw := by decide
    g := ![![![841441, -8360071, -1102059], ![-10622633, 0, 395496]], ![![389554, -3870450, -510211], ![-4917790, 0, 183100]]]
    h := ![![![-41614862, -641395, -4672], ![91629296, 530493, 0]], ![![-258944061, -3990959, -29070], ![570153567, 3300819, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R229N1 : Ideal.span {4} * I229N1 =  Ideal.span {B.equivFun.symm ![-356614, -78887, -8902]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E229RS1 


noncomputable def E233RS1 : RelationCertificate Table 16 ![![233, 0, 0], ![-33, 1, 0]]
  ![-446, -98, -11] ![![16, 0, 0], ![-83, -1, 1]] where
    su := ![![3728, 0, 0], ![-528, 16, 0]]
    hsu := by decide
    w := ![![-7136, -1568, -176], ![-24752, -5504, -624]]
    hw := by decide
    g := ![![![86, 41, -3], ![-97, 0, 0]], ![![29, -7, 0], ![27, 0, 0]]]
    h := ![![![-8110, 261, -1], ![-57248, 111, 0]], ![![-28246, 901, -3], ![-199387, 330, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R233N1 : Ideal.span {16} * I233N1 =  Ideal.span {B.equivFun.symm ![-446, -98, -11]} * (J0 ^ 8) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8 E233RS1 


noncomputable def E233RS2 : RelationCertificate Table 2 ![![233, 0, 0], ![-28, 1, 0]]
  ![47244, 2421, -574] ![![2, 0, 0], ![-77, -4, 1]] where
    su := ![![466, 0, 0], ![-56, 2, 0]]
    hsu := by decide
    w := ![![94488, 4842, -1148], ![-288718, -27274, 4916]]
    hw := by decide
    g := ![![![274124, -2859568, -329215], ![-4999013, 0, 137788]], ![![-28202, 277553, 28473], ![545330, 0, -14896]]]
    h := ![![![172148, -6193, 2], ![1430830, -520, 0]], ![![-525979, 18936, -6], ![-4371741, 1928, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R233N2 : Ideal.span {2} * I233N2 =  Ideal.span {B.equivFun.symm ![47244, 2421, -574]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E233RS2 


noncomputable def E239RS0 : RelationCertificate Table 16 ![![239, 0, 0], ![50, 1, 0]]
  ![7485886, 1655962, 186867] ![![16, 0, 0], ![-83, -1, 1]] where
    su := ![![3824, 0, 0], ![800, 16, 0]]
    hsu := by decide
    w := ![![119774176, 26495392, 2989872], ![421728912, 93291168, 10527440]]
    hw := by decide
    g := ![![![3747, 6114, -278], ![-19439, 0, 0]], ![![679, 1038, -49], ![-3232, 0, 0]]]
    h := ![![![3977016074, 84511802, 199389], ![-19009987116, -23733552, 0]], ![![14003207713, 297568995, 702059], ![-66934805707, -83567068, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R239N0 : Ideal.span {16} * I239N0 =  Ideal.span {B.equivFun.symm ![7485886, 1655962, 186867]} * (J0 ^ 8) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8 E239RS0 


noncomputable def E239RS2 : RelationCertificate Table 2 ![![239, 0, 0], ![-107, 1, 0]]
  ![-13363124, -2956073, -333578] ![![2, 0, 0], ![-77, -4, 1]] where
    su := ![![478, 0, 0], ![-214, 2, 0]]
    hsu := by decide
    w := ![![-26726248, -5912146, -667156], ![-122489762, -27096110, -3057660]]
    hw := by decide
    g := ![![![181595, -1709160, -156990], ![-3649399, 0, 99320]], ![![-80230, 756110, 69434], ![1613747, 0, -43930]]]
    h := ![![![-2971353222, 31595619, -73150], ![-6636822962, 8574636, 0]], ![![-13618086448, 144806402, -335250], ![-30417396413, 39297960, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R239N2 : Ideal.span {2} * I239N2 =  Ideal.span {B.equivFun.symm ![-13363124, -2956073, -333578]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E239RS2 


noncomputable def E241RS1 : RelationCertificate Table 8 ![![241, 0, 0], ![-96, 1, 0]]
  ![-158, -9, 2] ![![8, 0, 0], ![-75, -5, 1]] where
    su := ![![1928, 0, 0], ![-768, 8, 0]]
    hsu := by decide
    w := ![![-1264, -72, 16], ![-1640, -48, 16]]
    hw := by decide
    g := ![![![2095403, -207258, 249621], ![-19483253, 0, 416340]], ![![-814793, 80606, -97076], ![7576830, 0, -161910]]]
    h := ![![![-9854, 199, -2], ![-24736, 242, 0]], ![![-12829, 230, -2], ![-32204, 242, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R241N1 : Ideal.span {8} * I241N1 =  Ideal.span {B.equivFun.symm ![-158, -9, 2]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E241RS1 


noncomputable def E251RS1 : RelationCertificate Table 16 ![![251, 0, 0], ![-83, 1, 0]]
  ![866, -40, -1] ![![16, 0, 0], ![-83, -1, 1]] where
    su := ![![4016, 0, 0], ![-1328, 16, 0]]
    hsu := by decide
    w := ![![13856, -640, -16], ![-99568, -2464, 912]]
    hw := by decide
    g := ![![![410, 2073, 361], ![-1827, 0, 0]], ![![-14, -538, -95], ![493, 0, 0]]]
    h := ![![![46332, -600, 1], ![140102, -126, 0]], ![![-331999, 4382, -9], ![-1003922, 1158, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R251N1 : Ideal.span {16} * I251N1 =  Ideal.span {B.equivFun.symm ![866, -40, -1]} * (J0 ^ 8) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8 E251RS1 
