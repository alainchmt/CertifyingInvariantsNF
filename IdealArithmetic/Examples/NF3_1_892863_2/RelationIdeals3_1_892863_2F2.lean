import IdealArithmetic.Examples.NF3_1_892863_2.PrimesBelow3_1_892863_2F2
import IdealArithmetic.Examples.NF3_1_892863_2.ClassGroupData3_1_892863_2

set_option linter.all false

noncomputable section


noncomputable def E103RS1 : RelationCertificate Table 32 ![![103, 0, 0], ![-22, 1, 0]]
  ![-204386827, -9028407, -6331335] ![![32, 0, 0], ![12, 1, 1]] where
    su := ![![3296, 0, 0], ![-704, 32, 0]]
    hsu := by decide
    w := ![![-6540378464, -288909024, -202602720], ![-4202142816, -185621824, -130170688]]
    hw := by decide
    g := ![![![-566071771, 66373406, -6238933], ![-210397687, 136682640, 0]], ![![115747864, -13571758, 1275696], ![43021206, -27948225, 0]]]
    h := ![![![169697343185, -1904060239396, 362779277755], ![-54732056144, -9341567985025, 0]], ![![109029236697, -1223344046563, 233082893322], ![-35164924693, -6001885520000, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {32} * I103N1 =  Ideal.span {B.equivFun.symm ![-204386827, -9028407, -6331335]} * (J0 ^ 5*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_0 E103RS1 


noncomputable def E109RS1 : RelationCertificate Table 32 ![![109, 0, 0], ![-33, 1, 0]]
  ![7609625, 336141, 235725] ![![32, 0, 0], ![175, 13, 10]] where
    su := ![![3488, 0, 0], ![-1056, 32, 0]]
    hsu := by decide
    w := ![![243508000, 10756512, 7543200], ![2090435456, 92341088, 64755872]]
    hw := by decide
    g := ![![![6471, -19193, -4133], ![26719, -3210, 0]], ![![-1901, 5472, 1171], ![-7607, 915, 0]]]
    h := ![![![-14008834039, 256003546021, -32007997887], ![6589863116, 872218001352, 0]], ![![-120261196458, 2197705576321, -274778051071], ![56571789550, 7487702397590, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {32} * I109N1 =  Ideal.span {B.equivFun.symm ![7609625, 336141, 235725]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E109RS1 


noncomputable def E113RS0 : RelationCertificate Table 2 ![![113, 0, 0], ![-51, 1, 0]]
  ![-185, 9, 37] ![![2, 0, 0], ![18, 1, 1]] where
    su := ![![226, 0, 0], ![-102, 2, 0]]
    hsu := by decide
    w := ![![-370, 18, 74], ![286, 372, -528]]
    hw := by decide
    g := ![![![-64494, 369385, 111745], ![-339763, 46002, 0]], ![![28591, -163082, -49563], ![151107, -20295, 0]]]
    h := ![![![17144, -571746, 45749], ![-12693, -1292400, 0]], ![![-12605, 422738, -33828], ![9542, 955575, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N0 : Ideal.span {2} * I113N0 =  Ideal.span {B.equivFun.symm ![-185, 9, 37]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E113RS0 


noncomputable def E113RS1 : RelationCertificate Table 2 ![![113, 0, 0], ![-48, 1, 0]]
  ![-5898038731, -260534864, -182704823] ![![2, 0, 0], ![18, 2, 1]] where
    su := ![![226, 0, 0], ![-96, 2, 0]]
    hsu := by decide
    w := ![![-11796077462, -521069728, -365409646], ![-184394544180, -8145285184, -5712029726]]
    hw := by decide
    g := ![![![837, 2358, -14425], ![2795, 0, 0]], ![![-1213, 4226, 7329], ![-3016, 3, 0]]]
    h := ![![![-25815052155, 783985639456, -66737479335], ![17903611984, 1885288115008, 0]], ![![-403537090778, 12255147958886, -1043230440063], ![279866622298, 29470545928064, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {2} * I113N1 =  Ideal.span {B.equivFun.symm ![-5898038731, -260534864, -182704823]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E113RS1 


noncomputable def E113RS2 : RelationCertificate Table 32 ![![113, 0, 0], ![-14, 1, 0]]
  ![747, -217, 71] ![![32, 0, 0], ![175, 13, 10]] where
    su := ![![3616, 0, 0], ![-448, 32, 0]]
    hsu := by decide
    w := ![![23904, -6944, 2272], ![-123200, 33824, -9312]]
    hw := by decide
    g := ![![![-93475915, 273127742, 58882702], ![-381836907, 46050988, 0]], ![![9746724, -28479423, -6139798], ![39814754, -4801799, 0]]]
    h := ![![![-4165, 27777, -8549], ![833, 241527, 0]], ![![21476, -142890, 43977], ![-3872, -1242423, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N2 : Ideal.span {32} * I113N2 =  Ideal.span {B.equivFun.symm ![747, -217, 71]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E113RS2 


noncomputable def E137RS0 : RelationCertificate Table 16 ![![137, 0, 0], ![45, 1, 0]]
  ![-265, 67, -13] ![![16, 0, 0], ![12, 1, 1]] where
    su := ![![2192, 0, 0], ![720, 16, 0]]
    hsu := by decide
    w := ![![-4240, 1072, -208], ![6144, -1424, 144]]
    hw := by decide
    g := ![![![7177, -1010, -82], ![5331, -906, 0]], ![![2500, -349, -29], ![1875, -313, 0]]]
    h := ![![![483271, 13031363, 1133323], ![253872, -38816316, 0]], ![![-700089, -18877270, -1641735], ![-367695, 56229426, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N0 : Ideal.span {16} * I137N0 =  Ideal.span {B.equivFun.symm ![-265, 67, -13]} * (J0 ^ 4*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_0 E137RS0 


noncomputable def E137RS1 : RelationCertificate Table 32 ![![137, 0, 0], ![-27, 1, 0]]
  ![41225, 1821, 1277] ![![32, 0, 0], ![175, 13, 10]] where
    su := ![![4384, 0, 0], ![-864, 32, 0]]
    hsu := by decide
    w := ![![1319200, 58272, 40864], ![11324800, 500256, 350816]]
    hw := by decide
    g := ![![![23586, -69011, -14882], ![96477, -11634, 0]], ![![-4747, 13571, 2922], ![-18963, 2289, 0]]]
    h := ![![![2138208, -29417696, 4526525], ![-636039, -155033162, 0]], ![![18355512, -252539047, 38858391], ![-5460854, -1330897151, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {32} * I137N1 =  Ideal.span {B.equivFun.symm ![41225, 1821, 1277]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E137RS1 


noncomputable def E137RS2 : RelationCertificate Table 8 ![![137, 0, 0], ![-18, 1, 0]]
  ![1267718629063, 55999106767, 39270394499] ![![8, 0, 0], ![-33, 1, -2]] where
    su := ![![1096, 0, 0], ![-144, 8, 0]]
    hsu := by decide
    w := ![![10141749032504, 447992854136, 314163155992], ![-45647572149936, -2016396389448, -1414034727544]]
    hw := by decide
    g := ![![![50320, -122191, -95396], ![-198931, 146, 0]], ![![-9041, 28783, 11563], ![38058, -17, 0]]]
    h := ![![![-19167943013753, 167154426756219, -39336491349925], ![3738521175216, 1347284646333556, 0]], ![![86274079439562, -752354818787289, 177051839999801], ![-16826921523228, -6064069708578420, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N2 : Ideal.span {8} * I137N2 =  Ideal.span {B.equivFun.symm ![1267718629063, 55999106767, 39270394499]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E137RS2 
