import IdealArithmetic.Examples.NF3_1_648324_3.PrimesBelow3_1_648324_3F2
import IdealArithmetic.Examples.NF3_1_648324_3.ClassGroupData3_1_648324_3

set_option linter.all false

noncomputable section


noncomputable def E83RS1 : RelationCertificate Table 2 ![![83, 0, 0], ![14, 1, 0]]
  ![-10150, -2615, -353] ![![2, 0, 0], ![-53, -3, 1]] where
    su := ![![166, 0, 0], ![28, 2, 0]]
    hsu := by decide
    w := ![![-20300, -5230, -706], ![-124906, -32180, -4344]]
    hw := by decide
    g := ![![![56, -38, 16], ![-203, 0, 0]], ![![1, 0, 1], ![-18, 0, 0]]]
    h := ![![![-10178, -783, -9], ![59616, 197, 0]], ![![-62483, -4728, -44], ![365974, 740, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {2} * I83N1 =  Ideal.span {B.equivFun.symm ![-10150, -2615, -353]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E83RS1 


noncomputable def E101RS0 : RelationCertificate Table 2 ![![101, 0, 0], ![47, 1, 0]]
  ![-646370, -38815, 11129] ![![2, 0, 0], ![-53, -3, 1]] where
    su := ![![202, 0, 0], ![94, 2, 0]]
    hsu := by decide
    w := ![![-1292740, -77630, 22258], ![3499558, 518420, -101868]]
    hw := by decide
    g := ![![![-22315816, 502881050, 134954610], ![-95474961, 0, 0]], ![![-13658060, 307781865, 82597228], ![-58434217, 0, 0]]]
    h := ![![![-8731610, -234935, -1971], ![18749920, 105100, 0]], ![![23660326, 637686, 5116], ![-50807301, -283825, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N0 : Ideal.span {2} * I101N0 =  Ideal.span {B.equivFun.symm ![-646370, -38815, 11129]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E101RS0 


noncomputable def E101RS1 : RelationCertificate Table 2 ![![101, 0, 0], ![-28, 1, 0]]
  ![-14872956680, -3831817917, -517262848] ![![2, 0, 0], ![-53, -4, 1]] where
    su := ![![202, 0, 0], ![-56, 2, 0]]
    hsu := by decide
    w := ![![-29745913360, -7663635834, -1034525696], ![37328164390, 9617101172, 1298226912]]
    hw := by decide
    g := ![![![-104082, 399896, -112192], ![1902967, 0, -64480]], ![![27250, -96790, 29205], ![-512902, 0, 17732]]]
    h := ![![![-827408315872, 31442867765, -143390610], ![-2984048819514, 6982594381, 0]], ![![1038315188359, -39457673458, 179940960], ![3744684640788, -8762461752, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {2} * I101N1 =  Ideal.span {B.equivFun.symm ![-14872956680, -3831817917, -517262848]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E101RS1 


noncomputable def E107RS1 : RelationCertificate Table 2 ![![107, 0, 0], ![46, 1, 0]]
  ![-80, -2, 1] ![![2, 0, 0], ![-53, -3, 1]] where
    su := ![![214, 0, 0], ![92, 2, 0]]
    hsu := by decide
    w := ![![-160, -4, 2], ![2110, 154, -40]]
    hw := by decide
    g := ![![![23, 22, 5], ![-3, 0, 0]], ![![5, 12, 3], ![-2, 0, 0]]]
    h := ![![![-312, -30, -1], ![724, 54, 0]], ![![2999, 70, 0], ![-6953, -10, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {2} * I107N1 =  Ideal.span {B.equivFun.symm ![-80, -2, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E107RS1 


noncomputable def E109RS1 : RelationCertificate Table 2 ![![109, 0, 0], ![51, 1, 0]]
  ![184768, 47603, 6426] ![![2, 0, 0], ![-53, -4, 1]] where
    su := ![![218, 0, 0], ![102, 2, 0]]
    hsu := by decide
    w := ![![369536, 95206, 12852], ![-463730, -119474, -16128]]
    hw := by decide
    g := ![![![132374, -601977, 141873], ![-2232299, 0, 69600]], ![![62882, -285988, 67396], ![-1060363, 0, 33060]]]
    h := ![![![8355934, 216190, 2096], ![-17855138, -111019, 0]], ![![-10485916, -271342, -2632], ![22406529, 139412, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {2} * I109N1 =  Ideal.span {B.equivFun.symm ![184768, 47603, 6426]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E109RS1 


noncomputable def E113RS1 : RelationCertificate Table 2 ![![113, 0, 0], ![19, 1, 0]]
  ![-5771944, -1487064, -200741] ![![2, 0, 0], ![-53, -3, 1]] where
    su := ![![226, 0, 0], ![38, 2, 0]]
    hsu := by decide
    w := ![![-11543888, -2974128, -401482], ![-71029234, -18299730, -2470308]]
    hw := by decide
    g := ![![![-120, -1839, -90], ![6053, 0, 0]], ![![6, -250, 0], ![601, 0, 0]]]
    h := ![![![-5774508, -322454, -2625], ![34039340, 47942, 0]], ![![-35530297, -1984031, -16150], ![209442576, 294898, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {2} * I113N1 =  Ideal.span {B.equivFun.symm ![-5771944, -1487064, -200741]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E113RS1 


noncomputable def E131RS1 : RelationCertificate Table 2 ![![131, 0, 0], ![3, 1, 0]]
  ![10771474, 460209, -160267] ![![2, 0, 0], ![-53, -3, 1]] where
    su := ![![262, 0, 0], ![6, 2, 0]]
    hsu := by decide
    w := ![![21542948, 920418, -320534], ![-170017862, -14620560, 3522744]]
    hw := by decide
    g := ![![![-8874689557, 199988735181, 53669554277], ![-37969052043, 0, 0]], ![![-1206940661, 27198082768, 7298956003], ![-5163717941, 0, 0]]]
    h := ![![![10769120, 3567705, 39], ![-466661082, -82688, 0]], ![![-84991685, -28184997, 3486], ![3682967268, 652353, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {2} * I131N1 =  Ideal.span {B.equivFun.symm ![10771474, 460209, -160267]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E131RS1 


noncomputable def E137RS1 : RelationCertificate Table 2 ![![137, 0, 0], ![64, 1, 0]]
  ![-3309404312, -220664884, 59941033] ![![2, 0, 0], ![-53, -3, 1]] where
    su := ![![274, 0, 0], ![128, 2, 0]]
    hsu := by decide
    w := ![![-6618808624, -441329768, 119882066], ![4790547778, 1951365194, -307066084]]
    hw := by decide
    g := ![![![-604861699656834, 13630395218650205, 3657892207518456], ![-2587811683309913, 0, 0]], ![![-347975380249535, 7841531315096882, 2104375979741055], ![-1488761406161028, 0, 0]]]
    h := ![![![-21266930904, -398141360, -1581609], ![45472814524, 138310733, 0]], ![![15424509337, 293559174, 307528], ![-32980664145, -97832189, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {2} * I137N1 =  Ideal.span {B.equivFun.symm ![-3309404312, -220664884, 59941033]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E137RS1 
