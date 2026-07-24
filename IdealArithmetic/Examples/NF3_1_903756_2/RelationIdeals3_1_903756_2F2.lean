import IdealArithmetic.Examples.NF3_1_903756_2.PrimesBelow3_1_903756_2F2
import IdealArithmetic.Examples.NF3_1_903756_2.ClassGroupData3_1_903756_2

set_option linter.all false

noncomputable section


noncomputable def E101RS1 : RelationCertificate Table 3 ![![101, 0, 0], ![-21, 1, 0]]
  ![-2349976, -196008, -184393] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![303, 0, 0], ![-63, 3, 0]]
    hsu := by decide
    w := ![![-7049928, -588024, -553179], ![-34527951, -2879925, -2709267]]
    hw := by decide
    g := ![![![-2744, -445, 187], ![-147, 82, 0]], ![![1431, 101, -88], ![34, -16, 0]]]
    h := ![![![-59057315, 358207703, -171394421], ![15825893, 1573695648, 0]], ![![-289241006, 1754369410, -839426753], ![77509267, 7707381724, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {3} * I101N1 =  Ideal.span {B.equivFun.symm ![-2349976, -196008, -184393]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E101RS1 


noncomputable def E103RS1 : RelationCertificate Table 9 ![![103, 0, 0], ![-10, 1, 0]]
  ![-14, 819, -548] ![![9, 0, 0], ![-3, 1, 0]] where
    su := ![![927, 0, 0], ![-90, 9, 0]]
    hsu := by decide
    w := ![![-126, 7371, -4932], ![-96966, -6849, 9009]]
    hw := by decide
    g := ![![![-515246, -66248, -43855], ![164389, -736, 0]], ![![-23513, -2965, -2121], ![7512, 67, 0]]]
    h := ![![![-1606, 4901, -4493], ![268, 42021, 0]], ![![-683896, 2075762, -1903550], ![86645, 17824241, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {9} * I103N1 =  Ideal.span {B.equivFun.symm ![-14, 819, -548]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E103RS1 


noncomputable def E107RS1 : RelationCertificate Table 9 ![![107, 0, 0], ![-30, 1, 0]]
  ![-304868488, 19083339, 1116062] ![![9, 0, 0], ![-3, 1, 0]] where
    su := ![![963, 0, 0], ![-270, 9, 0]]
    hsu := by decide
    w := ![![-2743816392, 171750051, 10044558], ![1195178166, -394704873, 209916729]]
    hw := by decide
    g := ![![![-632325754093617, -80774233053301, -54894160009745], ![201800336580842, -2529888, 0]], ![![1058236798006314, -1342715680587997, 3102887872392684], ![-501936230511873, -2532301261436834, 0]]]
    h := ![![![-808185438094, 7120227592550, -2448519904014], ![293138231209, 23817420985960, 0]], ![![353185442082, -3111613884779, 1070028900523], ![-128104459304, -10408460821080, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {9} * I107N1 =  Ideal.span {B.equivFun.symm ![-304868488, 19083339, 1116062]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E107RS1 


noncomputable def E109RS1 : RelationCertificate Table 3 ![![109, 0, 0], ![31, 1, 0]]
  ![436734321056, 36427359705, 34268754860] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![327, 0, 0], ![93, 3, 0]]
    hsu := by decide
    w := ![![1310202963168, 109282079115, 102806264580], ![6416891578200, 535223375946, 503507221335]]
    hw := by decide
    g := ![![![1983939, -227306, 78735], ![-75767, 0, 0]], ![![687170, -40849, -899], ![-13616, -8, 0]]]
    h := ![![![65238307196743, 520844661147674, 197643150353672], ![23332405360171, -1958460829072308, 0]], ![![319513201996382, 2550905328123880, 967983360323673], ![114273528348830, -9591819858139992, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {3} * I109N1 =  Ideal.span {B.equivFun.symm ![436734321056, 36427359705, 34268754860]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E109RS1 


noncomputable def E137RS1 : RelationCertificate Table 3 ![![137, 0, 0], ![18, 1, 0]]
  ![1635514, 125904, -158909] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![411, 0, 0], ![54, 3, 0]]
    hsu := by decide
    w := ![![4906542, 377712, -476727], ![-28576731, 589161, 908217]]
    hw := by decide
    g := ![![![294496106614, 22107133773, 23107904133], ![7369044591, 40, 0]], ![![70276863719, 5275519751, 5514337863], ![1758506584, 8, 0]]]
    h := ![![![1656057422, 6762526986, 4650575111], ![266945718, -57920813556, 0]], ![![-9654742207, -39425229396, -27112653793], ![-1556281641, 337675806580, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {3} * I137N1 =  Ideal.span {B.equivFun.symm ![1635514, 125904, -158909]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E137RS1 
