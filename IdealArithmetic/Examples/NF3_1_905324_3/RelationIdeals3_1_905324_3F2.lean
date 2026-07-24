import IdealArithmetic.Examples.NF3_1_905324_3.PrimesBelow3_1_905324_3F2
import IdealArithmetic.Examples.NF3_1_905324_3.ClassGroupData3_1_905324_3

set_option linter.all false

noncomputable section


noncomputable def E83RS0 : RelationCertificate Table 169 ![![83, 0, 0], ![-36, 1, 0]]
  ![437, -65, -5] ![![169, 0, 0], ![-13, 1, 0]] where
    su := ![![14027, 0, 0], ![-6084, 169, 0]]
    hsu := by decide
    w := ![![73853, -10985, -845], ![-6591, 1352, 0]]
    hw := by decide
    g := ![![![25, 24755, -1904], ![208, 321816, 0]], ![![2, -10662, 820], ![70, -138595, 0]]]
    h := ![![![8359, -235, 0], ![19260, -5, 0]], ![![-717, 56, -1], ![-1652, 83, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N0 : Ideal.span {169} * I83N0 =  Ideal.span {B.equivFun.symm ![437, -65, -5]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E83RS0 


noncomputable def E83RS1 : RelationCertificate Table 169 ![![83, 0, 0], ![-32, 1, 0]]
  ![-141, 26, 2] ![![169, 0, 0], ![-13, 1, 0]] where
    su := ![![14027, 0, 0], ![-5408, 169, 0]]
    hsu := by decide
    w := ![![-23829, 4394, 338], ![2197, -507, 0]]
    hw := by decide
    g := ![![![-40837, -90257405, 6943119], ![-530894, -1173387105, 0]], ![![13621, 30085801, -2314373], ![177077, 391129035, 0]]]
    h := ![![![-1087, 67, -1], ![-2815, 85, 0]], ![![127, -4, 0], ![329, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {169} * I83N1 =  Ideal.span {B.equivFun.symm ![-141, 26, 2]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E83RS1 


noncomputable def E83RS2 : RelationCertificate Table 169 ![![83, 0, 0], ![-15, 1, 0]]
  ![-83, 104, -18] ![![169, 0, 0], ![-13, 1, 0]] where
    su := ![![14027, 0, 0], ![-2535, 169, 0]]
    hsu := by decide
    w := ![![-14027, 17576, -3042], ![-2197, -1183, 338]]
    hw := by decide
    g := ![![![-798097, -1763764773, 135678935], ![-10375024, -22929740097, 0]], ![![140182, 309793895, -23831129], ![1822337, 4027460811, 0]]]
    h := ![![![-221101, 15188, -30], ![-1223420, 2472, 0]], ![![-34361, 2366, -5], ![-190130, 417, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N2 : Ideal.span {169} * I83N2 =  Ideal.span {B.equivFun.symm ![-83, 104, -18]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E83RS2 


noncomputable def E89RS0 : RelationCertificate Table 48841 ![![89, 0, 0], ![7, 1, 0]]
  ![2279, -1638, 199] ![![48841, 0, 0], ![13507, 1, 0]] where
    su := ![![4346849, 0, 0], ![341887, 48841, 0]]
    hsu := by decide
    w := ![![111308639, -80001558, 9719359], ![30818671, -22124973, 2686255]]
    hw := by decide
    g := ![![![-909606503629, 172929773031925692, 12802974242931], ![3289116106000, -625310064998993028, 0]], ![![-79951349396, 15199945005151556, 1125338343901], ![289102232609, -54962650054468748, 0]]]
    h := ![![![708377640, 101881018, 97750], ![-9006515383, -8699551, 0]], ![![196132954, 28208431, 27064], ![-2493690325, -2408641, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N0 : Ideal.span {48841} * I89N0 =  Ideal.span {B.equivFun.symm ![2279, -1638, 199]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E89RS0 


noncomputable def E89RS1 : RelationCertificate Table 3757 ![![89, 0, 0], ![37, 1, 0]]
  ![19241, 2483, 508] ![![3757, 0, 0], ![-1521, 1, 0]] where
    su := ![![334373, 0, 0], ![139009, 3757, 0]]
    hsu := by decide
    w := ![![72288437, 9328631, 1908556], ![-29173105, -3764514, -770185]]
    hw := by decide
    g := ![![![7398103462, 79907721160010, -52536309023], ![18273947867, 197378912999412, 0]], ![![3247803726, 35079875602141, -23063693450], ![8022352793, 86650296291648, 0]]]
    h := ![![![1037056762, 38679673, 287873], ![-2494541421, -25620189, 0]], ![![-418520110, -15609790, -116176], ![1006710325, 10339459, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {3757} * I89N1 =  Ideal.span {B.equivFun.symm ![19241, 2483, 508]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E89RS1 


noncomputable def E89RS2 : RelationCertificate Table 289 ![![89, 0, 0], ![-44, 1, 0]]
  ![-369, -30, -8] ![![289, 0, 0], ![-76, 1, 0]] where
    su := ![![25721, 0, 0], ![-12716, 289, 0]]
    hsu := by decide
    w := ![![-106641, -8670, -2312], ![26588, 2023, 578]]
    hw := by decide
    g := ![![![-453, -594921, 7828], ![-1721, -2262288, 0]], ![![264, 293204, -3858], ![1003, 1114960, 0]]]
    h := ![![![-4772125, 129441, -477], ![-9652699, 42445, 0]], ![![1189940, -32235, 118], ![2406922, -10500, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N2 : Ideal.span {289} * I89N2 =  Ideal.span {B.equivFun.symm ![-369, -30, -8]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E89RS2 


noncomputable def E97RS1 : RelationCertificate Table 13 ![![97, 0, 0], ![47, 1, 0]]
  ![-15, 13, -2] ![![13, 0, 0], ![0, 1, 0]] where
    su := ![![1261, 0, 0], ![611, 13, 0]]
    hsu := by decide
    w := ![![-195, 169, -26], ![-364, 13, 13]]
    hw := by decide
    g := ![![![43, 5, 706075], ![6, -9178960, 0]], ![![23, 2, 349255], ![12, -4540307, 0]]]
    h := ![![![-4329, -138, -1], ![8934, 95, 0]], ![![-8062, -266, -2], ![16638, 195, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {13} * I97N1 =  Ideal.span {B.equivFun.symm ![-15, 13, -2]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E97RS1 


noncomputable def E101RS1 : RelationCertificate Table 2873 ![![101, 0, 0], ![24, 1, 0]]
  ![-565, -78, 20] ![![2873, 0, 0], ![-858, 1, 0]] where
    su := ![![290173, 0, 0], ![68952, 2873, 0]]
    hsu := by decide
    w := ![![-1623245, -224094, 57460], ![488410, 66079, -17238]]
    hw := by decide
    g := ![![![2237, 22617733, -26361], ![7491, 75735145, 0]], ![![1202, 5597590, -6524], ![4025, 18743450, 0]]]
    h := ![![![-25100081, -1132602, -3615], ![105629484, 365135, 0]], ![![7552066, 340759, 1087], ![-31781604, -109793, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {2873} * I101N1 =  Ideal.span {B.equivFun.symm ![-565, -78, 20]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E101RS1 


noncomputable def E103RS0 : RelationCertificate Table 48841 ![![103, 0, 0], ![48, 1, 0]]
  ![18313, -1911, -394] ![![48841, 0, 0], ![13507, 1, 0]] where
    su := ![![5030623, 0, 0], ![2344368, 48841, 0]]
    hsu := by decide
    w := ![![894425233, -93335151, -19243354], ![247281983, -25788048, -5323669]]
    hw := by decide
    g := ![![![2533, -2061789448, -152646], ![-9160, 7455383019, 0]], ![![1704, -1016374698, -75248], ![-6162, 3675187431, 0]]]
    h := ![![![14813805967, 468195775, 3324472], ![-31787958256, -342421010, 0]], ![![4095582689, 129442300, 919117], ![-8788437748, -94669160, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N0 : Ideal.span {48841} * I103N0 =  Ideal.span {B.equivFun.symm ![18313, -1911, -394]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E103RS0 


noncomputable def E103RS1 : RelationCertificate Table 3757 ![![103, 0, 0], ![-27, 1, 0]]
  ![4269, 481, 109] ![![3757, 0, 0], ![-1521, 1, 0]] where
    su := ![![386971, 0, 0], ![-101439, 3757, 0]]
    hsu := by decide
    w := ![![16038633, 1807117, 409513], ![-6473311, -728858, -165308]]
    hw := by decide
    g := ![![![17432515195, 188290523555877, -123793908624], ![43059802490, 465093714700350, 0]], ![![-4535270613, -48985965846064, 32206422635], ![-11202506044, -120999529839690, 0]]]
    h := ![![![60717, -2349, 5], ![231466, -406, 0]], ![![-24463, 973, -3], ![-93258, 265, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {3757} * I103N1 =  Ideal.span {B.equivFun.symm ![4269, 481, 109]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E103RS1 


noncomputable def E103RS2 : RelationCertificate Table 289 ![![103, 0, 0], ![-21, 1, 0]]
  ![7481, 963, 199] ![![289, 0, 0], ![-76, 1, 0]] where
    su := ![![29767, 0, 0], ![-6069, 289, 0]]
    hsu := by decide
    w := ![![2162009, 278307, 57511], ![-532338, -68493, -14161]]
    hw := by decide
    g := ![![![133, 86632, -1140], ![499, 329436, 0]], ![![25, -16795, 221], ![97, -63864, 0]]]
    h := ![![![53746589, -2645471, 4103], ![263613866, -422410, 0]], ![![-13233678, 651393, -1011], ![-64907952, 104084, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N2 : Ideal.span {289} * I103N2 =  Ideal.span {B.equivFun.symm ![7481, 963, 199]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E103RS2 


noncomputable def E107RS0 : RelationCertificate Table 48841 ![![107, 0, 0], ![21, 1, 0]]
  ![-5455, -1287, -112] ![![48841, 0, 0], ![13507, 1, 0]] where
    su := ![![5225987, 0, 0], ![1025661, 48841, 0]]
    hsu := by decide
    w := ![![-266427655, -62858367, -5470192], ![-73701069, -17387396, -1514071]]
    hw := by decide
    g := ![![![376766433765, -71628923533765647, -5303096436045], ![-1362378721516, 259008533032873820, 0]], ![![82043515596, -15597699181828319, -1154786346924], ![-296667457261, 56400919970115080, 0]]]
    h := ![![![-44864, -2250, -6], ![228333, 530, 0]], ![![-12420, -630, -2], ![63211, 183, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N0 : Ideal.span {48841} * I107N0 =  Ideal.span {B.equivFun.symm ![-5455, -1287, -112]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E107RS0 


noncomputable def E107RS1 : RelationCertificate Table 48841 ![![107, 0, 0], ![25, 1, 0]]
  ![-435, -416, -188] ![![48841, 0, 0], ![13507, 1, 0]] where
    su := ![![5225987, 0, 0], ![1221025, 48841, 0]]
    hsu := by decide
    w := ![![-21245835, -20317856, -9182108], ![-5909761, -5616715, -2539732]]
    hw := by decide
    g := ![![![1328919107291, -252647362249150640, -18704920585440], ![-4805340795084, 913567026313475028, 0]], ![![316034461369, -60082870840232487, -4448276513188], ![-1142773312188, 217258273180615104, 0]]]
    h := ![![![-2705, -143, -3], ![11560, 133, 0]], ![![-753, -44, -1], ![3218, 55, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {48841} * I107N1 =  Ideal.span {B.equivFun.symm ![-435, -416, -188]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E107RS1 


noncomputable def E107RS2 : RelationCertificate Table 48841 ![![107, 0, 0], ![-46, 1, 0]]
  ![42743, 5733, 1182] ![![48841, 0, 0], ![13507, 1, 0]] where
    su := ![![5225987, 0, 0], ![-2246686, 48841, 0]]
    hsu := by decide
    w := ![![2087610863, 280005453, 57730062], ![577544825, 77461826, 15971007]]
    hw := by decide
    g := ![![![-34187476101, 6499547145541589, 481198426599], ![123621123880, -23502212353521720, 0]], ![![-38684872941999, 7354571826546478338, 544500764744987], ![139883606971213, -26593961850909910082, 0]]]
    h := ![![![216035, -5046, 20], ![501587, -958, 0]], ![![59837, -1373, 5], ![138929, -208, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N2 : Ideal.span {48841} * I107N2 =  Ideal.span {B.equivFun.symm ![42743, 5733, 1182]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E107RS2 


noncomputable def E109RS1 : RelationCertificate Table 2873 ![![109, 0, 0], ![2, 1, 0]]
  ![29453, 3822, 788] ![![2873, 0, 0], ![-858, 1, 0]] where
    su := ![![313157, 0, 0], ![5746, 2873, 0]]
    hsu := by decide
    w := ![![84618469, 10980606, 2263924], ![-25127258, -3260855, -672282]]
    hw := by decide
    g := ![![![7885515589, 82625981514976, -96300688468], ![26404529474, 276671877968596, 0]], ![![216577726, 2269342212683, -2644921288], ![725207234, 7598858860426, 0]]]
    h := ![![![166083519, 83070131, 14243], ![-9051537059, -1551699, 0]], ![![-49318118, -24667485, -4230], ![2687833058, 460836, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {2873} * I109N1 =  Ideal.span {B.equivFun.symm ![29453, 3822, 788]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E109RS1 


noncomputable def E113RS0 : RelationCertificate Table 169 ![![113, 0, 0], ![50, 1, 0]]
  ![-155, 13, 1] ![![169, 0, 0], ![-13, 1, 0]] where
    su := ![![19097, 0, 0], ![8450, 169, 0]]
    hsu := by decide
    w := ![![-26195, 2197, 169], ![2197, -338, 0]]
    hw := by decide
    g := ![![![-4, -26546, 2042], ![-39, -345100, 0]], ![![-2, -11999, 923], ![-20, -155988, 0]]]
    h := ![![![-2435, -99, -1], ![5500, 114, 0]], ![![101, 2, 0], ![-228, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N0 : Ideal.span {169} * I113N0 =  Ideal.span {B.equivFun.symm ![-155, 13, 1]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E113RS0 


noncomputable def E113RS1 : RelationCertificate Table 13 ![![113, 0, 0], ![-47, 1, 0]]
  ![107, 13, 3] ![![13, 0, 0], ![0, 1, 0]] where
    su := ![![1469, 0, 0], ![-611, 13, 0]]
    hsu := by decide
    w := ![![1391, 169, 39], ![546, 65, 13]]
    hw := by decide
    g := ![![![-3, 1, 82], ![6, -1068, 0]], ![![1, -1, -33], ![5, 430, 0]]]
    h := ![![![69766, -1671, 4], ![167733, -449, 0]], ![![27376, -629, 1], ![65818, -112, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {13} * I113N1 =  Ideal.span {B.equivFun.symm ![107, 13, 3]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E113RS1 


noncomputable def E131RS1 : RelationCertificate Table 48841 ![![131, 0, 0], ![-19, 1, 0]]
  ![-24099, -3510, -647] ![![48841, 0, 0], ![13507, 1, 0]] where
    su := ![![6398171, 0, 0], ![-927979, 48841, 0]]
    hsu := by decide
    w := ![![-1177019259, -171431910, -31600127], ![-325622947, -47424611, -8742539]]
    hw := by decide
    g := ![![![282179225907, -53646484085650044, -3971754209413], ![-1020353562784, 193984447341940280, 0]], ![![-21945626711, 4172189364536301, 308890898509], ![79354879262, -15086540374078060, 0]]]
    h := ![![![-25362853006, 1359135088, -1276222], ![-174870195773, 167184435, 0]], ![![-7016645604, 376005393, -353068], ![-48377924603, 46251729, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {48841} * I131N1 =  Ideal.span {B.equivFun.symm ![-24099, -3510, -647]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E131RS1 
