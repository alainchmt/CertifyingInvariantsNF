import IdealArithmetic.Examples.NF3_1_420812_2.PrimesBelow3_1_420812_2F3
import IdealArithmetic.Examples.NF3_1_420812_2.ClassGroupData3_1_420812_2

set_option linter.all false

noncomputable section


noncomputable def E139RS0 : RelationCertificate Table 10 ![![139, 0, 0], ![-64, 1, 0]]
  ![107, -1, 3] ![![10, 0, 0], ![3, 1, 0]] where
    su := ![![1390, 0, 0], ![-640, 10, 0]]
    hsu := by decide
    w := ![![1070, -10, 30], ![320, -10, 10]]
    hw := by decide
    g := ![![![-1139, -4014, -2724], ![-739, 13622, 0]], ![![527, 1862, 1264], ![348, -6321, 0]]]
    h := ![![![52900, -5200932, 162543], ![-61621, -11296737, 0]], ![![15815, -1555867, 48625], ![-18456, -3379437, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N0 : Ideal.span {10} * I139N0 =  Ideal.span {B.equivFun.symm ![107, -1, 3]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E139RS0 


noncomputable def E139RS1 : RelationCertificate Table 50 ![![139, 0, 0], ![-54, 1, 0]]
  ![73, -9, 2] ![![50, 0, 0], ![6, 0, 1]] where
    su := ![![6950, 0, 0], ![-2700, 50, 0]]
    hsu := by decide
    w := ![![3650, -450, 100], ![400, 250, 0]]
    hw := by decide
    g := ![![![-1020101, -18713834696, 585209927], ![11581803, -29240944390, 972930]], ![![378893, 6950853001, -217363691], ![-4301799, 10860922380, -361374]]]
    h := ![![![-353, 28779, -1066], ![462, 74088, 0]], ![![0, 3023, -112], ![144, 7784, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N1 : Ideal.span {50} * I139N1 =  Ideal.span {B.equivFun.symm ![73, -9, 2]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E139RS1 


noncomputable def E139RS2 : RelationCertificate Table 125 ![![139, 0, 0], ![-22, 1, 0]]
  ![-193, -6, -7] ![![125, 0, 0], ![33, 1, 0]] where
    su := ![![17375, 0, 0], ![-2750, 125, 0]]
    hsu := by decide
    w := ![![-24125, -750, -875], ![-6375, -125, -250]]
    hw := by decide
    g := ![![![253259663, 9608588618, 582408391], ![143729287, -36400524440, 0]], ![![-38563183, -1463073876, -88681755], ![-21885206, 5542609688, 0]]]
    h := ![![![-7281, 168557, -15325], ![2419, 1065084, 0]], ![![-1919, 44545, -4050], ![672, 281474, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N2 : Ideal.span {125} * I139N2 =  Ideal.span {B.equivFun.symm ![-193, -6, -7]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E139RS2 


noncomputable def E149RS0 : RelationCertificate Table 625 ![![149, 0, 0], ![-71, 1, 0]]
  ![308, -39, 17] ![![625, 0, 0], ![-217, 1, 0]] where
    su := ![![93125, 0, 0], ![-44375, 625, 0]]
    hsu := by decide
    w := ![![192500, -24375, 10625], ![-66875, 8125, -3750]]
    hw := by decide
    g := ![![![4309, -1134144, 10453], ![-2644, -3266556, 0]], ![![-1667, 500615, -4614], ![1844, 1441872, 0]]]
    h := ![![![15536198, -1750985657, 49327161], ![-19154652, -3674873486, 0]], ![![-5397085, 608272619, -17135698], ![6654140, 1276609498, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R149N0 : Ideal.span {625} * I149N0 =  Ideal.span {B.equivFun.symm ![308, -39, 17]} * (J0 ^ 4*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_0 E149RS0 


noncomputable def E149RS1 : RelationCertificate Table 6250 ![![149, 0, 0], ![-55, 1, 0]]
  ![-431, 223, 31] ![![6250, 0, 0], ![-217, 1, 0]] where
    su := ![![931250, 0, 0], ![-343750, 6250, 0]]
    hsu := by decide
    w := ![![-2693750, 1393750, 193750], ![93750, -50000, -6250]]
    hw := by decide
    g := ![![![83993887629, -18270669434634, 168393275290], ![-5839574184, -526228985281275, 0]], ![![-29947484551, 6514290611307, -60039547875], ![2082067580, 187623587109384, 0]]]
    h := ![![![134156674, -9705667728, 352961355], ![-114659565, -26295620932, 0]], ![![-4670158, 337866399, -12287025], ![3991451, 915383362, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R149N1 : Ideal.span {6250} * I149N1 =  Ideal.span {B.equivFun.symm ![-431, 223, 31]} * (J0 ^ 5*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_2 E149RS1 


noncomputable def E149RS2 : RelationCertificate Table 250 ![![149, 0, 0], ![-24, 1, 0]]
  ![803, 1, 22] ![![250, 0, 0], ![-44, 0, 1]] where
    su := ![![37250, 0, 0], ![-6000, 250, 0]]
    hsu := by decide
    w := ![![200750, 250, 5500], ![-35750, -500, -1000]]
    hw := by decide
    g := ![![![-2154393404469, 258714840611898065, -3155010071863893], ![-12240867048159, 788764757965555056, -10578858]], ![![333779260561, -40082581023160370, 488804378346727], ![1896472363629, -122202990924649184, 1638978]]]
    h := ![![![-5897933, 149078294, -12424282], ![1950675, 925609020, 0]], ![![1049912, -26537279, 2211634], ![-347071, -164766735, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R149N2 : Ideal.span {250} * I149N2 =  Ideal.span {B.equivFun.symm ![803, 1, 22]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E149RS2 


noncomputable def E163RS0 : RelationCertificate Table 625 ![![163, 0, 0], ![12, 1, 0]]
  ![527, -16, 23] ![![625, 0, 0], ![-217, 1, 0]] where
    su := ![![101875, 0, 0], ![7500, 625, 0]]
    hsu := by decide
    w := ![![329375, -10000, 14375], ![-114375, 3125, -5000]]
    hw := by decide
    g := ![![![10516, -2905723, 26781], ![-8280, -8369056, 0]], ![![933, -217976, 2009], ![-206, -627812, 0]]]
    h := ![![![-22158971, -268785415, -44800923], ![-3280203, 3651275236, 0]], ![![7694320, 93331184, 15556362], ![1139097, -1267843507, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R163N0 : Ideal.span {625} * I163N0 =  Ideal.span {B.equivFun.symm ![527, -16, 23]} * (J0 ^ 4*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_0 E163RS0 


noncomputable def E163RS1 : RelationCertificate Table 50 ![![163, 0, 0], ![41, 1, 0]]
  ![47, -1, 3] ![![50, 0, 0], ![-17, 1, 0]] where
    su := ![![8150, 0, 0], ![2050, 50, 0]]
    hsu := by decide
    w := ![![2350, -50, 150], ![-800, -50, -50]]
    hw := by decide
    g := ![![![479, -10022, 1180], ![-337, -29496, 0]], ![![131, -2557, 301], ![-60, -7524, 0]]]
    h := ![![![8272, 386376, 18849], ![4583, -1536192, 0]], ![![-2798, -128793, -6283], ![-1366, 512064, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R163N1 : Ideal.span {50} * I163N1 =  Ideal.span {B.equivFun.symm ![47, -1, 3]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E163RS1 


noncomputable def E163RS2 : RelationCertificate Table 2 ![![163, 0, 0], ![-54, 1, 0]]
  ![73, -1, 2] ![![2, 0, 0], ![26, 0, 1]] where
    su := ![![326, 0, 0], ![-108, 2, 0]]
    hsu := by decide
    w := ![![146, -2, 4], ![1860, -26, 48]]
    hw := by decide
    g := ![![![-21375, 1274006, 754815], ![99645, 0, 134106]], ![![7036, -420546, -249163], ![-32891, 0, -44268]]]
    h := ![![![-287, 22300, -826], ![379, 67320, 0]], ![![-4182, 284132, -10524], ![3243, 857718, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R163N2 : Ideal.span {2} * I163N2 =  Ideal.span {B.equivFun.symm ![73, -1, 2]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E163RS2 


noncomputable def E167RS0 : RelationCertificate Table 6250 ![![167, 0, 0], ![13, 1, 0]]
  ![-13651, 233, -374] ![![6250, 0, 0], ![1456, 0, 1]] where
    su := ![![1043750, 0, 0], ![81250, 6250, 0]]
    hsu := by decide
    w := ![![-85318750, 1456250, -2337500], ![-19868750, 337500, -543750]]
    hw := by decide
    g := ![![![-8515098300512071, 341520332392075291394586, 240846490902202053800], ![36551761244269323, -1505290604690035668378330, -344437335]], ![![-722493189187559, 28977482750512044966659, 20435459835602634968], ![3101361560348193, -127721627073836587868049, -29224986]]]
    h := ![![![7587533798, 99833508734, 15360096184], ![1188451818, -1282568031551, 0]], ![![1766958309, 23248878148, 3577005447], ![276762622, -298679954868, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R167N0 : Ideal.span {6250} * I167N0 =  Ideal.span {B.equivFun.symm ![-13651, 233, -374]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E167RS0 


noncomputable def E167RS1 : RelationCertificate Table 6250 ![![167, 0, 0], ![24, 1, 0]]
  ![949, -317, 26] ![![6250, 0, 0], ![1456, 0, 1]] where
    su := ![![1043750, 0, 0], ![150000, 6250, 0]]
    hsu := by decide
    w := ![![5931250, -1981250, 162500], ![1381250, -450000, 37500]]
    hw := by decide
    g := ![![![3939919143, -158063444739499629, -111469197956178], ![-16917222005, 696683025116284968, -367399824]], ![![582032748, -23350281609058247, -16467040607032], ![-2499131799, 102919083254994936, -54274974]]]
    h := ![![![2363, 59008, 4918], ![707, -410640, 0]], ![![546, 13726, 1144], ![190, -95521, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R167N1 : Ideal.span {6250} * I167N1 =  Ideal.span {B.equivFun.symm ![949, -317, 26]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E167RS1 


noncomputable def E167RS2 : RelationCertificate Table 50 ![![167, 0, 0], ![-38, 1, 0]]
  ![-21, -7, -4] ![![50, 0, 0], ![6, 0, 1]] where
    su := ![![8350, 0, 0], ![-1900, 50, 0]]
    hsu := by decide
    w := ![![-1050, -350, -200], ![-50, 300, 100]]
    hw := by decide
    g := ![![![15578948, 193429170348, -6040040501], ![-118931327, 302231036172, 3439994]], ![![-3478799, -43192921464, 1348746905], ![26557521, -67488483696, -768154]]]
    h := ![![![-1195, 50460, -2656], ![585, 221774, 0]], ![![-56, 2508, -132], ![44, 11023, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R167N2 : Ideal.span {50} * I167N2 =  Ideal.span {B.equivFun.symm ![-21, -7, -4]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E167RS2 


noncomputable def E173RS1 : RelationCertificate Table 6250 ![![173, 0, 0], ![-76, 1, 0]]
  ![577, 209, -27] ![![6250, 0, 0], ![-217, 1, 0]] where
    su := ![![1081250, 0, 0], ![-475000, 6250, 0]]
    hsu := by decide
    w := ![![3606250, 1306250, -168750], ![-125000, -43750, 6250]]
    hw := by decide
    g := ![![![-264689002329, 57576157090526, -530655852856], ![18402191783, 1658299540175020, 0]], ![![116076358649, -25249370361396, 232713102789], ![-8070067551, -727228446215634, 0]]]
    h := ![![![-160114490, 17987552672, -473383165], ![174313637, 40947643759, 0]], ![![5550999, -623601423, 16411483], ![-6043032, -1419593279, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R173N1 : Ideal.span {6250} * I173N1 =  Ideal.span {B.equivFun.symm ![577, 209, -27]} * (J0 ^ 5*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_2 E173RS1 


noncomputable def E181RS0 : RelationCertificate Table 125 ![![181, 0, 0], ![40, 1, 0]]
  ![-42, 11, -8] ![![125, 0, 0], ![33, 1, 0]] where
    su := ![![22625, 0, 0], ![5000, 125, 0]]
    hsu := by decide
    w := ![![-5250, 1375, -1000], ![-1375, 625, -250]]
    hw := by decide
    g := ![![![370159731, 14043739528, 851237582], ![210072179, -53202348884, 0]], ![![83350846, 3162304945, 191677780], ![47303193, -11979861252, 0]]]
    h := ![![![409616, 18066709, 903388], ![190402, -81756618, 0]], ![![107515, 4742324, 237130], ![50001, -21460266, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R181N0 : Ideal.span {125} * I181N0 =  Ideal.span {B.equivFun.symm ![-42, 11, -8]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E181RS0 


noncomputable def E181RS1 : RelationCertificate Table 50 ![![181, 0, 0], ![53, 1, 0]]
  ![-27, -9, 2] ![![50, 0, 0], ![6, 0, 1]] where
    su := ![![9050, 0, 0], ![2650, 50, 0]]
    hsu := by decide
    w := ![![-1350, -450, 100], ![-200, 250, -100]]
    hw := by decide
    g := ![![![458677, -6949593716, 218785141], ![4430781, -10860287646, 2606256]], ![![140148, -2123486849, 66851011], ![1353878, -3318421038, 796356]]]
    h := ![![![-46205, -2904715, -109618], ![-29384, 9920430, 0]], ![![-7128, -447083, -16872], ![-4467, 1526915, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R181N1 : Ideal.span {50} * I181N1 =  Ideal.span {B.equivFun.symm ![-27, -9, 2]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E181RS1 


noncomputable def E181RS2 : RelationCertificate Table 10 ![![181, 0, 0], ![87, 1, 0]]
  ![24, -2, 1] ![![10, 0, 0], ![3, 1, 0]] where
    su := ![![1810, 0, 0], ![870, 10, 0]]
    hsu := by decide
    w := ![![240, -20, 10], ![70, -20, 0]]
    hw := by decide
    g := ![![![25, 63, 43], ![14, -213, 0]], ![![10, 30, 21], ![14, -104, 0]]]
    h := ![![![-18820, -2611742, -60043], ![-23304, 5433892, 0]], ![![-5550, -762953, -17540], ![-6699, 1587370, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R181N2 : Ideal.span {10} * I181N2 =  Ideal.span {B.equivFun.symm ![24, -2, 1]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E181RS2 
