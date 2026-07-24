import IdealArithmetic.Examples.NF3_1_797796_1.PrimesBelow3_1_797796_1F2
import IdealArithmetic.Examples.NF3_1_797796_1.ClassGroupData3_1_797796_1

set_option linter.all false

noncomputable section


noncomputable def E83RS0 : RelationCertificate Table 2 ![![83, 0, 0], ![24, 1, 0]]
  ![-98788, -21853, -2466] ![![2, 0, 0], ![-77, -4, 1]] where
    su := ![![166, 0, 0], ![48, 2, 0]]
    hsu := by decide
    w := ![![-197576, -43706, -4932], ![-905514, -200310, -22604]]
    hw := by decide
    g := ![![![60512, -568098, -52391], ![-1219597, 0, 33100]], ![![18205, -170456, -15716], ![-365832, 0, 9930]]]
    h := ![![![-2604764, -120485, -1008], ![9004026, 40599, 0]], ![![-11937783, -552145, -4616], ![41265968, 185913, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N0 : Ideal.span {2} * I83N0 =  Ideal.span {B.equivFun.symm ![-98788, -21853, -2466]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E83RS0 


noncomputable def E83RS1 : RelationCertificate Table 16 ![![83, 0, 0], ![35, 1, 0]]
  ![-22, -3, 0] ![![16, 0, 0], ![-383, -13, 5]] where
    su := ![![1328, 0, 0], ![560, 16, 0]]
    hsu := by decide
    w := ![![-352, -48, 0], ![-2224, -320, -32]]
    hw := by decide
    g := ![![![612956, -10145737, -1468654], ![-6884605, 0, 286740]], ![![261087, -4321332, -625538], ![-2932331, 0, 122130]]]
    h := ![![![-174, -40, -2], ![412, 83, 0]], ![![-988, -63, -2], ![2339, 82, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {16} * I83N1 =  Ideal.span {B.equivFun.symm ![-22, -3, 0]} * (J0 ^ 7) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7 E83RS1 


noncomputable def E89RS0 : RelationCertificate Table 4 ![![89, 0, 0], ![32, 1, 0]]
  ![162388, 10041, -2167] ![![4, 0, 0], ![-79, -5, 1]] where
    su := ![![356, 0, 0], ![128, 4, 0]]
    hsu := by decide
    w := ![![649552, 40164, -8668], ![1993308, 68028, -20368]]
    hw := by decide
    g := ![![![-284976, 6496673, 1555586], ![-2103199, 0, 0]], ![![-159160, 3629631, 869090], ![-1175034, 0, 0]]]
    h := ![![![10487348, 396863, 4293], ![-29162862, -192122, 0]], ![![32171279, 1217388, 13194], ![-89460797, -589679, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N0 : Ideal.span {4} * I89N0 =  Ideal.span {B.equivFun.symm ![162388, 10041, -2167]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E89RS0 


noncomputable def E89RS1 : RelationCertificate Table 16 ![![89, 0, 0], ![-16, 1, 0]]
  ![5281346, 1168293, 131836] ![![16, 0, 0], ![-383, -13, 5]] where
    su := ![![1424, 0, 0], ![-256, 16, 0]]
    hsu := by decide
    w := ![![84501536, 18692688, 2109376], ![907838352, 200824032, 22661984]]
    hw := by decide
    g := ![![![-985368, 16318060, 2362258], ![11075981, 0, -461214]], ![![170448, -2820293, -408289], ![-1914602, 0, 79716]]]
    h := ![![![44296978, -2824547, 10584], ![246071856, -405070, 0]], ![![475902257, -30345383, 113710], ![2643660061, -4351908, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {16} * I89N1 =  Ideal.span {B.equivFun.symm ![5281346, 1168293, 131836]} * (J0 ^ 7) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7 E89RS1 


noncomputable def E97RS1 : RelationCertificate Table 2 ![![97, 0, 0], ![-17, 1, 0]]
  ![-42, -9, -1] ![![2, 0, 0], ![-77, -3, 1]] where
    su := ![![194, 0, 0], ![-34, 2, 0]]
    hsu := by decide
    w := ![![-84, -18, -2], ![-1026, -238, -28]]
    hw := by decide
    g := ![![![70, 13, -2], ![1, 0, 0]], ![![22, -2, 0], ![1, 0, 0]]]
    h := ![![![-352, 29, -1], ![-2006, 48, 0]], ![![-4297, 267, -2], ![-24488, 90, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {2} * I97N1 =  Ideal.span {B.equivFun.symm ![-42, -9, -1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E97RS1 


noncomputable def E101RS1 : RelationCertificate Table 2 ![![101, 0, 0], ![-47, 1, 0]]
  ![-78666, -2961, 835] ![![2, 0, 0], ![-77, -3, 1]] where
    su := ![![202, 0, 0], ![-94, 2, 0]]
    hsu := by decide
    w := ![![-157332, -5922, 1670], ![2176422, 120898, -27500]]
    hw := by decide
    g := ![![![195201, -6000434, -1253577], ![861327, 0, 0]], ![![-56532, 1739330, 363370], ![-249669, 0, 0]]]
    h := ![![![-2265546, 54156, -247], ![-4866840, 12891, 0]], ![![31338354, -748481, 3376], ![67320969, -177363, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {2} * I101N1 =  Ideal.span {B.equivFun.symm ![-78666, -2961, 835]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E101RS1 


noncomputable def E103RS1 : RelationCertificate Table 2 ![![103, 0, 0], ![47, 1, 0]]
  ![-595892, -131818, -14875] ![![2, 0, 0], ![-77, -3, 1]] where
    su := ![![206, 0, 0], ![94, 2, 0]]
    hsu := by decide
    w := ![![-1191784, -263636, -29750], ![-16023346, -3544544, -399984]]
    hw := by decide
    g := ![![![-17, -199, -115], ![1607, 0, 0]], ![![30, -93, -42], ![611, 0, 0]]]
    h := ![![![-25395962, -700793, -6923], ![55642302, 349097, 0]], ![![-341444551, -9421469, -93054], ![748101640, 4692285, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {2} * I103N1 =  Ideal.span {B.equivFun.symm ![-595892, -131818, -14875]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E103RS1 


noncomputable def E107RS1 : RelationCertificate Table 2 ![![107, 0, 0], ![30, 1, 0]]
  ![-24416, -2300, 415] ![![2, 0, 0], ![-77, -3, 1]] where
    su := ![![214, 0, 0], ![60, 2, 0]]
    hsu := by decide
    w := ![![-48832, -4600, 830], ![-636918, -17092, 5984]]
    hw := by decide
    g := ![![![-66658, 2050116, 428298], ![-294281, 0, 0]], ![![-29682, 914381, 191026], ![-131252, 0, 0]]]
    h := ![![![-150628, -5468, -25], ![536426, 1545, 0]], ![![-1963947, -70875, -334], ![6994129, 19365, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {2} * I107N1 =  Ideal.span {B.equivFun.symm ![-24416, -2300, 415]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E107RS1 


noncomputable def E137RS1 : RelationCertificate Table 2 ![![137, 0, 0], ![4, 1, 0]]
  ![4, 1, 0] ![![2, 0, 0], ![-77, -4, 1]] where
    su := ![![274, 0, 0], ![8, 2, 0]]
    hsu := by decide
    w := ![![8, 2, 0], ![402, 24, -4]]
    hw := by decide
    g := ![![![-153939, 1446478, 133279], ![3102963, 0, -84238]], ![![-5943, 56359, 5192], ![120896, 0, -3282]]]
    h := ![![![20, 5, 0], ![-684, 0, 0]], ![![1345, 336, 0], ![-46016, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {2} * I137N1 =  Ideal.span {B.equivFun.symm ![4, 1, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E137RS1 
