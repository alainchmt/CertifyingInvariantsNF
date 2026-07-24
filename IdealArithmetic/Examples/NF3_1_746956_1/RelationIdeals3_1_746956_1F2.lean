import IdealArithmetic.Examples.NF3_1_746956_1.PrimesBelow3_1_746956_1F2
import IdealArithmetic.Examples.NF3_1_746956_1.ClassGroupData3_1_746956_1

set_option linter.all false

noncomputable section


noncomputable def E83RS0 : RelationCertificate Table 99 ![![83, 0, 0], ![0, 1, 0]]
  ![82, -18, 11] ![![99, 0, 0], ![-41, 1, 0]] where
    su := ![![8217, 0, 0], ![0, 99, 0]]
    hsu := by decide
    w := ![![8118, -1782, 1089], ![-2178, 495, -693]]
    hw := by decide
    g := ![![![9498636917, 355543959249, -105716421615], ![-342425775, 951329103916, -29013264]], ![![177544646, 6645681465, -1976007876], ![-6400408, 17781852368, -542304]]]
    h := ![![![0, 3, 11], ![61, -82, 0]], ![![0, -1, -3], ![0, 22, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N0 : Ideal.span {99} * I83N0 =  Ideal.span {B.equivFun.symm ![82, -18, 11]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E83RS0 


noncomputable def E83RS1 : RelationCertificate Table 2673 ![![83, 0, 0], ![29, 1, 0]]
  ![634, -144, 143] ![![2673, 0, 0], ![-41, 1, 0]] where
    su := ![![221859, 0, 0], ![77517, 2673, 0]]
    hsu := by decide
    w := ![![1694682, -384912, 382239], ![-10692, 2673, -8019]]
    hw := by decide
    g := ![![![15813163956483444321, 585100502090049213887, -173948795287330498470], ![-23658518565568776, 42269557254816489028799, -1178735418]], ![![5565709881160597192, 205935994524324083947, -61224213662170592772], ![-8327014816033409, 14877483919905756824343, -414875820]]]
    h := ![![![108741927, -3535380535, -1178478653], ![-4600765, 8892157122, 0]], ![![-686325, 22313308, 7437886], ![29060, -56122231, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {2673} * I83N1 =  Ideal.span {B.equivFun.symm ![634, -144, 143]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E83RS1 


noncomputable def E83RS2 : RelationCertificate Table 2673 ![![83, 0, 0], ![-29, 1, 0]]
  ![790, -171, 77] ![![2673, 0, 0], ![-41, 1, 0]] where
    su := ![![221859, 0, 0], ![-77517, 2673, 0]]
    hsu := by decide
    w := ![![2111670, -457083, 205821], ![-24057, 5346, -5346]]
    hw := by decide
    g := ![![![328705, 12158731, -3614799], ![279, 878387485, -2124]], ![![-112333, -4156059, 1235599], ![1457, -300247592, 726]]]
    h := ![![![42043708, 1067125409, -469525463], ![-1832968, 3542783046, 0]], ![![-479104, -12160593, 5350550], ![20921, -40372332, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N2 : Ideal.span {2673} * I83N2 =  Ideal.span {B.equivFun.symm ![790, -171, 77]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E83RS2 


noncomputable def E97RS1 : RelationCertificate Table 99 ![![97, 0, 0], ![-37, 1, 0]]
  ![479, 18, 22] ![![99, 0, 0], ![-41, 1, 0]] where
    su := ![![9603, 0, 0], ![-3663, 99, 0]]
    hsu := by decide
    w := ![![47421, 1782, 2178], ![-17325, -693, -792]]
    hw := by decide
    g := ![![![886309664836805, 33268916082021990, -9890665661746199], ![-31007880568471, 89015991398633201, 108268700]], ![![-335500634053793, -12593501890625635, 3743978806031979], ![11737617228155, -33695809421948255, -40983664]]]
    h := ![![![-3549406, -118762989, 39587218], ![129579, -349087284, 0]], ![![1296741, 43388017, -14462510], ![-47270, 127533042, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {99} * I97N1 =  Ideal.span {B.equivFun.symm ![479, 18, 22]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E97RS1 


noncomputable def E101RS1 : RelationCertificate Table 11 ![![101, 0, 0], ![-27, 1, 0]]
  ![-519, -17, -22] ![![11, 0, 0], ![3, 1, 0]] where
    su := ![![1111, 0, 0], ![-297, 11, 0]]
    hsu := by decide
    w := ![![-5709, -187, -242], ![-3872, -132, -165]]
    hw := by decide
    g := ![![![-32631738, 8302883, 328803], ![-8144754, 0, 3616824]], ![![8598902, -2187923, -86644], ![2146263, 0, -953082]]]
    h := ![![![482452, 11206996, -5359783], ![-17940, 49212551, 0]], ![![327213, 7600773, -3635095], ![-12145, 33376780, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {11} * I101N1 =  Ideal.span {B.equivFun.symm ![-519, -17, -22]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E101RS1 


noncomputable def E103RS0 : RelationCertificate Table 9 ![![103, 0, 0], ![26, 1, 0]]
  ![32, 0, 1] ![![9, 0, 0], ![4, 1, 0]] where
    su := ![![927, 0, 0], ![234, 9, 0]]
    hsu := by decide
    w := ![![288, 0, 9], ![234, 9, 0]]
    hw := by decide
    g := ![![![-31265, 213915, 295642], ![9879, -241889, 0]], ![![-9705, 66387, 91751], ![3070, -75069, 0]]]
    h := ![![![-1178, 34447, 12631], ![119, -118272, 0]], ![![-950, 27719, 10164], ![104, -95172, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N0 : Ideal.span {9} * I103N0 =  Ideal.span {B.equivFun.symm ![32, 0, 1]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E103RS0 


noncomputable def E103RS1 : RelationCertificate Table 9 ![![103, 0, 0], ![51, 1, 0]]
  ![-538, -18, -23] ![![9, 0, 0], ![4, 1, 0]] where
    su := ![![927, 0, 0], ![459, 9, 0]]
    hsu := by decide
    w := ![![-4842, -162, -207], ![-4572, -153, -198]]
    hw := by decide
    g := ![![![51, -407, -564], ![-13, 461, 0]], ![![25, -202, -280], ![-7, 229, 0]]]
    h := ![![![-477717, 25873053, 5174639], ![14723, -48453440, 0]], ![![-451075, 24430316, 4886090], ![13895, -45751572, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {9} * I103N1 =  Ideal.span {B.equivFun.symm ![-538, -18, -23]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E103RS1 


noncomputable def E109RS0 : RelationCertificate Table 81 ![![109, 0, 0], ![9, 1, 0]]
  ![61, -9, -4] ![![81, 0, 0], ![40, 1, 0]] where
    su := ![![8829, 0, 0], ![729, 81, 0]]
    hsu := by decide
    w := ![![4941, -729, -324], ![2025, -243, -243]]
    hw := by decide
    g := ![![![930, -41445, -10361], ![34, 76296, 0]], ![![-624055, 26928515, 6732204], ![24375, -49573502, 0]]]
    h := ![![![481395, -6239211, -5279468], ![-17474, 52314728, 0]], ![![197235, -2556329, -2163103], ![-7134, 21434384, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N0 : Ideal.span {81} * I109N0 =  Ideal.span {B.equivFun.symm ![61, -9, -4]} * (J0 ^ 4*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_0 E109RS0 


noncomputable def E109RS1 : RelationCertificate Table 297 ![![109, 0, 0], ![49, 1, 0]]
  ![28, 18, 11] ![![297, 0, 0], ![-41, 1, 0]] where
    su := ![![32373, 0, 0], ![14553, 297, 0]]
    hsu := by decide
    w := ![![8316, 5346, 3267], ![0, -891, -297]]
    hw := by decide
    g := ![![![-6815571157, -252837305894, 75165085469], ![89566234, -2029519948713, -15312257]], ![![-3645538068, -135238559304, 40204580700], ![47907534, -1085557184578, -8190277]]]
    h := ![![![716, -39698, -8239], ![74, 81642, 0]], ![![-40, -49, -10], ![91, 99, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {297} * I109N1 =  Ideal.span {B.equivFun.symm ![28, 18, 11]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E109RS1 


noncomputable def E109RS2 : RelationCertificate Table 29403 ![![109, 0, 0], ![51, 1, 0]]
  ![-4183, 90, 22] ![![29403, 0, 0], ![-10733, 1, 0]] where
    su := ![![3204927, 0, 0], ![1499553, 29403, 0]]
    hsu := by decide
    w := ![![-122992749, 2646270, 646866], ![44898381, -970299, -235224]]
    hw := by decide
    g := ![![![1249948810942275053107, 13411288476215016713316512, -13750039448061966253577], ![-150056512206961211, 36753855444682643266188693, 13326084954]], ![![615054176812712991475, 6599205440675594033927343, -6765892426822464378911], ![-73837331403393843, 18085230456902847786125905, 6557279898]]]
    h := ![![![-7735544625, 419543344936, 83909090342], ![229638346, -831462804296, 0]], ![![2823857184, -153154117274, -30630977270], ![-83829277, 303525138402, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N2 : Ideal.span {29403} * I109N2 =  Ideal.span {B.equivFun.symm ![-4183, 90, 22]} * (J0 ^ 5*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_2 E109RS2 


noncomputable def E113RS0 : RelationCertificate Table 27 ![![113, 0, 0], ![19, 1, 0]]
  ![37, -9, 2] ![![27, 0, 0], ![13, 1, 0]] where
    su := ![![3051, 0, 0], ![513, 27, 0]]
    hsu := by decide
    w := ![![999, -243, 54], ![702, -162, -81]]
    hw := by decide
    g := ![![![26, -949, -615], ![-8, 1506, 0]], ![![-130, 1877, 1215], ![26, -2983, 0]]]
    h := ![![![-91, 1833, 877], ![69, -9009, 0]], ![![-73, 1285, 615], ![103, -6318, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N0 : Ideal.span {27} * I113N0 =  Ideal.span {B.equivFun.symm ![37, -9, 2]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E113RS0 


noncomputable def E113RS1 : RelationCertificate Table 99 ![![113, 0, 0], ![-17, 1, 0]]
  ![190, 9, 11] ![![99, 0, 0], ![-41, 1, 0]] where
    su := ![![11187, 0, 0], ![-1683, 99, 0]]
    hsu := by decide
    w := ![![18810, 891, 1089], ![-6633, -396, -396]]
    hw := by decide
    g := ![![![1326619711, 51847354523, -15382880130], ![-25697430, 138689064688, 59435082]], ![![-192263720, -7514109350, 2229402917], ![3724280, -20099864444, -8613780]]]
    h := ![![![-1735588, -22681479, 19191568], ![60477, -197149743, 0]], ![![611951, 7997144, -6766655], ![-21263, 69512001, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {99} * I113N1 =  Ideal.span {B.equivFun.symm ![190, 9, 11]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E113RS1 


noncomputable def E113RS2 : RelationCertificate Table 363 ![![113, 0, 0], ![-2, 1, 0]]
  ![-2045, -63, -88] ![![363, 0, 0], ![157, 1, 0]] where
    su := ![![41019, 0, 0], ![-726, 363, 0]]
    hsu := by decide
    w := ![![-742335, -22869, -31944], ![-330330, -10164, -14157]]
    hw := by decide
    g := ![![![359543648695, -57655041626374, -3939164961878], ![-3324211156, 129992443693571, 3480]], ![![-5371998509, 861433087717, 58855686171], ![49667652, -1942237642920, -52]]]
    h := ![![![41484401, -83007831, -456614554], ![-1468708, 4690676774, 0]], ![![18460064, -36937495, -203188031], ![-653541, 2087295224, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N2 : Ideal.span {363} * I113N2 =  Ideal.span {B.equivFun.symm ![-2045, -63, -88]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E113RS2 


noncomputable def E127RS1 : RelationCertificate Table 9801 ![![127, 0, 0], ![45, 1, 0]]
  ![-1435, -180, -44] ![![9801, 0, 0], ![-932, 1, 0]] where
    su := ![![1244727, 0, 0], ![441045, 9801, 0]]
    hsu := by decide
    w := ![![-14064435, -1764180, -431244], ![1332936, 166617, 39204]]
    hw := by decide
    g := ![![![-2523216542447226252393, -2341635014170430616652574, 27756449520181375281876], ![1020590081663535724, -24730996522482543252845984, -11022055170]], ![![-927791424303801358495, -861023558005733604147039, 10206098208665440391852], ![375272874748426540, -9093633503921252248148284, -4052830224]]]
    h := ![![![30005, -1457842, -327272], ![-746, 3778500, 0]], ![![-2847, 138166, 31017], ![80, -358105, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N1 : Ideal.span {9801} * I127N1 =  Ideal.span {B.equivFun.symm ![-1435, -180, -44]} * (J0 ^ 4*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_2 E127RS1 


noncomputable def E131RS1 : RelationCertificate Table 3267 ![![131, 0, 0], ![24, 1, 0]]
  ![2140, 18, 77] ![![3267, 0, 0], ![-932, 1, 0]] where
    su := ![![427977, 0, 0], ![78408, 3267, 0]]
    hsu := by decide
    w := ![![6991380, 58806, 251559], ![-1986336, -16335, -71874]]
    hw := by decide
    g := ![![![20881927768015, 19384574751364148, -229775241347030], ![-23685927544, 68242894164122309, -4142815600]], ![![3915361456996, 3634607765878742, -43082857752544], ![-4441109678, 12795542655765768, -776777925]]]
    h := ![![![-52474, 1461222, 574057], ![1656, -6836490, 0]], ![![14885, -415153, -163097], ![-342, 1942335, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {3267} * I131N1 =  Ideal.span {B.equivFun.symm ![2140, 18, 77]} * (J0 ^ 3*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_2 E131RS1 


noncomputable def E137RS0 : RelationCertificate Table 1089 ![![137, 0, 0], ![-65, 1, 0]]
  ![-223, -9, 22] ![![1089, 0, 0], ![157, 1, 0]] where
    su := ![![149193, 0, 0], ![-70785, 1089, 0]]
    hsu := by decide
    w := ![![-242847, -9801, 23958], ![-32670, -2178, 3267]]
    hw := by decide
    g := ![![![-1583930106102668, 254880519073543886, 17414197312030752], ![5696503596184, -1724005533959501170, 4921725]], ![![755353529581657, -121548860623364014, -8304580709587440], ![-2716580788720, 822153490281802588, -2347100]]]
    h := ![![![-14149809, -873012895, 157428106], ![341106, -1960695500, 0]], ![![-1902675, -117393277, 21169219], ![45947, -263653000, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N0 : Ideal.span {1089} * I137N0 =  Ideal.span {B.equivFun.symm ![-223, -9, 22]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E137RS0 


noncomputable def E137RS1 : RelationCertificate Table 297 ![![137, 0, 0], ![-47, 1, 0]]
  ![-2846, -90, -121] ![![297, 0, 0], ![-41, 1, 0]] where
    su := ![![40689, 0, 0], ![-13959, 297, 0]]
    hsu := by decide
    w := ![![-845262, -26730, -35937], ![103950, 3267, 4455]]
    hw := by decide
    g := ![![![-6046659421065755, -224135594416568533, 66634826220091589], ![80058726758139, -1799140310033461924, -511130650]], ![![2070266053659121, 76739945187046729, -22814550830219268], ![-27410649875229, 615992873131836792, 175001825]]]
    h := ![![![85281152, 3700265604, -946575377], ![-2247774, 11789166048, 0]], ![![-10487862, -455058129, 116409703], ![276436, -1449829936, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {297} * I137N1 =  Ideal.span {B.equivFun.symm ![-2846, -90, -121]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E137RS1 


noncomputable def E137RS2 : RelationCertificate Table 3 ![![137, 0, 0], ![-25, 1, 0]]
  ![2, 0, 1] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![411, 0, 0], ![-75, 3, 0]]
    hsu := by decide
    w := ![![6, 0, 3], ![108, -21, -3]]
    hw := by decide
    g := ![![![138, -322, -753], ![-58, 206, 0]], ![![-23, 54, 128], ![12, -35, 0]]]
    h := ![![![-680, -14718, 7709], ![114, -96012, 0]], ![![-12556, -265321, 138976], ![427, -1730883, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N2 : Ideal.span {3} * I137N2 =  Ideal.span {B.equivFun.symm ![2, 0, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E137RS2 
