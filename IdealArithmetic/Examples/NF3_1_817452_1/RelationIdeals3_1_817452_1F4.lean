import IdealArithmetic.Examples.NF3_1_817452_1.PrimesBelow3_1_817452_1F4
import IdealArithmetic.Examples.NF3_1_817452_1.ClassGroupData3_1_817452_1

set_option linter.all false

noncomputable section


noncomputable def E197RS1 : RelationCertificate Table 81250 ![![197, 0, 0], ![70, 1, 0]]
  ![-20168, 33718, -5393] ![![81250, 0, 0], ![4526, 1, 0]] where
    su := ![![16006250, 0, 0], ![5687500, 81250, 0]]
    hsu := by decide
    w := ![![-1638650000, 2739587500, -438181250], ![-92218750, 152587500, -24375000]]
    hw := by decide
    g := ![![![194808205070, -285026323435583685, -62975325558689], ![-3497164529901, 5116745201643468596, 0]], ![![8538204981430146684, -12492354437779196216897433, -2760131338856755511247], ![-153276437194255284628, 224260671282111385288813895, 0]]]
    h := ![![![-409284, -6628, -41], ![1151554, 2684, 0]], ![![-23115, -424, -3], ![65036, 291, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R197N1 : Ideal.span {81250} * I197N1 =  Ideal.span {B.equivFun.symm ![-20168, 33718, -5393]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E197RS1 


noncomputable def E199RS0 : RelationCertificate Table 5 ![![199, 0, 0], ![46, 1, 0]]
  ![-1183, -212, -38] ![![5, 0, 0], ![1, 1, 0]] where
    su := ![![995, 0, 0], ![230, 5, 0]]
    hsu := by decide
    w := ![![-5915, -1060, -190], ![-7795, -1395, -250]]
    hw := by decide
    g := ![![![15856, -410027, -425774], ![-78829, 2128872, 0]], ![![3705, -95800, -99480], ![-18419, 497400, 0]]]
    h := ![![![-3535, -115, -1], ![15267, 161, 0]], ![![-4615, -136, -1], ![19931, 149, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R199N0 : Ideal.span {5} * I199N0 =  Ideal.span {B.equivFun.symm ![-1183, -212, -38]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E199RS0 


noncomputable def E199RS1 : RelationCertificate Table 130 ![![199, 0, 0], ![53, 1, 0]]
  ![1886, -176, -29] ![![130, 0, 0], ![-24, 1, 0]] where
    su := ![![25870, 0, 0], ![6890, 130, 0]]
    hsu := by decide
    w := ![![245180, -22880, -3770], ![-50310, 6110, 520]]
    hw := by decide
    g := ![![![-8756557, -6376131916, 265687359], ![-47430495, -34539357329, 0]], ![![-2327258, -1694605693, 70612609], ![-12605729, -9179639364, 0]]]
    h := ![![![7011494, 148517, 306], ![-26326140, -60923, 0]], ![![-1438590, -30483, -63], ![5401491, 12541, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R199N1 : Ideal.span {130} * I199N1 =  Ideal.span {B.equivFun.symm ![1886, -176, -29]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E199RS1 


noncomputable def E199RS2 : RelationCertificate Table 16250 ![![199, 0, 0], ![-99, 1, 0]]
  ![-156422, -4378, 5803] ![![16250, 0, 0], ![4526, 1, 0]] where
    su := ![![3233750, 0, 0], ![-1608750, 16250, 0]]
    hsu := by decide
    w := ![![-2541857500, -71142500, 94298750], ![-706956250, -19971250, 26260000]]
    hw := by decide
    g := ![![![-331978752009856460991, 20871324873267560637574804, 4611428401815470816116], ![1191925479487443104923, -74935711529501400761827961, 0]], ![![166823493472321103042, -10488102951392709694972303, -2317300704430321355915], ![-598957527380737500059, 37656136446992722033591974, 0]]]
    h := ![![![-253632612026, 3066221268, -5093665], ![-509827168048, 1013645138, 0]], ![![-70541709623, 852794637, -1416680], ![-141795961328, 281920936, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R199N2 : Ideal.span {16250} * I199N2 =  Ideal.span {B.equivFun.symm ![-156422, -4378, 5803]} * (J0 ^ 4*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_1 E199RS2 


noncomputable def E223RS0 : RelationCertificate Table 3125 ![![223, 0, 0], ![36, 1, 0]]
  ![-8029, 1179, 46] ![![3125, 0, 0], ![1401, 1, 0]] where
    su := ![![696875, 0, 0], ![112500, 3125, 0]]
    hsu := by decide
    w := ![![-25090625, 3684375, 143750], ![-11240625, 1643750, 65625]]
    hw := by decide
    g := ![![![42748027349, -357863731016731, -255434519293], ![-95351595634, 798232872790062, 0]], ![![7248817590, -60683249172253, -43314242931], ![-16168847232, 135357009159270, 0]]]
    h := ![![![-38479, -1106, -1], ![238133, 269, 0]], ![![-17295, -517, -1], ![107033, 244, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R223N0 : Ideal.span {3125} * I223N0 =  Ideal.span {B.equivFun.symm ![-8029, 1179, 46]} * (J0 ^ 5*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_0 E223RS0 


noncomputable def E223RS1 : RelationCertificate Table 625 ![![223, 0, 0], ![66, 1, 0]]
  ![-209, 109, -9] ![![625, 0, 0], ![151, 1, 0]] where
    su := ![![139375, 0, 0], ![41250, 625, 0]]
    hsu := by decide
    w := ![![-130625, 68125, -5625], ![-33125, 16250, -1250]]
    hw := by decide
    g := ![![![-34, -166104, -1100], ![143, 687516, 0]], ![![-124, -57231, -379], ![514, 236880, 0]]]
    h := ![![![-4631, -133, -1], ![15644, 214, 0]], ![![-1235, -84, -1], ![4172, 221, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R223N1 : Ideal.span {625} * I223N1 =  Ideal.span {B.equivFun.symm ![-209, 109, -9]} * (J0 ^ 4*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_0 E223RS1 


noncomputable def E223RS2 : RelationCertificate Table 125 ![![223, 0, 0], ![-102, 1, 0]]
  ![-4301, 776, -1] ![![125, 0, 0], ![26, 1, 0]] where
    su := ![![27875, 0, 0], ![-12750, 125, 0]]
    hsu := by decide
    w := ![![-537625, 97000, -125], ![-112000, 15875, 750]]
    hw := by decide
    g := ![![![-27934241, 17514402265, 673672211], ![134304969, -84209021592, 0]], ![![12746562, -7991924366, -307400576], ![-61284027, 38425069932, 0]]]
    h := ![![![-72114221, 799723, -909], ![-157661441, 202706, 0]], ![![-15021512, 166653, -190], ![-32841140, 42376, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R223N2 : Ideal.span {125} * I223N2 =  Ideal.span {B.equivFun.symm ![-4301, 776, -1]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E223RS2 


noncomputable def E227RS1 : RelationCertificate Table 650 ![![227, 0, 0], ![-106, 1, 0]]
  ![428, 72, 3] ![![650, 0, 0], ![-24, 1, 0]] where
    su := ![![147550, 0, 0], ![-68900, 650, 0]]
    hsu := by decide
    w := ![![278200, 46800, 1950], ![-9750, -1300, 0]]
    hw := by decide
    g := ![![![8071660, 142288288553, -5928692703], ![218607449, 3853650256956, 0]], ![![524412406, 9244429135891, -385185457767], ![14202836000, 250370547548547, 0]]]
    h := ![![![5272, -48, 0], ![11286, 3, 0]], ![![-107, 107, -1], ![-229, 227, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R227N1 : Ideal.span {650} * I227N1 =  Ideal.span {B.equivFun.symm ![428, 72, 3]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E227RS1 


noncomputable def E233RS1 : RelationCertificate Table 130 ![![233, 0, 0], ![-21, 1, 0]]
  ![-16, -44, 9] ![![130, 0, 0], ![-24, 1, 0]] where
    su := ![![30290, 0, 0], ![-2730, 130, 0]]
    hsu := by decide
    w := ![![-2080, -5720, 1170], ![1950, 1040, -260]]
    hw := by decide
    g := ![![![8866774, 6456469595, -269034960], ![48028337, 34974544816, 0]], ![![-3329800902, -2424650030704, 101032865517], ![-18036421551, -13134272517211, 0]]]
    h := ![![![-134, 7, 0], ![-1486, 9, 0]], ![![186, 12, -1], ![2063, 231, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R233N1 : Ideal.span {130} * I233N1 =  Ideal.span {B.equivFun.symm ![-16, -44, 9]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E233RS1 


noncomputable def E239RS1 : RelationCertificate Table 5 ![![239, 0, 0], ![-48, 1, 0]]
  ![120119, 21516, 3854] ![![5, 0, 0], ![1, 1, 0]] where
    su := ![![1195, 0, 0], ![-240, 5, 0]]
    hsu := by decide
    w := ![![600595, 107580, 19270], ![790715, 141635, 25370]]
    hw := by decide
    g := ![![![1014, 4241, 4574], ![1055, -22944, 0]], ![![-215, -852, -924], ![-209, 4632, 0]]]
    h := ![![![166729, -3463, 18], ![827669, -448, 0]], ![![219425, -4524, 23], ![1089259, -423, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R239N1 : Ideal.span {5} * I239N1 =  Ideal.span {B.equivFun.symm ![120119, 21516, 3854]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E239RS1 


noncomputable def E251RS1 : RelationCertificate Table 650 ![![251, 0, 0], ![61, 1, 0]]
  ![698486, 125114, 22411] ![![650, 0, 0], ![-24, 1, 0]] where
    su := ![![163150, 0, 0], ![39650, 650, 0]]
    hsu := by decide
    w := ![![454015900, 81324100, 14567150], ![-12864150, -2304250, -412750]]
    hw := by decide
    g := ![![![1499589046003948, 26435005634465249126, -1101461171555923582], ![40613869995940329, 715949761511350327905, 0]], ![![358467501082529, 6319124853666095479, -263297491242165580], ![9708494820985189, 171143369307407626914, 0]]]
    h := ![![![14618202, 256670, 361], ![-60138856, -68200, 0]], ![![-414220, -7320, -11], ![1704089, 2126, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R251N1 : Ideal.span {650} * I251N1 =  Ideal.span {B.equivFun.symm ![698486, 125114, 22411]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E251RS1 
