import IdealArithmetic.Examples.NF3_1_456435_2.PrimesBelow3_1_456435_2F2
import IdealArithmetic.Examples.NF3_1_456435_2.ClassGroupData3_1_456435_2

set_option linter.all false

noncomputable section


noncomputable def E83RS1 : RelationCertificate Table 20 ![![83, 0, 0], ![-16, 1, 0]]
  ![53, 11, 4] ![![20, 0, 0], ![6, 1, 0]] where
    su := ![![1660, 0, 0], ![-320, 20, 0]]
    hsu := by decide
    w := ![![1060, 220, 80], ![960, 220, 100]]
    hw := by decide
    g := ![![![3404316, 17797215, 15904568], ![1911174, -39761344, -199]], ![![-598784, -3130331, -2797435], ![-336140, 6993574, 35]]]
    h := ![![![113179, -774211, 476668], ![-31066, -4945430, 0]], ![![102458, -700905, 431535], ![-28149, -4477175, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {20} * I83N1 =  Ideal.span {B.equivFun.symm ![53, 11, 4]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E83RS1 


noncomputable def E83RS2 : RelationCertificate Table 50 ![![83, 0, 0], ![-3, 1, 0]]
  ![177, 9, -14] ![![50, 0, 0], ![-24, 1, 0]] where
    su := ![![4150, 0, 0], ![-150, 50, 0]]
    hsu := by decide
    w := ![![8850, 450, -700], ![-6400, -250, 450]]
    hw := by decide
    g := ![![![395681808, -5704580750, 2175786322], ![-304018870, -13596227720, 722013]], ![![-9096111, 131139780, -50018074], ![6988986, 312556944, -16598]]]
    h := ![![![961974, 418, 3852902], ![-34685, -39973860, 0]], ![![-695809, -304, -2786877], ![25227, 28913850, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N2 : Ideal.span {50} * I83N2 =  Ideal.span {B.equivFun.symm ![177, 9, -14]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E83RS2 


noncomputable def E89RS1 : RelationCertificate Table 5 ![![89, 0, 0], ![0, 1, 0]]
  ![-39109, -8418, -3712] ![![5, 0, 0], ![1, 1, 0]] where
    su := ![![445, 0, 0], ![0, 5, 0]]
    hsu := by decide
    w := ![![-195545, -42090, -18560], ![-631305, -135885, -59920]]
    hw := by decide
    g := ![![![-400, -3121, -6608], ![-701, 4094, 0]], ![![-89, 22, 40], ![-9, -23, 0]]]
    h := ![![![351981, 528469, 1409640], ![5968, -15682709, 0]], ![![1136349, 1706130, 4550936], ![19236, -50630661, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {5} * I89N1 =  Ideal.span {B.equivFun.symm ![-39109, -8418, -3712]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E89RS1 


noncomputable def E97RS0 : RelationCertificate Table 20 ![![97, 0, 0], ![8, 1, 0]]
  ![-1303, -281, -124] ![![20, 0, 0], ![6, 1, 0]] where
    su := ![![1940, 0, 0], ![160, 20, 0]]
    hsu := by decide
    w := ![![-26060, -5620, -2480], ![-27600, -5940, -2620]]
    hw := by decide
    g := ![![![-28748558077, -150353409545, -134364907745], ![-16142237884, 335912269242, 327]], ![![-2373734156, -12414501706, -11094350181], ![-1332845316, 27735875442, 27]]]
    h := ![![![-4287535, -23847096, -17347836], ![-599425, 210342496, 0]], ![![-4540932, -25256457, -18373091], ![-634800, 222773712, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N0 : Ideal.span {20} * I97N0 =  Ideal.span {B.equivFun.symm ![-1303, -281, -124]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E97RS0 


noncomputable def E97RS2 : RelationCertificate Table 50 ![![97, 0, 0], ![-18, 1, 0]]
  ![81717, 17589, 7756] ![![50, 0, 0], ![-24, 1, 0]] where
    su := ![![4850, 0, 0], ![-900, 50, 0]]
    hsu := by decide
    w := ![![4085850, 879450, 387800], ![-723850, -155800, -68700]]
    hw := by decide
    g := ![![![-2351586256780, 33746112550065, -12869403837548], ![1803683654297, 80433777585480, 1066890]], ![![427561137613, -6135656827313, 2339891606837], ![-327942482598, -14624323197429, -193980]]]
    h := ![![![560997, -4407505, 2351668], ![-149501, -28513005, 0]], ![![-99377, 780834, -416622], ![26536, 5051370, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N2 : Ideal.span {50} * I97N2 =  Ideal.span {B.equivFun.symm ![81717, 17589, 7756]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E97RS2 


noncomputable def E101RS0 : RelationCertificate Table 10 ![![101, 0, 0], ![30, 1, 0]]
  ![-2401, -517, -228] ![![10, 0, 0], ![-4, 1, 0]] where
    su := ![![1010, 0, 0], ![300, 10, 0]]
    hsu := by decide
    w := ![![-24010, -5170, -2280], ![-26770, -5760, -2540]]
    hw := by decide
    g := ![![![-189863912721387, 103562130665596, -897538472641211], ![86301778155123, 1121923091126574, 371496]], ![![-57784669092164, 31518909334670, -273163882992161], ![26265758570333, 341454853839132, 113064]]]
    h := ![![![2632951, 49675243, 12045540], ![1273983, -152074971, 0]], ![![2935645, 55385657, 13430234], ![1420355, -169556736, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N0 : Ideal.span {10} * I101N0 =  Ideal.span {B.equivFun.symm ![-2401, -517, -228]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E101RS0 


noncomputable def E101RS1 : RelationCertificate Table 25 ![![101, 0, 0], ![34, 1, 0]]
  ![-1406, -302, -133] ![![25, 0, 0], ![1, 1, 0]] where
    su := ![![2525, 0, 0], ![850, 25, 0]]
    hsu := by decide
    w := ![![-35150, -7550, -3325], ![-22625, -4875, -2150]]
    hw := by decide
    g := ![![![-18629365526, -37348295307, -74875719133], ![-2239106414, 233986622286, 0]], ![![-6179049571, -12387806106, -24835026151], ![-742674220, 77609456721, 0]]]
    h := ![![![-164222, -3602754, -779169], ![-90852, 9836992, 0]], ![![-105683, -2318422, -501406], ![-58453, 6330240, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {25} * I101N1 =  Ideal.span {B.equivFun.symm ![-1406, -302, -133]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E101RS1 


noncomputable def E101RS2 : RelationCertificate Table 4 ![![101, 0, 0], ![37, 1, 0]]
  ![-15, -5, 4] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![404, 0, 0], ![148, 4, 0]]
    hsu := by decide
    w := ![![-60, -20, 16], ![580, 28, -44]]
    hw := by decide
    g := ![![![9440, 116, -69], ![4749, 0, -303]], ![![3435, 43, -24], ![1730, 0, -110]]]
    h := ![![![-6933, -169139, -33836], ![-4166, 427180, 0]], ![![67131, 1641601, 328401], ![40866, -4146064, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N2 : Ideal.span {4} * I101N2 =  Ideal.span {B.equivFun.symm ![-15, -5, 4]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E101RS2 


noncomputable def E109RS1 : RelationCertificate Table 25 ![![109, 0, 0], ![-43, 1, 0]]
  ![1266, 47, -87] ![![25, 0, 0], ![1, 1, 0]] where
    su := ![![2725, 0, 0], ![-1075, 25, 0]]
    hsu := by decide
    w := ![![31650, 1175, -2175], ![-12125, -25, 550]]
    hw := by decide
    g := ![![![1949, 4621, 9397], ![263, -29484, 0]], ![![-808, -1802, -3646], ![-97, 11424, 0]]]
    h := ![![![21993, -546624, 109349], ![-13577, -1489891, 0]], ![![-8380, 209602, -41930], ![5341, 571299, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {25} * I109N1 =  Ideal.span {B.equivFun.symm ![1266, 47, -87]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E109RS1 


noncomputable def E127RS1 : RelationCertificate Table 50 ![![127, 0, 0], ![-44, 1, 0]]
  ![-2393, 119, 26] ![![50, 0, 0], ![-24, 1, 0]] where
    su := ![![6350, 0, 0], ![-2200, 50, 0]]
    hsu := by decide
    w := ![![-119650, 5950, 1300], ![61700, -4450, 250]]
    hw := by decide
    g := ![![![241240336124, -3461968470173, 1320255800746], ![-185034730688, -8251591511834, 2146131]], ![![-81365083834, 1167646170494, -445293376626], ![62408163655, 2783081161025, -723843]]]
    h := ![![![-20308743, 493833079, -96374458], ![10924570, 1529944524, 0]], ![![10474992, -254711691, 49708499], ![-5634593, -789122421, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N1 : Ideal.span {50} * I127N1 =  Ideal.span {B.equivFun.symm ![-2393, 119, 26]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E127RS1 


noncomputable def E137RS0 : RelationCertificate Table 10 ![![137, 0, 0], ![29, 1, 0]]
  ![277, 59, 26] ![![10, 0, 0], ![-4, 1, 0]] where
    su := ![![1370, 0, 0], ![290, 10, 0]]
    hsu := by decide
    w := ![![2770, 590, 260], ![3040, 660, 290]]
    hw := by decide
    g := ![![![611624, -308748, 2723963], ![-275519, -3407232, -2603]], ![![125004, -63102, 556725], ![-56310, -696372, -532]]]
    h := ![![![-11532, -197660, -49422], ![-3881, 846355, 0]], ![![-12676, -216910, -54235], ![-4160, 928778, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N0 : Ideal.span {10} * I137N0 =  Ideal.span {B.equivFun.symm ![277, 59, 26]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E137RS0 


noncomputable def E137RS1 : RelationCertificate Table 25 ![![137, 0, 0], ![33, 1, 0]]
  ![-257, 56, -26] ![![25, 0, 0], ![1, 1, 0]] where
    su := ![![3425, 0, 0], ![825, 25, 0]]
    hsu := by decide
    w := ![![-6425, 1400, -650], ![-4175, -475, 500]]
    hw := by decide
    g := ![![![1209632358392, 2425080257441, 4861791595342], ![145388504643, -15193098735522, 0]], ![![286956580817, 575292760747, 1153344719420], ![34489973686, -3604202248215, 0]]]
    h := ![![![10968, 215997, 48006], ![4283, -822106, 0]], ![![7083, 139497, 31004], ![2768, -530941, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {25} * I137N1 =  Ideal.span {B.equivFun.symm ![-257, 56, -26]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E137RS1 


noncomputable def E137RS2 : RelationCertificate Table 4 ![![137, 0, 0], ![-62, 1, 0]]
  ![-45051, -9697, -4276] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![548, 0, 0], ![-248, 4, 0]]
    hsu := by decide
    w := ![![-180204, -38788, -17104], ![-772276, -166228, -73300]]
    hw := by decide
    g := ![![![-145006110694427, -1672504160362, 1170752912234], ![-72921181387301, 0, 4683011648729]], ![![66681642102124, 769107752088, -538375426460], ![33533097989089, 0, -2153501705721]]]
    h := ![![![-513963, 20225811, -2742900], ![380248, 46971628, 0]], ![![-2202601, 86679033, -11754877], ![1629624, 201299978, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N2 : Ideal.span {4} * I137N2 =  Ideal.span {B.equivFun.symm ![-45051, -9697, -4276]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E137RS2 
