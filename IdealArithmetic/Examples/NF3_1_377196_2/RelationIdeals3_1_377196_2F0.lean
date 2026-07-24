import IdealArithmetic.Examples.NF3_1_377196_2.PrimesBelow3_1_377196_2F0
import IdealArithmetic.Examples.NF3_1_377196_2.ClassGroupData3_1_377196_2

set_option linter.all false

noncomputable section


noncomputable def E3RS0 : RelationCertificate Table 1 ![![3, 0, 0], ![0, 1, 0]]
  ![1, 0, 0] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![3, 0, 0], ![0, 1, 0]]
    hsu := by decide
    w := ![![3, 0, 0], ![0, 1, 0]]
    hw := by decide
    g := ![![![0, 0, -7], ![0, 3, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![0, 0, -7], ![0, 3, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {1} * I3N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 3 ![![3, 0, 0], ![-1, 1, 0]]
  ![-8, -1, 1] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![9, 0, 0], ![-3, 3, 0]]
    hsu := by decide
    w := ![![-24, -3, 3], ![117, 0, -6]]
    hw := by decide
    g := ![![![-8, -1, -10], ![0, 4, 0]], ![![-24, -4, 0], ![1, -1, 0]]]
    h := ![![![0, -3, -2], ![9, 1, 0]], ![![16, -3, -17], ![16, 7, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {3} * I3N1 =  Ideal.span {B.equivFun.symm ![-8, -1, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E3RS1 


noncomputable def E5RS0 : RelationCertificate Table 3 ![![5, 0, 0], ![0, 1, 0]]
  ![173, -8, -4] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![15, 0, 0], ![0, 3, 0]]
    hsu := by decide
    w := ![![519, -24, -12], ![-480, 141, -60]]
    hw := by decide
    g := ![![![1173, 160, 88], ![56, 12, 0]], ![![2773, 378, 271], ![129, 1, 0]]]
    h := ![![![34, -4, -5], ![12, 3, 0]], ![![-32, 18, -4], ![-43, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {3} * I5N0 =  Ideal.span {B.equivFun.symm ![173, -8, -4]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 3 ![![5, 0, 0], ![1, 1, 0]]
  ![124554230, -1722215, -5296186] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![15, 0, 0], ![3, 3, 0]]
    hsu := by decide
    w := ![![373662690, -5166645, -15888558], ![-626672163, 82184742, -17351691]]
    hw := by decide
    g := ![![![-524396132103222, -71643568935196, -51683224723249], ![-23881189645063, -16, 0]], ![![-1340524122986913, -183143861167153, -132118841566285], ![-61047953722382, 0, 0]]]
    h := ![![![22039428, -3215861, -15888558], ![3764718, 10592372, 0]], ![![-42575915, 4681212, -17351691], ![-7578940, 11567794, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {3} * I5N1 =  Ideal.span {B.equivFun.symm ![124554230, -1722215, -5296186]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E5RS1 


noncomputable def E5RS2 : RelationCertificate Table 3 ![![5, 0, 0], ![-2, 1, 0]]
  ![166392845217931937, 25258634640025540, 16399279638570107] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![15, 0, 0], ![-6, 3, 0]]
    hsu := by decide
    w := ![![499178535653795811, 75775903920076620, 49197838915710321], ![1960373631991298166, 297587082326492793, 193209722118748887]]
    hw := by decide
    g := ![![![-87188149, 45788350, -26017703], ![15262784, -264, 0]], ![![-568981874, -71475603, 76429781], ![-23825198, 88, 0]]]
    h := ![![![-602277346267812835, 1614443318926225722, -6024250437670717325], ![563799602292370282, 4305378781141736676, 0]], ![![-2365263216341451448, 6340240789044080137, -23658432538678626529], ![2214153444345396610, 16908080847728483182, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N2 : Ideal.span {3} * I5N2 =  Ideal.span {B.equivFun.symm ![166392845217931937, 25258634640025540, 16399279638570107]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E5RS2 


noncomputable def E7RS0 : RelationCertificate Table 3 ![![7, 0, 0], ![1, 1, 0]]
  ![5267399, -12523292, 7227106] ![![3, 0, 0], ![-5, 0, 1]] where
    su := ![![21, 0, 0], ![3, 3, 0]]
    hsu := by decide
    w := ![![15802197, -37569876, 21681318], ![-1373997543, 92518032, 14425425]]
    hw := by decide
    g := ![![![-559091796638547, -283097144558164, -444967757979890], ![783497075070956, 0, 0]], ![![-1020869522206565, -516919132852125, -812485579680092], ![1430620677117580, 0, 0]]]
    h := ![![![5285953551, 251187998, 92527426], ![791020226, 0, -320232438]], ![![-145286244835, -6944942260, -2513339775], ![-21747312436, 0, 8799093450]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {3} * I7N0 =  Ideal.span {B.equivFun.symm ![5267399, -12523292, 7227106]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 3 ![![7, 0, 0], ![-1, 1, 0]]
  ![-177202756373068, -26899592194427, -17464678548415] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![21, 0, 0], ![-3, 3, 0]]
    hsu := by decide
    w := ![![-531608269119204, -80698776583281, -52394035645245], ![-2087731660907397, -316920184760388, -205761823909404]]
    hw := by decide
    g := ![![![-7683056, -140996, 483996], ![-46997, 12, 0]], ![![9234461, -469826, -156657], ![-156607, -2, 0]]]
    h := ![![![-24893662215260, -4263816151525, -2494954078345], ![2947120866248, 0, 0]], ![![-97762374631307, -16744856114778, -9798182090924], ![11573931216650, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {3} * I7N1 =  Ideal.span {B.equivFun.symm ![-177202756373068, -26899592194427, -17464678548415]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E7RS1 


noncomputable def E17RS0 : RelationCertificate Table 3 ![![17, 0, 0], ![-8, 1, 0]]
  ![114019432, 23324369, -19750398] ![![3, 0, 0], ![-5, 0, 1]] where
    su := ![![51, 0, 0], ![-24, 3, 0]]
    hsu := by decide
    w := ![![342058296, 69973107, -59251194], ![1826671218, -285534057, 78092607]]
    hw := by decide
    g := ![![![-2513371396811592, -1272650162154901, -2000332042312287], ![3522174980581892, 0, 0]], ![![-559091796638547, -283097144558164, -444967757979890], ![783497075070956, 0, 0]]]
    h := ![![![-348115594, 4407949897, -3878695164], ![423110280, 9416866770, 0]], ![![-2238900500, 28256349022, -24867453689], ![2715738415, 60396106226, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N0 : Ideal.span {3} * I17N0 =  Ideal.span {B.equivFun.symm ![114019432, 23324369, -19750398]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E17RS0 


noncomputable def E17RS1 : RelationCertificate Table 3 ![![17, 0, 0], ![-2, 1, 0]]
  ![-21677, -5128, 4170] ![![3, 0, 0], ![-5, 0, 1]] where
    su := ![![51, 0, 0], ![-6, 3, 0]]
    hsu := by decide
    w := ![![-65031, -15384, 12510], ![-421659, 59676, -14295]]
    hw := by decide
    g := ![![![115561392, 58514720, 91972541], ![-161944805, 0, 0]], ![![66492657, 33668675, 52919907], ![-93181115, 0, 0]]]
    h := ![![![441717, -904849, 3187818], ![-105191, -7741248, 0]], ![![3003983, -6149532, 21674411], ![-715136, -52638536, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {3} * I17N1 =  Ideal.span {B.equivFun.symm ![-21677, -5128, 4170]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E17RS1 


noncomputable def E23RS0 : RelationCertificate Table 3 ![![23, 0, 0], ![3, 1, 0]]
  ![-5686, -17, 299] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![69, 0, 0], ![9, 3, 0]]
    hsu := by decide
    w := ![![-17058, -51, 897], ![35265, -3294, 180]]
    hw := by decide
    g := ![![![1110202, 151226, 132166], ![50411, -9888, 0]], ![![711865, 97190, 73477], ![32397, -1442, 0]]]
    h := ![![![114415, 354540, 830353], ![30343, -2728260, 0]], ![![-239398, -741847, -1737300], ![-63457, 5708280, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N0 : Ideal.span {3} * I23N0 =  Ideal.span {B.equivFun.symm ![-5686, -17, 299]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E23RS0 


noncomputable def E23RS1 : RelationCertificate Table 3 ![![23, 0, 0], ![5, 1, 0]]
  ![-29172561462304975, -4428430023688544, -2875177671053824] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![69, 0, 0], ![15, 3, 0]]
    hsu := by decide
    w := ![![-87517684386914925, -13285290071065632, -8625533013161472], ![-343699395208039776, -52173982830735567, -33874187836873632]]
    hw := by decide
    g := ![![![-469649315, 16813276, 12676122], ![5604428, 62, 0]], ![![-36250683, -10754299, 8992464], ![-3584764, 16, 0]]]
    h := ![![![1021655655046865503, 5600259162142976936, 7868847550577968768], ![465588584233795848, -25855195548709190784, 0]], ![![4012245447423902778, 21993334267475307727, 30902533163026363296], ![1828459195851948770, -101538507735078854336, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {3} * I23N1 =  Ideal.span {B.equivFun.symm ![-29172561462304975, -4428430023688544, -2875177671053824]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E23RS1 


noncomputable def E23RS2 : RelationCertificate Table 3 ![![23, 0, 0], ![-9, 1, 0]]
  ![3178171, 138074, -244070] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![69, 0, 0], ![-27, 3, 0]]
    hsu := by decide
    w := ![![9534513, 414222, -732210], ![-28662186, 1225611, 722448]]
    hw := by decide
    g := ![![![-449693217291, -61437575607, -44320684518], ![-20479191869, -60, 0]], ![![-54385469866, -7430201942, -5360101489], ![-2476733979, 23, 0]]]
    h := ![![![-2396590, 30727801, -23982235], ![2273796, 78763905, 0]], ![![7336623, -93942794, 73326107], ![-6955316, -240894235, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N2 : Ideal.span {3} * I23N2 =  Ideal.span {B.equivFun.symm ![3178171, 138074, -244070]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E23RS2 


noncomputable def E31RS1 : RelationCertificate Table 3 ![![31, 0, 0], ![-7, 1, 0]]
  ![-1883, 98, 37] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![93, 0, 0], ![-21, 3, 0]]
    hsu := by decide
    w := ![![-5649, 294, 111], ![4464, -1587, 723]]
    hw := by decide
    g := ![![![153305, 19957, 64993], ![6653, -21684, 0]], ![![21049, 3078, -8158], ![1027, 4448, 0]]]
    h := ![![![18088, -140365, 140647], ![-8607, -622860, 0]], ![![-14489, 112432, -112664], ![6904, 498975, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {3} * I31N1 =  Ideal.span {B.equivFun.symm ![-1883, 98, 37]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E31RS1 
