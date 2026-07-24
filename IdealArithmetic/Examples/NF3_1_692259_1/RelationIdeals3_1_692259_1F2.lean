import IdealArithmetic.Examples.NF3_1_692259_1.PrimesBelow3_1_692259_1F2
import IdealArithmetic.Examples.NF3_1_692259_1.ClassGroupData3_1_692259_1

set_option linter.all false

noncomputable section


noncomputable def E101RS0 : RelationCertificate Table 4 ![![101, 0, 0], ![-46, 1, 0]]
  ![240, 14, 9] ![![4, 0, 0], ![1, 1, 0]] where
    su := ![![404, 0, 0], ![-184, 4, 0]]
    hsu := by decide
    w := ![![960, 56, 36], ![1612, 96, 60]]
    hw := by decide
    g := ![![![-52205, 3073, 165837], ![-12281, -221118, 0]], ![![-8578192, 504598, 27248361], ![-2018396, -36331147, 0]]]
    h := ![![![-10064, -472113, 30135], ![-47, -1014542, 0]], ![![-16883, -792746, 50601], ![-44, -1703562, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N0 : Ideal.span {4} * I101N0 =  Ideal.span {B.equivFun.symm ![240, 14, 9]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E101RS0 


noncomputable def E101RS1 : RelationCertificate Table 2 ![![101, 0, 0], ![-30, 1, 0]]
  ![1866, -282, -19] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![202, 0, 0], ![-60, 2, 0]]
    hsu := by decide
    w := ![![3732, -564, -38], ![-778, 2170, -884]]
    hw := by decide
    g := ![![![1591391, -226691, 72175], ![682350, 303, 0]], ![![-382434, 54477, -17314], ![-163977, -93, 0]]]
    h := ![![![-11682, -361722, 35005], ![-108, -1178508, 0]], ![![2637, 80771, -7820], ![120, 263126, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {2} * I101N1 =  Ideal.span {B.equivFun.symm ![1866, -282, -19]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E101RS1 


noncomputable def E113RS1 : RelationCertificate Table 4 ![![113, 0, 0], ![-10, 1, 0]]
  ![-3994084, 766218, -29997] ![![4, 0, 0], ![1, 1, 0]] where
    su := ![![452, 0, 0], ![-40, 4, 0]]
    hsu := by decide
    w := ![![-15976336, 3064872, -119988], ![-9379840, -3514132, 2238660]]
    hw := by decide
    g := ![![![2519551473716, 1063148166, 100618010727], ![630153655473, -113, 0]], ![![-95234090520, -40184910, -3803162925], ![-23818568857, 10, 0]]]
    h := ![![![13971342, 153956434, -41986839], ![126146, 1581494270, 0]], ![![8143855, 89730796, -24469380], ![73404, 921866535, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {4} * I113N1 =  Ideal.span {B.equivFun.symm ![-3994084, 766218, -29997]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E113RS1 


noncomputable def E131RS1 : RelationCertificate Table 2 ![![131, 0, 0], ![-13, 1, 0]]
  ![-2426730, 432066, -3679] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![262, 0, 0], ![-26, 2, 0]]
    hsu := by decide
    w := ![![-4853460, 864132, -7358], ![-3425362, -2367866, 1288840]]
    hw := by decide
    g := ![![![3002415826551, -427675429606, 137038141696], ![1287370198474, -393, 0]], ![![-166649612169, 23738199035, -7606325898], ![-71455706567, 42, 0]]]
    h := ![![![-6244981, -87104045, 18665905], ![-45131, -815079078, 0]], ![![-4032103, -56234840, 12053353], ![-29067, -526114941, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {2} * I131N1 =  Ideal.span {B.equivFun.symm ![-2426730, 432066, -3679]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E131RS1 
