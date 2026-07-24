import IdealArithmetic.Examples.NF3_1_808623_1.PrimesBelow3_1_808623_1F4
import IdealArithmetic.Examples.NF3_1_808623_1.ClassGroupData3_1_808623_1

set_option linter.all false

noncomputable section


noncomputable def E211RS1 : RelationCertificate Table 5 ![![211, 0, 0], ![-56, 1, 0]]
  ![7208, 1314, 485] ![![5, 0, 0], ![1, 1, 0]] where
    su := ![![1055, 0, 0], ![-280, 5, 0]]
    hsu := by decide
    w := ![![36040, 6570, 2425], ![90425, 16485, 6085]]
    hw := by decide
    g := ![![![188681451, 4479671, -1109631], ![38632228, 0, -5548248]], ![![-49501963, -1175276, 291119], ![-10135444, 0, 1455624]]]
    h := ![![![10273296, 287168620, -26589085], ![-1365370, 1122059484, 0]], ![![25775771, 720511132, -66712483], ![-3426151, 2815267026, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R211N1 : Ideal.span {5} * I211N1 =  Ideal.span {B.equivFun.symm ![7208, 1314, 485]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E211RS1 


noncomputable def E223RS1 : RelationCertificate Table 25 ![![223, 0, 0], ![49, 1, 0]]
  ![-3652, 569, -130] ![![25, 0, 0], ![1, 1, 0]] where
    su := ![![5575, 0, 0], ![1225, 25, 0]]
    hsu := by decide
    w := ![![-91300, 14225, -3250], ![-27800, -3375, 2975]]
    hw := by decide
    g := ![![![-8614625, 12834038, 21409827], ![168780, -107058790, 1886]], ![![-1938082, 2885026, 4813145], ![37882, -24068364, 424]]]
    h := ![![![-23260029, 606537563, 59463415], ![-2390895, -2652068335, 0]], ![![-7067621, 184297647, 18068078], ![-726411, -805836255, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R223N1 : Ideal.span {25} * I223N1 =  Ideal.span {B.equivFun.symm ![-3652, 569, -130]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E223RS1 


noncomputable def E227RS1 : RelationCertificate Table 25 ![![227, 0, 0], ![55, 1, 0]]
  ![26746, 813, -1610] ![![25, 0, 0], ![1, 1, 0]] where
    su := ![![5675, 0, 0], ![1375, 25, 0]]
    hsu := by decide
    w := ![![668650, 20325, -40250], ![-259850, 11475, 5675]]
    hw := by decide
    g := ![![![-347360087902, 520603528238, 868116538468], ![6929737619, -4340587126919, -23096436]], ![![-85773165910, 128551981452, 214362930739], ![1711152634, -1071815740182, -5703174]]]
    h := ![![![4493284, -131574062, -11541395], ![509260, 523979011, 0]], ![![-1746912, 51151818, 4486926], ![-197712, -203706395, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R227N1 : Ideal.span {25} * I227N1 =  Ideal.span {B.equivFun.symm ![26746, 813, -1610]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E227RS1 


noncomputable def E229RS1 : RelationCertificate Table 5 ![![229, 0, 0], ![-110, 1, 0]]
  ![-9, -2, 0] ![![5, 0, 0], ![1, 1, 0]] where
    su := ![![1145, 0, 0], ![-550, 5, 0]]
    hsu := by decide
    w := ![![-45, -10, 0], ![-5, -15, -10]]
    hw := by decide
    g := ![![![-46721, -1110, 274], ![-9562, 0, 1374]], ![![22509, 534, -132], ![4611, 0, -662]]]
    h := ![![![8141, 481255, -22280], ![-1605, 1020424, 0]], ![![919, 52013, -2408], ![-92, 110286, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R229N1 : Ideal.span {5} * I229N1 =  Ideal.span {B.equivFun.symm ![-9, -2, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E229RS1 


noncomputable def E239RS0 : RelationCertificate Table 5 ![![239, 0, 0], ![4, 1, 0]]
  ![2935566, 535153, 197535] ![![5, 0, 0], ![1, 1, 0]] where
    su := ![![1195, 0, 0], ![20, 5, 0]]
    hsu := by decide
    w := ![![14677830, 2675765, 987675], ![36828955, 6713910, 2478230]]
    hw := by decide
    g := ![![![9904, -530, 244], ![1875, 0, -248]], ![![545, 0, -14], ![110, 0, -9]]]
    h := ![![![-1675038986, 5025537162, 4187922165], ![-7006685, -200182639980, 0]], ![![-4202932955, 12609853227, 10508147114], ![-17580951, -502289332920, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R239N0 : Ideal.span {5} * I239N0 =  Ideal.span {B.equivFun.symm ![2935566, 535153, 197535]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E239RS0 


noncomputable def E239RS1 : RelationCertificate Table 5 ![![239, 0, 0], ![91, 1, 0]]
  ![-13422299, -2446882, -903190] ![![5, 0, 0], ![1, 1, 0]] where
    su := ![![1195, 0, 0], ![455, 5, 0]]
    hsu := by decide
    w := ![![-67111495, -12234410, -4515950], ![-168393165, -30698035, -11331220]]
    hw := by decide
    g := ![![![-94647316, -2246721, 555708], ![-19378807, 0, 2783418]], ![![-36762933, -872627, 215881], ![-7527107, 0, 1081113]]]
    h := ![![![-25704709361, 1274176229742, 68503092790], ![-4455867220, -3274448016000, 0]], ![![-64497108188, 3197106070936, 171884900004], ![-11180463391, -8216098673440, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R239N1 : Ideal.span {5} * I239N1 =  Ideal.span {B.equivFun.symm ![-13422299, -2446882, -903190]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E239RS1 


noncomputable def E239RS2 : RelationCertificate Table 5 ![![239, 0, 0], ![-95, 1, 0]]
  ![-122529, -22337, -8245] ![![5, 0, 0], ![1, 1, 0]] where
    su := ![![1195, 0, 0], ![-475, 5, 0]]
    hsu := by decide
    w := ![![-612645, -111685, -41225], ![-1537220, -280235, -103440]]
    hw := by decide
    g := ![![![-560900, -13178, 3230], ![-114813, 0, 16491]], ![![223684, 5256, -1285], ![45789, 0, -6578]]]
    h := ![![![179640620, 8978866668, -482727195], ![-33836693, 23074358272, 0]], ![![450745770, 22529349632, -1211236357], ![-84901484, 57897093727, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R239N2 : Ideal.span {5} * I239N2 =  Ideal.span {B.equivFun.symm ![-122529, -22337, -8245]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E239RS2 


noncomputable def E241RS1 : RelationCertificate Table 25 ![![241, 0, 0], ![55, 1, 0]]
  ![-207, -21, 20] ![![25, 0, 0], ![1, 1, 0]] where
    su := ![![6025, 0, 0], ![1375, 25, 0]]
    hsu := by decide
    w := ![![-5175, -525, 500], ![3375, -50, -125]]
    hw := by decide
    g := ![![![91023828032207, -136354320128638, -227378088515401], ![-1813219683849, 1136890440769536, -9037200]], ![![21238893196255, -31816008013156, -53054887292144], ![-423084592656, 265274436038976, -2108680]]]
    h := ![![![-1485871, 43382561, 3805430], ![-159068, -183421722, 0]], ![![969779, -28315067, -2483740], ![103926, 119716267, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R241N1 : Ideal.span {25} * I241N1 =  Ideal.span {B.equivFun.symm ![-207, -21, 20]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E241RS1 
