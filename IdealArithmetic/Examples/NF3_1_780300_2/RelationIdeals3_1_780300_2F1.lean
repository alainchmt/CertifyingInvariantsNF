import IdealArithmetic.Examples.NF3_1_780300_2.PrimesBelow3_1_780300_2F1
import IdealArithmetic.Examples.NF3_1_780300_2.ClassGroupData3_1_780300_2

set_option linter.all false

noncomputable section


noncomputable def E41RS1 : RelationCertificate Table 64009 ![![41, 0, 0], ![-19, 1, 0]]
  ![-954961, -136833, -39218] ![![64009, 0, 0], ![-5961, 1, 0]] where
    su := ![![2624369, 0, 0], ![-1216171, 64009, 0]]
    hsu := by decide
    w := ![![-61126098649, -8758543497, -2510304962], ![5685855461, 814706552, 233504832]]
    hw := by decide
    g := ![![![-49416930172, -34260133502503206, 11494760446500], ![-530637188959, -367884060710009210, 0]], ![![22250278990, 15425832371103635, -5175585430242], ![238922682079, 165642023902180046, 0]]]
    h := ![![![-8749032, 509924, -6642], ![-18829229, 116552, 0]], ![![813860, -47417, 616], ![1751549, -10804, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {64009} * I41N1 =  Ideal.span {B.equivFun.symm ![-954961, -136833, -39218]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E41RS1 


noncomputable def E43RS0 : RelationCertificate Table 121 ![![43, 0, 0], ![13, 1, 0]]
  ![213, 18, -14] ![![121, 0, 0], ![-32, 1, 0]] where
    su := ![![5203, 0, 0], ![1573, 121, 0]]
    hsu := by decide
    w := ![![25773, 2178, -1694], ![-9196, -363, 484]]
    hw := by decide
    g := ![![![-33, -24388, 1524], ![-102, -92217, 0]], ![![-11, -8738, 546], ![-31, -33040, 0]]]
    h := ![![![557, 45, 0], ![-1826, -7, 0]], ![![-214, -30, -2], ![702, 45, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N0 : Ideal.span {121} * I43N0 =  Ideal.span {B.equivFun.symm ![213, 18, -14]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E43RS0 


noncomputable def E43RS1 : RelationCertificate Table 23 ![![43, 0, 0], ![-8, 1, 0]]
  ![-237, 27, 2] ![![23, 0, 0], ![-4, 1, 0]] where
    su := ![![989, 0, 0], ![-184, 23, 0]]
    hsu := by decide
    w := ![![-5451, 621, 46], ![1288, -345, 46]]
    hw := by decide
    g := ![![![-2519, -355344, 178008], ![-14995, -2047050, 0]], ![![348, 47380, -23734], ![2013, 272940, 0]]]
    h := ![![![-48671, 6268, -46], ![-261577, 990, 0]], ![![11528, -1481, 10], ![61956, -214, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {23} * I43N1 =  Ideal.span {B.equivFun.symm ![-237, 27, 2]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E43RS1 


noncomputable def E43RS2 : RelationCertificate Table 5819 ![![43, 0, 0], ![-5, 1, 0]]
  ![1577, 216, 85] ![![5819, 0, 0], ![-142, 1, 0]] where
    su := ![![250217, 0, 0], ![-29095, 5819, 0]]
    hsu := by decide
    w := ![![9176563, 1256904, 494615], ![-209484, -29095, -11638]]
    hw := by decide
    g := ![![![10255371, 2446895697550, -34463320701], ![420253549, 100271031579556, 0]], ![![-1176465, -280728402666, 3953921281], ![-48210210, -11503933967068, 0]]]
    h := ![![![50005979, -10123331, 48861], ![430051104, -1050469, 0]], ![![-1141532, 231096, -1116], ![-9817168, 23993, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N2 : Ideal.span {5819} * I43N2 =  Ideal.span {B.equivFun.symm ![1577, 216, 85]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E43RS2 


noncomputable def E47RS1 : RelationCertificate Table 2783 ![![47, 0, 0], ![12, 1, 0]]
  ![467, -27, 21] ![![2783, 0, 0], ![-395, 1, 0]] where
    su := ![![130801, 0, 0], ![33396, 2783, 0]]
    hsu := by decide
    w := ![![1299661, -75141, 58443], ![-180895, 11132, -8349]]
    hw := by decide
    g := ![![![1301, 21055669, -106611], ![9166, 148349205, 0]], ![![396, 5800574, -29370], ![2790, 40868355, 0]]]
    h := ![![![445, 27, -1], ![-1704, 34, 0]], ![![-79, -12, -1], ![304, 22, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {2783} * I47N1 =  Ideal.span {B.equivFun.symm ![467, -27, 21]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E47RS1 


noncomputable def E53RS1 : RelationCertificate Table 253 ![![53, 0, 0], ![-19, 1, 0]]
  ![-1073, -159, -45] ![![253, 0, 0], ![111, 1, 0]] where
    su := ![![13409, 0, 0], ![-4807, 253, 0]]
    hsu := by decide
    w := ![![-271469, -40227, -11385], ![-126753, -18722, -5313]]
    hw := by decide
    g := ![![![17391098, -11959122238, -215482503], ![-39639167, 27258536625, 0]], ![![-6162151, 4237413940, 76350801], ![14045262, -9658376325, 0]]]
    h := ![![![-7897, 451, -5], ![-21972, 110, 0]], ![![-3689, 217, -3], ![-10264, 69, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {253} * I53N1 =  Ideal.span {B.equivFun.symm ![-1073, -159, -45]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E53RS1 


noncomputable def E59RS1 : RelationCertificate Table 11 ![![59, 0, 0], ![13, 1, 0]]
  ![171, -28, 1] ![![11, 0, 0], ![1, 1, 0]] where
    su := ![![649, 0, 0], ![143, 11, 0]]
    hsu := by decide
    w := ![![1881, -308, 11], ![341, 143, -55]]
    hw := by decide
    g := ![![![-227, -6369, -12777], ![-594, 70210, 0]], ![![-83, -1397, -2795], ![-134, 15351, 0]]]
    h := ![![![15487, 1275, 13], ![-70274, -383, 0]], ![![2805, 223, 1], ![-12728, -32, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {11} * I59N1 =  Ideal.span {B.equivFun.symm ![171, -28, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E59RS1 


noncomputable def E67RS0 : RelationCertificate Table 11 ![![67, 0, 0], ![10, 1, 0]]
  ![43, 1, -2] ![![11, 0, 0], ![1, 1, 0]] where
    su := ![![737, 0, 0], ![110, 11, 0]]
    hsu := by decide
    w := ![![473, 11, -22], ![-297, 44, 0]]
    hw := by decide
    g := ![![![20, -302, -612], ![-21, 3370, 0]], ![![4, -49, -98], ![6, 540, 0]]]
    h := ![![![3659, 366, 0], ![-24511, -1, 0]], ![![-2311, -241, -2], ![15481, 67, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N0 : Ideal.span {11} * I67N0 =  Ideal.span {B.equivFun.symm ![43, 1, -2]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E67RS0 


noncomputable def E67RS1 : RelationCertificate Table 5819 ![![67, 0, 0], ![22, 1, 0]]
  ![6203, -571, -90] ![![5819, 0, 0], ![-142, 1, 0]] where
    su := ![![389873, 0, 0], ![128018, 5819, 0]]
    hsu := by decide
    w := ![![36095257, -3322649, -523710], ![-896126, 87285, 11638]]
    hw := by decide
    g := ![![![-88639145, -21149152879154, 297875401456], ![-3632332323, -866668480536128, 0]], ![![-30356170, -7242949305859, 102013373516], ![-1243961658, -296807910244757, 0]]]
    h := ![![![343873969, 19140759, 319102], ![-1047252260, -10689962, 0]], ![![-8536330, -475179, -7924], ![25996998, 265455, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {5819} * I67N1 =  Ideal.span {B.equivFun.symm ![6203, -571, -90]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E67RS1 


noncomputable def E67RS2 : RelationCertificate Table 253 ![![67, 0, 0], ![-32, 1, 0]]
  ![-13, -9, 7] ![![253, 0, 0], ![111, 1, 0]] where
    su := ![![16951, 0, 0], ![-8096, 253, 0]]
    hsu := by decide
    w := ![![-3289, -2277, 1771], ![-253, -1012, 759]]
    hw := by decide
    g := ![![![-25886126, 17800779571, 320738969], ![59001711, -40573479578, 0]], ![![11767890, -8092289709, -145808932], ![-26822308, 18444829898, 0]]]
    h := ![![![-132271, 4759, -39], ![-276942, 1310, 0]], ![![-9835, 356, -3], ![-20592, 102, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N2 : Ideal.span {253} * I67N2 =  Ideal.span {B.equivFun.symm ![-13, -9, 7]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E67RS2 


noncomputable def E71RS1 : RelationCertificate Table 23 ![![71, 0, 0], ![8, 1, 0]]
  ![39, 4, 2] ![![23, 0, 0], ![-4, 1, 0]] where
    su := ![![1633, 0, 0], ![184, 23, 0]]
    hsu := by decide
    w := ![![897, 92, 46], ![184, 23, 0]]
    hw := by decide
    g := ![![![-66979, -9126107, 4571426], ![-385131, -52571400, 0]], ![![-7700, -1049503, 525714], ![-44274, -6045711, 0]]]
    h := ![![![25, 3, 0], ![-217, 1, 0]], ![![-8, -1, 0], ![72, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {23} * I71N1 =  Ideal.span {B.equivFun.symm ![39, 4, 2]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E71RS1 
