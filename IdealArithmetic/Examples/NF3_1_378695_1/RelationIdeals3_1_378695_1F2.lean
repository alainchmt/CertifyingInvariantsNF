import IdealArithmetic.Examples.NF3_1_378695_1.PrimesBelow3_1_378695_1F2
import IdealArithmetic.Examples.NF3_1_378695_1.ClassGroupData3_1_378695_1

set_option linter.all false

noncomputable section


noncomputable def E101RS1 : RelationCertificate Table 41 ![![101, 0, 0], ![19, 1, 0]]
  ![-406, 150, -17] ![![41, 0, 0], ![3, 1, 0]] where
    su := ![![4141, 0, 0], ![779, 41, 0]]
    hsu := by decide
    w := ![![-16646, 6150, -697], ![1927, -738, 82]]
    hw := by decide
    g := ![![![-10, -2790, -930], ![-37, 38136, 0]], ![![-2, -525, -175], ![-9, 7176, 0]]]
    h := ![![![-1176, -76, -1], ![6230, 84, 0]], ![![125, 6, 0], ![-662, 2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {41} * I101N1 =  Ideal.span {B.equivFun.symm ![-406, 150, -17]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E101RS1 


noncomputable def E109RS1 : RelationCertificate Table 41 ![![109, 0, 0], ![44, 1, 0]]
  ![-191, -8, 2] ![![41, 0, 0], ![3, 1, 0]] where
    su := ![![4469, 0, 0], ![1804, 41, 0]]
    hsu := by decide
    w := ![![-7831, -328, 82], ![-943, -123, 0]]
    hw := by decide
    g := ![![![3, -4334, -1446], ![-94, 59280, 0]], ![![0, -1805, -602], ![-18, 24680, 0]]]
    h := ![![![-217103, -6035, -25], ![537819, 2727, 0]], ![![-26223, -728, -3], ![64961, 327, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {41} * I109N1 =  Ideal.span {B.equivFun.symm ![-191, -8, 2]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E109RS1 


noncomputable def E109RS2 : RelationCertificate Table 41 ![![109, 0, 0], ![49, 1, 0]]
  ![-2576, 324, 83] ![![41, 0, 0], ![3, 1, 0]] where
    su := ![![4469, 0, 0], ![2009, 41, 0]]
    hsu := by decide
    w := ![![-105616, 13284, 3403], ![-23083, 2214, 656]]
    hw := by decide
    g := ![![![-400, -1506, -570], ![-43, 22668, 0]], ![![-151, -694, -257], ![-16, 10272, 0]]]
    h := ![![![-2001510, -58521, -360], ![4452286, 39323, 0]], ![![-437688, -12810, -79], ![973621, 8627, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N2 : Ideal.span {41} * I109N2 =  Ideal.span {B.equivFun.symm ![-2576, 324, 83]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E109RS2 


noncomputable def E127RS1 : RelationCertificate Table 41 ![![127, 0, 0], ![-51, 1, 0]]
  ![-5368, 2019, -228] ![![41, 0, 0], ![3, 1, 0]] where
    su := ![![5207, 0, 0], ![-2091, 41, 0]]
    hsu := by decide
    w := ![![-220088, 82779, -9348], ![26076, -9799, 1107]]
    hw := by decide
    g := ![![![-13336, 7539918, 2514792], ![182934, -103106493, 0]], ![![4581, -2591359, -864297], ![-62868, 35436186, 0]]]
    h := ![![![-17926, 428, -3], ![-44534, 153, 0]], ![![2196, -34, 0], ![5456, 27, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N1 : Ideal.span {41} * I127N1 =  Ideal.span {B.equivFun.symm ![-5368, 2019, -228]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E127RS1 


noncomputable def E127RS2 : RelationCertificate Table 41 ![![127, 0, 0], ![-11, 1, 0]]
  ![27, 8, -2] ![![41, 0, 0], ![3, 1, 0]] where
    su := ![![5207, 0, 0], ![-451, 41, 0]]
    hsu := by decide
    w := ![![1107, 328, -82], ![451, -41, 0]]
    hw := by decide
    g := ![![![-45172, 25446219, 8487092], ![617351, -347970770, 0]], ![![3408, -1920175, -640437], ![-46577, 26257917, 0]]]
    h := ![![![12517, -1138, 0], ![144512, -2, 0]], ![![5115, -465, 0], ![59054, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N2 : Ideal.span {41} * I127N2 =  Ideal.span {B.equivFun.symm ![27, 8, -2]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E127RS2 


noncomputable def E137RS1 : RelationCertificate Table 41 ![![137, 0, 0], ![57, 1, 0]]
  ![-1397, 523, -59] ![![41, 0, 0], ![3, 1, 0]] where
    su := ![![5617, 0, 0], ![2337, 41, 0]]
    hsu := by decide
    w := ![![-57277, 21443, -2419], ![6724, -2542, 287]]
    hw := by decide
    g := ![![![61204, -34487597, -11502667], ![-836655, 471609344, 0]], ![![26508, -14936767, -4981868], ![-362358, 204256586, 0]]]
    h := ![![![-1143166, -28520, -149], ![2747585, 20354, 0]], ![![134086, 3318, 17], ![-322274, -2322, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {41} * I137N1 =  Ideal.span {B.equivFun.symm ![-1397, 523, -59]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E137RS1 
