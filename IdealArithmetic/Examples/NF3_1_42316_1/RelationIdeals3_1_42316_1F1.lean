import IdealArithmetic.Examples.NF3_1_42316_1.PrimesBelow3_1_42316_1F1
import IdealArithmetic.Examples.NF3_1_42316_1.ClassGroupData3_1_42316_1

set_option linter.all false

noncomputable section


noncomputable def E43RS1 : RelationCertificate Table 10 ![![43, 0, 0], ![-14, 1, 0]]
  ![-345234, -20642, -24103] ![![10, 0, 0], ![1, 1, 0]] where
    su := ![![430, 0, 0], ![-140, 10, 0]]
    hsu := by decide
    w := ![![-3452340, -206420, -241030], ![-1281790, -76640, -89490]]
    hw := by decide
    g := ![![![-2956, -2687, -5558], ![-559, 27924, 0]], ![![727, 602, 1283], ![137, -6444, 0]]]
    h := ![![![8103142, -140319214, 20064579], ![-5901440, -431400500, 0]], ![![3008556, -52097929, 7449607], ![-2191067, -160171025, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {10} * I43N1 =  Ideal.span {B.equivFun.symm ![-345234, -20642, -24103]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E43RS1 


noncomputable def E47RS1 : RelationCertificate Table 10 ![![47, 0, 0], ![14, 1, 0]]
  ![58, -46, 21] ![![10, 0, 0], ![1, 1, 0]] where
    su := ![![470, 0, 0], ![140, 10, 0]]
    hsu := by decide
    w := ![![580, -460, 210], ![810, -240, -50]]
    hw := by decide
    g := ![![![-32941, -30964, -63100], ![-6383, 314766, 0]], ![![-10182, -9479, -19314], ![-1966, 96309, 0]]]
    h := ![![![-18282, -305322, -43653], ![-11896, 1025856, 0]], ![![-25183, -420791, -60163], ![-16439, 1413828, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {10} * I47N1 =  Ideal.span {B.equivFun.symm ![58, -46, 21]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E47RS1 
