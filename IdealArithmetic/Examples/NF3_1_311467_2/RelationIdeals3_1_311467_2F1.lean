import IdealArithmetic.Examples.NF3_1_311467_2.PrimesBelow3_1_311467_2F1
import IdealArithmetic.Examples.NF3_1_311467_2.ClassGroupData3_1_311467_2

set_option linter.all false

noncomputable section


noncomputable def E43RS0 : RelationCertificate Table 4 ![![43, 0, 0], ![19, 1, 0]]
  ![-1142004305, 442826597, -51571441] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![172, 0, 0], ![76, 4, 0]]
    hsu := by decide
    w := ![![-4568017220, 1771306388, -206285764], ![8664002088, -3359576268, 391255156]]
    hw := by decide
    g := ![![![-42365, -15049, -1405], ![-3761, 134, 0]], ![![-13361, -8868, -1025], ![-2215, 61, 0]]]
    h := ![![![-33657403680, -2468231697, -38488046], ![76111913365, 1603414537, 0]], ![![63836846834, 4681410635, 72998959], ![-144358863860, -3041141448, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N0 : Ideal.span {4} * I43N0 =  Ideal.span {B.equivFun.symm ![-1142004305, 442826597, -51571441]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E43RS0 


noncomputable def E43RS1 : RelationCertificate Table 4 ![![43, 0, 0], ![-18, 1, 0]]
  ![-4717, 1829, -213] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![172, 0, 0], ![-72, 4, 0]]
    hsu := by decide
    w := ![![-18868, 7316, -852], ![35784, -13876, 1616]]
    hw := by decide
    g := ![![![-13, -36, -12199], ![-7, 48777, 0]], ![![24, 10, 4810], ![3, -19236, 0]]]
    h := ![![![-36067, 2239, -16], ![-85898, 475, 0]], ![![68454, -4225, 29], ![163032, -843, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {4} * I43N1 =  Ideal.span {B.equivFun.symm ![-4717, 1829, -213]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E43RS1 


noncomputable def E43RS2 : RelationCertificate Table 4 ![![43, 0, 0], ![-2, 1, 0]]
  ![-1510181, 734125, 123003] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![172, 0, 0], ![-8, 4, 0]]
    hsu := by decide
    w := ![![-6040724, 2936500, 492012], ![-20664504, 3778948, 857128]]
    hw := by decide
    g := ![![![227554597003, -83046748089, 10276044358], ![-20761687019, 110607, 0]], ![![-50732309108, 18514911805, -2291004594], ![4628727953, -4122, 0]]]
    h := ![![![-11132989, 5577416, -2844], ![-238604173, 245295, 0]], ![![-38060806, 19031401, -14566], ![-815724266, 840620, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N2 : Ideal.span {4} * I43N2 =  Ideal.span {B.equivFun.symm ![-1510181, 734125, 123003]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E43RS2 
