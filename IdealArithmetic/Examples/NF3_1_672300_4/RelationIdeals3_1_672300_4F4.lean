import IdealArithmetic.Examples.NF3_1_672300_4.PrimesBelow3_1_672300_4F4
import IdealArithmetic.Examples.NF3_1_672300_4.ClassGroupData3_1_672300_4

set_option linter.all false

noncomputable section


noncomputable def E211RS1 : RelationCertificate Table 7 ![![211, 0, 0], ![29, 1, 0]]
  ![83459, 4658, 4421] ![![7, 0, 0], ![3, -3, 1]] where
    su := ![![1477, 0, 0], ![203, 7, 0]]
    hsu := by decide
    w := ![![584213, 32606, 30947], ![-934269, -52143, -49490]]
    hw := by decide
    g := ![![![-708, 22, 3], ![-307, 0, 0]], ![![-124, -2, 6], ![-47, 0, 0]]]
    h := ![![![5541066, 79756921, 19940596], ![1139667, -601065905, 0]], ![![-8861271, -127546665, -31888850], ![-1822254, 961220040, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R211N1 : Ideal.span {7} * I211N1 =  Ideal.span {B.equivFun.symm ![83459, 4658, 4421]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E211RS1 


noncomputable def E223RS1 : RelationCertificate Table 49 ![![223, 0, 0], ![73, 1, 0]]
  ![-213, 293, -205] ![![49, 0, 0], ![3, -10, 1]] where
    su := ![![10927, 0, 0], ![3577, 49, 0]]
    hsu := by decide
    w := ![![-10437, 14357, -10045], ![350399, -19453, -17150]]
    hw := by decide
    g := ![![![-313199, -20645, -16329], ![-15252, 0, 0]], ![![-114291, -7530, -5959], ![-5548, 0, 0]]]
    h := ![![![998578, 42020736, 4085573], ![515429, -130154712, 0]], ![![-32741075, -1377718811, -133952252], ![-16895960, 4267335978, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R223N1 : Ideal.span {49} * I223N1 =  Ideal.span {B.equivFun.symm ![-213, 293, -205]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E223RS1 
