import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_3_670761_3.RI3_3_670761_3

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-8, -1, 0]

def alpha1 := B.equivFun.symm ![125, 3, -3]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-12, -1, 0]

def zeta2 := B.equivFun.symm ![24, 2, -1]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-2, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![5, 0, 0], ![-2, 1, 0]] ![![5, 0, 0], ![-2, 1, 0]]
  ![![25, 0, 0], ![8, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![25, 0, 0], ![-10, 5, 0]], ![![-10, 5, 0], ![6, -3, 5]]]
 hmul := by decide
 f := ![![![![96958173, 25918301, -956566], ![-33599605, 0, -1784050]], ![![0, 0, 0], ![-574900, 0, 100]]], ![![![29087779, 7775577, -286973], ![-10079992, 0, -535221]], ![![0, 0, 0], ![-172472, 0, 30]]]]
 g := ![![![![9795, 48540, 27034], ![5100, -135100, -50]], ![![-4907, -24264, -13513], ![-2515, 67530, 25]]], ![![![-4907, -24264, -13513], ![-2515, 67530, 25]], ![![2933, 14557, 8108], ![1544, -40518, -15]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![25, 0, 0], ![8, 1, 0]] ![![5, 0, 0], ![-2, 1, 0]]
  ![![-8, -1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![125, 0, 0], ![-50, 25, 0]], ![![40, 5, 0], ![-14, 7, 5]]]
 hmul := by decide
 f := ![![![![-635780946793, -170482517984, 7015577334], ![220215875123, 0, 11692878325]], ![![3877104894, 0, 544811], ![-74393, 0, 45]]]]
 g := ![![![![-207, -7, 5]], ![![389, 14, -10]]], ![![![-5, 0, 0]], ![![2, -1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![-1, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![17, 0, 0], ![-1, 1, 0]] ![![17, 0, 0], ![-1, 1, 0]]
  ![![289, 0, 0], ![101, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![289, 0, 0], ![-17, 17, 0]], ![![-17, 17, 0], ![3, -1, 5]]]
 hmul := by decide
 f := ![![![![-31735881915, -108180448, -79610756180], ![1860453038, 270655791470, 0]], ![![0, 0, 0], ![353175918, -38148, 0]]], ![![![-11081103833, -37772979, -27797401625], ![649607714, 94503910007, 0]], ![![0, 0, 0], ![123317166, -13320, 0]]]]
 g := ![![![![-23726, -1441827, -70680], ![-13005, 4085304, 0]], ![![1363, 85269, 4180], ![884, -241604, 0]]], ![![![1363, 85269, 4180], ![884, -241604, 0]], ![![-258, -14994, -735], ![-103, 42484, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![289, 0, 0], ![101, 1, 0]] ![![17, 0, 0], ![-1, 1, 0]]
  ![![125, 3, -3]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![4913, 0, 0], ![-289, 289, 0]], ![![1717, 17, 0], ![-99, 101, 5]]]
 hmul := by decide
 f := ![![![![-14595466346517158, -50378345977732, -36614249820536821], ![855593411796440, 124488441327034260, 0]], ![![273108086601, 137057391128, 0], ![172576398, -16464, 0]]]]
 g := ![![![![1198, 93, -48]], ![![-932, -82, 33]]], ![![![368, 28, -15]], ![![-291, -26, 10]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-127, -11, 5])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![269, 7, -6])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![17, 0, 0], ![-1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![289, 0, 0], ![101, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![5, 0, 0], ![-2, 1, 0]] ![![17, 0, 0], ![-1, 1, 0]]
  ![![85, 0, 0], ![33, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![85, 0, 0], ![-5, 5, 0]], ![![-34, 17, 0], ![4, -2, 5]]]
 hmul := by decide
 f := ![![![![2791343086, 9096834, 6999667369], ![-163661533, -23798870095, 0]], ![![2679115, 0, -510], ![0, 0, 0]]], ![![![1067278758, 3478203, 2676344708], ![-62576500, -9099572405, 0]], ![![1024368, 0, -195], ![0, 0, 0]]]]
 g := ![![![![1048274, 22213523, 3267899], ![668355, -55553195, -170]], ![![-92478, -1958991, -288193], ![-58860, 4899185, 15]]], ![![![-523981, -11103271, -1633436], ![-334050, 27767868, 85]], ![![61639, 1306267, 192169], ![39315, -3266808, -10]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![85, 0, 0], ![33, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![5, 0, 0], ![-2, 1, 0]] ![![289, 0, 0], ![101, 1, 0]]
  ![![1445, 0, 0], ![-477, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![1445, 0, 0], ![505, 5, 0]], ![![-578, 289, 0], ![-200, 100, 5]]]
 hmul := by decide
 f := ![![![![-29380608362976, -1791943987487246, -87843154542036], ![-16468461702661, 5077334332128780, 0]], ![![3096963015, 0, -11560], ![0, 0, 0]]], ![![![9708816936058, 592147579772333, 29027755178092], ![5442000312759, -1677804249161240, 0]], ![![-1023390891, 0, 3820], ![0, 0, 0]]]]
 g := ![![![![383590955, -107063576460, 1124617904], ![-200716280, -325014850540, -2890]], ![![133395210, -37231750165, 391089988], ![-69799660, -113025102610, -1005]]], ![![![-191733397, 53514515545, -562127516], ![100326350, 162454990266, 1445]], ![![-66343462, 18517133406, -194507791], ![34715830, 56212799400, 500]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![1445, 0, 0], ![-477, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![25, 0, 0], ![8, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![25, 0, 0], ![8, 1, 0]] ![![17, 0, 0], ![-1, 1, 0]]
  ![![425, 0, 0], ![33, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![425, 0, 0], ![-25, 25, 0]], ![![136, 17, 0], ![-6, 8, 5]]]
 hmul := by decide
 f := ![![![![76105078773082, 263170328468, 190904358247559], ![-4461288732031, -649074778278075, 0]], ![![-18013099275, -58472350, -2550], ![0, 0, 0]]], ![![![5819802746173, 20124798831, 14598575105588], ![-341157526313, -49635152318250, 0]], ![![-1377472914, -4471417, -195], ![0, 0, 0]]]]
 g := ![![![![31742692, 544551749, 80082484], ![3746375, -6807005700, -850]], ![![-2799356, -48022957, -7062318], ![-330000, 600296550, 75]]], ![![![9523811, 163383019, 24027318], ![1124244, -2042320398, -255]], ![![-746424, -12804750, -1883083], ![-87874, 160061928, 20]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![425, 0, 0], ![33, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![25, 0, 0], ![8, 1, 0]] ![![289, 0, 0], ![101, 1, 0]]
  ![![7225, 0, 0], ![-3367, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![7225, 0, 0], ![2525, 25, 0]], ![![2312, 289, 0], ![810, 110, 5]]]
 hmul := by decide
 f := ![![![![-4529664973502604196, -276267363011723288321, -13542949530580915766], ![-2538974136108948931, 782782488858028883400, 0]], ![![-599055424879050, -518205105250, -57800], ![0, 0, 0]]], ![![![2111231390361926829, 128765445642186058352, 6312232876892106791], ![1183390367019863998, -364847063076453315072, 0]], ![![279213722200138, 241530199529, 26940], ![0, 0, 0]]]]
 g := ![![![![628947669, -1445290096682, 2146888934], ![-493135150, -3102264243150, -14450]], ![![218719915, -502604919920, 746588483], ![-171487275, -1078823742775, -5025]]], ![![![188706249, -433633714615, 644136029], ![-147952972, -930779481961, -4335]], ![![65732747, -151048084211, 224372575], ![-51535535, -324219388010, -1510]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![7225, 0, 0], ![-3367, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl
