import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF5_1_2025000000_5.RI5_1_2025000000_5

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![3, -30, 3, -4, 3]

def v := B.equivFun.symm ![-1, 0, 0, 0, 0]

def zeta1 := B.equivFun.symm ![94349, 49754, 42647, 22399, 6349]

def zeta2 := B.equivFun.symm ![-4436583, -499539, -81866, 425045, 249983]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![-7, 2, 0, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0, 0, 0], ![-7, 2, 0, 1, 0]] ![![2, 0, 0, 0, 0], ![-7, 2, 0, 1, 0]]
  ![![2, 0, 0, 0, 0], ![-3, 1, 1, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0, 0, 0], ![-14, 4, 0, 2, 0]], ![![-14, 4, 0, 2, 0], ![-9, -13, 1, -1, 2]]]
 hmul := by decide
 f := ![![![![844991547, 1987909410, -115671560, 508077496, -282204437], ![-715522250, 347014680, -108846475, 6673053, 0]], ![![0, 0, 0, 0, 0], ![-298756, 2495, -157, -1, 0]]], ![![![-2545810389, -5989220206, 348497995, -1530747825, 850232162], ![2155742261, -1045493985, 327935219, -20104731, 0]], ![![0, 0, 0, 0, 0], ![900099, -7517, 473, 3, 0]]]]
 g := ![![![![52, 36, 22, 0, 0], ![-44, 8, -4, 0, 0]], ![![-223, -163, -102, -2, 0], ![204, -36, 18, 0, 0]]], ![![![-223, -163, -102, -2, 0], ![204, -36, 18, 0, 0]], ![![47, 31, 20, -3, 0], ![-43, 10, -4, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![2, 0, 0, 0, 0], ![-3, 1, 1, 1, 0]] ![![2, 0, 0, 0, 0], ![-7, 2, 0, 1, 0]]
  ![![4, 0, 0, 0, 0], ![-17, -15, 1, -1, 2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![4, 0, 0, 0, 0], ![-14, 4, 0, 2, 0]], ![![-6, 2, 2, 2, 0], ![21, 4, 1, 2, -1]]]
 hmul := by decide
 f := ![![![![-17699730, -41614863, 2417311, -10619553, 5906996], ![15024442, -7251933, 2286228, -141231, 0]], ![![0, 0, 0, 0, 0], ![-20188, 336, -6, 0, 0]]], ![![![131974833, 310293553, -18024234, 79182738, -44044429], ![-112026979, 54072702, -17046839, 1053063, 0]], ![![0, 0, 0, 0, 0], ![150527, -2505, 45, 0, 0]]]]
 g := ![![![![3380095374476, -3525351054249, -40903289900, -1077723582654, 309710967814], ![-731278330968, -223724739690, 746830, 18, 0]], ![![-11834995329051, 12343590531655, 143217924725, 3773518837092, -1084415512394], ![2560482670588, 783345129615, -2614935, -63, 0]]], ![![![-5635055160410, 5877215122562, 68191062468, 1796704282904, -516328148786], ![1219135342674, 372978010746, -1245062, -30, 0]], ![![17459555316404, -18209859463205, -211281982758, -5566876795618, 1599782010733], ![-3777347399025, -1155628476570, 3857678, 93, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![4, 0, 0, 0, 0], ![-17, -15, 1, -1, 2]] ![![2, 0, 0, 0, 0], ![-7, 2, 0, 1, 0]]
  ![![4, 0, 0, 0, 0], ![-3, 1, 1, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![8, 0, 0, 0, 0], ![-28, 8, 0, 4, 0]], ![![-34, -30, 2, -2, 4], ![119, 4, -9, -14, -1]]]
 hmul := by decide
 f := ![![![![786577770759592667, 2118659406306717352, -211241206356155184, 552093542692865611, -312684751670559457], ![-358316020005424152, 492896148164362096, -66271319256254724, 4107427403523325, 0]], ![![-69187466535282, 198598893507, -428831709, 0, 0], ![2415986, -51213, 681, -3, 0]]], ![![![-783047209354170095, -2109149784487734938, 210293048299672440, -549615465856124959, 311281263347661474], ![356707715323797938, -490683779365902360, 65973859843148476, -4088991178644442, 0]], ![![68876917968864, -197707480586, 426906894, 0, 0], ![-2405141, 50984, -678, 3, 0]]]]
 g := ![![![![2, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![76, 27, 11, -10, 0], ![-44, 16, -8, 0, 0]]], ![![![-318, -113, -53, 34, 0], ![206, -60, 32, 0, 0]], ![![147, 47, 22, -15, 0], ![-95, 25, -13, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ03 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0) J0
  ![![4, 0, 0, 0, 0], ![-3, 1, 1, 1, 0]] ![![2, 0, 0, 0, 0], ![-7, 2, 0, 1, 0]]
  ![![3, -30, 3, -4, 3]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![8, 0, 0, 0, 0], ![-28, 8, 0, 4, 0]], ![![-6, 2, 2, 2, 0], ![21, 4, 1, 2, -1]]]
 hmul := by decide
 f := ![![![![589840035830, 1584519423535, -157293134730, 412354802153, -233727062785], ![-273743300785, 367017314370, -50176057205, 3159005745, 0]], ![![1469715633, 186014537, -8388891, 0, 0], ![-304503, 5070, -90, 0, 0]]]]
 g := ![![![![22, -18, -1, -11, 3]], ![![126, -39, -1, -35, 4]]], ![![![-118, -2, -2, 16, 4]], ![![-225, -47, -6, 12, 17]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow5 : J0 ^ 5 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-6540991, 13889124, -1249807, 2240413, -1315887])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![1728271045, 771064391, 677595114, 313890231, 96712103])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![-7, 2, 0, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![-3, 1, 1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     

lemma PowJ0_3 : J0 ^ 3 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0, 0, 0], ![-17, -15, 1, -1, 2]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     

lemma PowJ0_4 : J0 ^ 4 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0, 0, 0], ![-3, 1, 1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02]
 rfl     
