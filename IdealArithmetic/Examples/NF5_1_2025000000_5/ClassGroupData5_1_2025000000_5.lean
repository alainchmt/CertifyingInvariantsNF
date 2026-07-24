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
  ![![4, 0, 0, 0, 0], ![-7, -15, 3, -1, 2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![4, 0, 0, 0, 0], ![-14, 4, 0, 2, 0]], ![![-6, 2, 2, 2, 0], ![21, 4, 1, 2, -1]]]
 hmul := by decide
 f := ![![![![-17699730, -41614863, 2417311, -10619553, 5906996], ![15024442, -7251933, 2286228, -141231, 0]], ![![0, 0, 0, 0, 0], ![-20188, 336, -6, 0, 0]]], ![![![78877515, 185453421, -10772560, 47325218, -26324073], ![-66955261, 32317680, -10188399, 629385, 0]], ![![0, 0, 0, 0, 0], ![89965, -1497, 27, 0, 0]]]]
 g := ![![![![2181696113327, -895731287284, 170250305551, -234611434365, 91269099908], ![-227000733276, -88928976210, 488686, 18, 0]], ![![-7646749206943, 3139498882954, -596719855260, 822302789430, -319894192910], ![795627615856, 311692161963, -1712823, -63, 0]]], ![![![-3639755530135, 1494361605415, -284031074427, 391405686819, -152265574062], ![378708642898, 148361511474, -815282, -30, 0]], ![![11262196003786, -4623880137346, 878853979302, -1211094406049, 471142835144], ![-1171806987943, -459062815566, 2522660, 93, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![4, 0, 0, 0, 0], ![-7, -15, 3, -1, 2]] ![![2, 0, 0, 0, 0], ![-7, 2, 0, 1, 0]]
  ![![4, 0, 0, 0, 0], ![-3, 1, 1, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![8, 0, 0, 0, 0], ![-28, 8, 0, 4, 0]], ![![-14, -30, 6, -2, 4], ![165, 28, -7, -10, -5]]]
 hmul := by decide
 f := ![![![![176240900866044667762, 474768719736631103127, -47346737248962723465, 123723714598500319519, -70070373108847388909], ![-80212575995275074252, 110475720247579688085, -14840246775475632508, 918830261084267868, 0]], ![![-15445751307099960, 44341342212321, -85413048849, 0, 0], ![411030974, -1427001, 4821, -3, 0]]], ![![![-176131104203248118465, -474472942645325304496, 47317240612718266161, -123646635720073380653, 70026719830349294411], ![80162604206006419821, -110406894763009287709, 14831001421173551742, -918257837226651446, 0]], ![![15436128728347971, -44313717912996, 85359837207, 0, 0], ![-410774905, 1426112, -4818, 3, 0]]]]
 g := ![![![![2, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![76, 27, 11, -10, 0], ![-44, 16, -8, 0, 0]]], ![![![-353, -126, -58, 39, 0], ![230, -68, 36, 0, 0]], ![![371, 125, 60, -37, 0], ![-237, 65, -35, 0, 0]]]]
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

lemma PowJ0_3 : J0 ^ 3 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0, 0, 0], ![-7, -15, 3, -1, 2]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     

lemma PowJ0_4 : J0 ^ 4 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0, 0, 0], ![-3, 1, 1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02]
 rfl     
