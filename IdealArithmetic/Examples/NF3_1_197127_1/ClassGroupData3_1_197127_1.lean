import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_197127_1.RI3_1_197127_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![29, 3, 2]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-1, 3, -1]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![2, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![5, 0, 0], ![2, 1, 0]] ![![5, 0, 0], ![2, 1, 0]]
  ![![25, 0, 0], ![2, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![25, 0, 0], ![10, 5, 0]], ![![10, 5, 0], ![3, 3, 3]]]
 hmul := by decide
 f := ![![![![51070, -59040, -168924], ![8625, 279000, 0]], ![![0, 0, 0], ![12800, -25, 0]]], ![![![2051, -2372, -6786], ![348, 11208, 0]], ![![0, 0, 0], ![514, -1, 0]]]]
 g := ![![![![-116, 117, 351], ![0, -2925, 0]], ![![-45, 45, 135], ![5, -1125, 0]]], ![![![-45, 45, 135], ![5, -1125, 0]], ![![-13, 13, 39], ![2, -324, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![25, 0, 0], ![2, 1, 0]] ![![5, 0, 0], ![2, 1, 0]]
  ![![125, 0, 0], ![27, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![125, 0, 0], ![50, 25, 0]], ![![10, 5, 0], ![3, 3, 3]]]
 hmul := by decide
 f := ![![![![698023390, -776172930, -2250369024], ![123974775, 3750333500, 0]], ![![31349000, 1395000, 0], ![64000, -125, 0]]], ![![![145212937, -161470736, -468154362], ![25791028, 780198700, 0]], ![![6521673, 290208, 0], ![13314, -26, 0]]]]
 g := ![![![![-2991, 77792, 8976], ![0, -374000, 0]], ![![-1195, 30940, 3570], ![25, -148750, 0]]], ![![![-239, 6188, 714], ![5, -29750, 0]], ![![-93, 1845, 213], ![102, -8874, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![125, 0, 0], ![27, 1, 0]] ![![5, 0, 0], ![2, 1, 0]]
  ![![625, 0, 0], ![27, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![625, 0, 0], ![250, 125, 0]], ![![135, 5, 0], ![53, 28, 3]]]
 hmul := by decide
 f := ![![![![-30809432263418, 34125304107041, 99078769383726], ![-5498712083955, -165131549700000, 0]], ![![-80274660000, 6684935000, 0], ![-433125, -625, 0]]], ![![![-1281885695250, 1419848921810, 4122362791041], ![-228784493733, -6870615777168, 0]], ![![-3339981648, 278139580, 0], ![-18021, -26, 0]]]]
 g := ![![![![-189366, 4923542, 568101], ![0, -118354375, 0]], ![![-75670, 1967290, 226995], ![125, -47290625, 0]]], ![![![-40900, 1063400, 122700], ![5, -25562500, 0]], ![![-16040, 417040, 48120], ![2, -10024999, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ03 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0) J0
  ![![625, 0, 0], ![27, 1, 0]] ![![5, 0, 0], ![2, 1, 0]]
  ![![3125, 0, 0], ![-598, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![3125, 0, 0], ![1250, 625, 0]], ![![135, 5, 0], ![53, 28, 3]]]
 hmul := by decide
 f := ![![![![-15060741229841250, 16676009854666875, 48414370768106226], ![-2689094521003125, -80690617397225000, 0]], ![![-40383127050000, -68701887500, 0], ![-2165625, -3125, 0]]], ![![![2886822016765738, -3196434469298841, -9279999525143019], ![515441912846532, 15466665769888212, 0]], ![![7740581854152, 13168682630, 0], ![415104, 599, 0]]]]
 g := ![![![![-4915616, -2944454583, 14746851], ![0, -15361303125, 0]], ![![-1965795, -1177583085, 5897745], ![625, -6143484375, 0]]], ![![![-212351, -127198848, 637056], ![5, -663600000, 0]], ![![-83234, -49929046, 250062], ![627, -260481249, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ04 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0) J0
  ![![3125, 0, 0], ![-598, 1, 0]] ![![5, 0, 0], ![2, 1, 0]]
  ![![29, 3, 2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![15625, 0, 0], ![6250, 3125, 0]], ![![-2990, 5, 0], ![-1197, -597, 3]]]
 hmul := by decide
 f := ![![![![1448277245104475455, -1603479057443637266, -4655268899574810232], ![258615086553062731, 7758781497587120112, 0]], ![![-172555040619450, 1065143909664, 0], ![44518, -26, 0]]]]
 g := ![![![![1007, 22, -47]], ![![-410, 140, -15]]], ![![![-194, -4, 9]], ![![78, -27, 3]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow6 : J0 ^ 6 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![146, 28, 13])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis) 
   timesTableT_eq_Table _ (by norm_num)
  decide

lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![5, 0, 0], ![2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![25, 0, 0], ![2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     

lemma PowJ0_3 : J0 ^ 3 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![125, 0, 0], ![27, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     

lemma PowJ0_4 : J0 ^ 4 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![625, 0, 0], ![27, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02]
 rfl     

lemma PowJ0_5 : J0 ^ 5 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3125, 0, 0], ![-598, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03]
 rfl     
