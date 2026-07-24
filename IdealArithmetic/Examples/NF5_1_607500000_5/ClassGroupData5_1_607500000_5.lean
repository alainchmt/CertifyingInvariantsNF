import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF5_1_607500000_5.RI5_1_607500000_5

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![515, -169, -6, -80, -17]

def v := B.equivFun.symm ![-1, 0, 0, 0, 0]

def zeta1 := B.equivFun.symm ![732565, -518780, 105501, -76167, 48164]

def zeta2 := B.equivFun.symm ![-43063, 19747, -1913, 6064, -38]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![7, -5, 2, 0, 1]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0, 0, 0], ![7, -5, 2, 0, 1]] ![![2, 0, 0, 0, 0], ![7, -5, 2, 0, 1]]
  ![![4, 0, 0, 0, 0], ![9, -5, 2, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0, 0, 0], ![14, -10, 4, 0, 2]], ![![14, -10, 4, 0, 2], ![19, -24, 11, 4, 7]]]
 hmul := by decide
 f := ![![![![857052, 679556, -409540, 0, -598009], ![592264, -963704, 314988, -10708, 0]], ![![0, 0, 0, 0, 0], ![-1348, -24, -4, 0, 0]]], ![![![1654588, 1311923, -790635, 0, -1154480], ![1143394, -1860479, 608097, -20675, 0]], ![![0, 0, 0, 0, 0], ![-2601, -47, -7, 0, 0]]]]
 g := ![![![![3745, 3683, -1754, 0, -1660], ![2536, -6264, 2088, -36, 0]], ![![8864, 8720, -4154, 0, -3931], ![6006, -14832, 4944, -84, 0]]], ![![![8864, 8720, -4154, 0, -3931], ![6006, -14832, 4944, -84, 0]], ![![7174, 7058, -3365, 0, -3184], ![4865, -12011, 4005, -66, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![4, 0, 0, 0, 0], ![9, -5, 2, 0, 1]] ![![2, 0, 0, 0, 0], ![7, -5, 2, 0, 1]]
  ![![515, -169, -6, -80, -17]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![8, 0, 0, 0, 0], ![28, -20, 8, 0, 4]], ![![18, -10, 4, 0, 2], ![33, -34, 15, 4, 9]]]
 hmul := by decide
 f := ![![![![-116736590431, -99057828505, 48352941454, 0, 71961019024], ![-76600044254, 126303521910, -38254401780, 5770158285, 0]], ![![-4878983685, -267482790, 89378280, -2636454, 0], ![-330143, -7045, 1879, 80, 0]]]]
 g := ![![![![-2395984, 1333210, -1050089, -526014, -617933]], ![![-5964356, 3318778, -2614001, -1309414, -1538229]]], ![![![-4180170, 2325994, -1832045, -917714, -1078081]], ![![-10405755, 5790129, -4560535, -2284478, -2683682]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-42117, 23900, -46157, 69239, -52194])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![13145817655579315, -7314796502938757, 5761423464721343, 2886031062176506, 3390354069449008])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![7, -5, 2, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0, 0, 0], ![9, -5, 2, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
