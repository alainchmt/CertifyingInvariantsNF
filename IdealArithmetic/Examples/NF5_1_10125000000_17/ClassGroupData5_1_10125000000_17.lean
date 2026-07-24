import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF5_1_10125000000_17.RI5_1_10125000000_17

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-19939143752836442, -872556877448547, 96994111614622, -949739541230382, -1057766086864789]

def v := B.equivFun.symm ![-1, 0, 0, 0, 0]

def zeta1 := B.equivFun.symm ![31, 17, -3, 2, 4]

def zeta2 := B.equivFun.symm ![-4295384860860502876347593465084835629, 7985121332494519147874150758241985881, -2952269487519506460585879238362277861, 1275467727902054332373616598638592896, 48156740590741678429992868441786652]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![1, 1, 1, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0, 0, 0], ![1, 1, 1, 1, 0]] ![![2, 0, 0, 0, 0], ![1, 1, 1, 1, 0]]
  ![![2, 0, 0, 0, 0], ![1, 2, 0, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0, 0, 0], ![2, 2, 2, 2, 0]], ![![2, 2, 2, 2, 0], ![61, -54, -18, 7, 6]]]
 hmul := by decide
 f := ![![![![-31126641, 77465234, -21000481, 75140011, 65037852], ![50239064, -65155125, 0, 410520, 264255]], ![![0, 0, 0, 0, 0], ![-9722, -90, 0, 3, 0]]], ![![![45925716566, -114295848229, 30985103690, -110865169633, -95959905165], ![-74125098801, 96132938877, 0, -605700522, -389901651]], ![![0, 0, 0, 0, 0], ![14344559, 132928, 0, -4407, -2]]]]
 g := ![![![![2, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![-48, 50, 0, 17, 33], ![38, -32, 0, 0, 2]]], ![![![-48, 50, 0, 17, 33], ![38, -32, 0, 0, 2]], ![![1334, -1425, 0, -466, -924], ![-987, 900, 0, 0, -54]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![2, 0, 0, 0, 0], ![1, 2, 0, 1, 0]] ![![2, 0, 0, 0, 0], ![1, 1, 1, 1, 0]]
  ![![4, 0, 0, 0, 0], ![1, 2, 0, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![4, 0, 0, 0, 0], ![2, 2, 2, 2, 0]], ![![2, 4, 0, 2, 0], ![31, -16, -18, 7, 4]]]
 hmul := by decide
 f := ![![![![-1869, 4551, -1277, 4757, 3829], ![3082, -3852, 0, 24, 54]], ![![0, 0, 0, 0, 0], ![-4, 0, 0, 0, 0]]], ![![![-47006421, 116295464, -31917155, 115461247, 97681872], ![76416568, -97981131, 0, 611727, 696933]], ![![0, 0, 0, 0, 0], ![-47221, -786, 0, 0, 2]]]]
 g := ![![![![-1302, 1328, 0, -188, 19], ![292, -44, 164, 6, 0]], ![![43604, -44494, 0, 6279, -681], ![-9774, 1558, -5490, -195, 2]]], ![![![88559, -90364, 0, 12753, -1382], ![-19854, 3162, -11150, -396, 4]], ![![-355775, 363019, 0, -51237, 5541], ![79761, -12681, 44795, 1593, -16]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![4, 0, 0, 0, 0], ![1, 2, 0, 1, 0]] ![![2, 0, 0, 0, 0], ![1, 1, 1, 1, 0]]
  ![![4, 0, 0, 0, 0], ![-1, 0, 0, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![8, 0, 0, 0, 0], ![4, 4, 4, 4, 0]], ![![2, 4, 0, 2, 0], ![31, -16, -18, 7, 4]]]
 hmul := by decide
 f := ![![![![1337909263436, 1286433194359, 1232069957836, 1333331258759, 42121959756], ![-2546596118872, -41959150866, 0, -4307413600, -307672400]], ![![-32162966, -17463957, 0, 0, 1049925], ![41576, 882, 0, 21, 0]]], ![![![-445979961830, -428820879411, -410699385814, -444453925345, -14040974615], ![848884801780, 13986703743, 0, 1435837396, 102559814]], ![![10721234, 5821452, 0, 0, -349983], ![-13859, -294, 0, -7, 0]]]]
 g := ![![![![2, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![-760, 1044, 0, 9, 23], ![196, -44, 108, 0, 4]]], ![![![-761, 1044, 0, 8, 21], ![194, -40, 108, 0, 4]], ![![3055, -4176, 0, -34, -92], ![-771, 178, -432, 0, -16]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ03 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0) J0
  ![![4, 0, 0, 0, 0], ![-1, 0, 0, 1, 0]] ![![2, 0, 0, 0, 0], ![1, 1, 1, 1, 0]]
  ![![-19939143752836442, -872556877448547, 96994111614622, -949739541230382, -1057766086864789]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![8, 0, 0, 0, 0], ![4, 4, 4, 4, 0]], ![![-2, 0, 0, 2, 0], ![29, -24, -20, -1, 0]]]
 hmul := by decide
 f := ![![![![-495432423868312083444432, -476375713172187513558571, -456246887163516363917752, -493739071836646414196016, -15583781456539495993224], ![943022041294722416303964, 15541312635145862708194, 0, 1594760214730058352830, 113911443909289882345]], ![![1084388345996238930, -29544313100432469092, 0, 0, -1471727402878219428], ![72292556399749262, 316835140625437183, 0, 0, -872556877448547]]]]
 g := ![![![![322080326, -307849883, -122196483, -15294958, 29623454]], ![![-1901331452, 1983972354, 276718810, -765452199, -537431122]]], ![![![-996993704, 981434556, 302238582, -98957196, -153683326]], ![![2550723938, -3023829123, 595279836, 2887004452, 1509070057]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow5 : J0 ^ 5 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-29, 21, 29, 36, 12])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![2477525262805708468802905859622830116575201031605206463961231, 108418983979997255831765033762583768364598269284080374018797, -12051939885053328353498969036651499432195859919376318730293, 118009265375252040870300184501030988199553323674656950216962, 131432033132007124394154076233743832633779632265363190012284])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![1, 1, 1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![1, 2, 0, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     

lemma PowJ0_3 : J0 ^ 3 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0, 0, 0], ![1, 2, 0, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     

lemma PowJ0_4 : J0 ^ 4 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0, 0, 0], ![-1, 0, 0, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02]
 rfl     
