import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF5_3_18225000000_2.RI5_3_18225000000_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![267863, 87239, 721, -21807, -31202]

def v := B.equivFun.symm ![-1, 0, 0, 0, 0]

def zeta1 := B.equivFun.symm ![113, -54, 0, 22, -22]

def zeta2 := B.equivFun.symm ![-28009, -10036, -920, 1530, 2672]

def zeta3 := B.equivFun.symm ![383105, 37964, -30148, -17252, 40006]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![7, -3, -1, 0, 2]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0, 0, 0], ![7, -3, -1, 0, 2]] ![![2, 0, 0, 0, 0], ![7, -3, -1, 0, 2]]
  ![![2, 0, 0, 0, 0], ![7, -2, -1, 0, 2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0, 0, 0], ![14, -6, -2, 0, 4]], ![![14, -6, -2, 0, 4], ![241, 36, -3, -12, 4]]]
 hmul := by decide
 f := ![![![![20947524045, 40428676893, 5536813075, -3658250508, -15963340152], ![-6058427848, 0, 1223933412, -1401696, -93486]], ![![0, 0, 0, 0, 0], ![-15554, 0, -3, 0, 0]]], ![![![3684904402039190, 7111857663117887, 973987513810582, -643527290706539, -2808130557782003], ![-1065745402226931, 0, 215303613251148, -246574039335, -16445141358]], ![![0, 0, 0, 0, 0], ![-2736029863, 0, -527742, 758, 2]]]]
 g := ![![![![-5, 2, 1, 0, -2], ![2, 0, 0, 0, 0]], ![![-11021, -17034, -4185, 2133, 11068], ![-8376, 0, 0, -222, -4]]], ![![![-11021, -17034, -4185, 2133, 11068], ![-8376, 0, 0, -222, -4]], ![![-8930, -13801, -3388, 1728, 8969], ![-6781, 0, 0, -180, -4]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![2, 0, 0, 0, 0], ![7, -2, -1, 0, 2]] ![![2, 0, 0, 0, 0], ![7, -3, -1, 0, 2]]
  ![![4, 0, 0, 0, 0], ![-5, 3, 1, -1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![4, 0, 0, 0, 0], ![14, -6, -2, 0, 4]], ![![14, -4, -2, 0, 4], ![97, 16, -1, -6, 4]]]
 hmul := by decide
 f := ![![![![-2289061477417, -4417880599235, -605040533398, 399758353770, 1744410193246], ![662036187858, 0, -133745903142, 153036792, 9248205]], ![![0, 0, 0, 0, 0], ![1483052, 0, 0, -1296, -18]]], ![![![3046749604772, 5880216019747, 805311270228, -532079901904, -2321816656865], ![-881172704883, 0, 178016309985, -203692557, -12309396]], ![![0, 0, 0, 0, 0], ![-1973947, 0, 0, 1725, 24]]]]
 g := ![![![![4308733453, 6902589133, 10261060642, 14612872141, -30021650577], ![-1296927840, -10173642592, -51460224, 3438280, -18996]], ![![15786900524, 25290607832, 37595814522, 53540550035, -109997245529], ![-4751853654, -37275520853, -188546691, 12597620, -69600]]], ![![![15789620122, 25294964630, 37602291123, 53549773420, -110016194663], ![-4752672254, -37281942276, -188579172, 12599790, -69612]], ![![104864428915, 167992769893, 249730060064, 355642907154, -730656299873], ![-31564170489, -247602510510, -1252420710, 83679639, -462318]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![4, 0, 0, 0, 0], ![-5, 3, 1, -1, 0]] ![![2, 0, 0, 0, 0], ![7, -3, -1, 0, 2]]
  ![![4, 0, 0, 0, 0], ![29, 5, -1, -1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![8, 0, 0, 0, 0], ![28, -12, -4, 0, 8]], ![![-10, 6, 2, -2, 0], ![-107, -53, -1, 5, 14]]]
 hmul := by decide
 f := ![![![![-533774163864499567866187, -1029546353205375520785325, -141121961750204399356201, 93190839776975913233453, 406633793457068742790772], ![153304730614485736115210, 0, -31112925693285677586149, 15456136121908010074, 213285565084501952]], ![![-1881262236002545044, 0, 0, -1450477924722387, 2670518676105], ![-4725168116, 0, -2186271, -554, 18]]], ![![![-3919520042354306380722448, -7559990421240465109978588, -1036262889705351159972234, 684303192243694637657830, 2985924406334017318524028], ![1125721334807318230949480, 0, -228463166797391722493045, 113494881184532966405, 1566162440387026524]], ![![-13814166248795957706, 0, 0, -10650903850013016, 19609700474623], ![-34697054275, 0, -16053855, -4068, 132]]]]
 g := ![![![![-296585333, 1775027763, 497455307, -354217543, -731489448], ![32731724, -244594272, 0, 550888, -23952]], ![![-1086185983, 6500693457, 1821833169, -1297252760, -2678937628], ![119873560, -895778880, 0, 2017520, -87720]]], ![![![394948896, -2363722156, -662438160, 471695075, 974090574], ![-43587314, 325714848, 0, -733592, 31896]], ![![3958981739, -23694033943, -6640303398, 4728288009, 9764318129], ![-436920779, 3264977088, 0, -7353552, 319722]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ03 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0) J0
  ![![4, 0, 0, 0, 0], ![29, 5, -1, -1, 0]] ![![2, 0, 0, 0, 0], ![7, -3, -1, 0, 2]]
  ![![267863, 87239, 721, -21807, -31202]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![8, 0, 0, 0, 0], ![28, -12, -4, 0, 8]], ![![58, 10, -2, -2, 0], ![-157, -33, -3, 5, 10]]]
 hmul := by decide
 f := ![![![![37577148070626862316380756, 72478944760515941745314860, 9934897996361343974321249, -6560585887927382981289295, -28626564423914564665875196], ![-10792412315675131163675452, 0, 2190306365767088544828097, -1079589039062366751716, -9177606188400824209]], ![![193411477304548871169, 0, 0, 149418785886603129, -2172633983311085], ![2636009667455, 0, 0, 988912566, 1204302]]]]
 g := ![![![![-19880, -1609, 1506, 750, -1880]], ![![24068, -2978, -1081, 1176, -492]]], ![![![82598, -2816, -4828, 908, 2468]], ![![180325, 14827, -13695, -6902, 17184]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow5 : J0 ^ 5 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-9487, -3242, -280, 514, 826])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-276889, 1012, 11072, 12390, -23912])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta3 : IsUnit zeta3 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-3198898752415, -1041910152748, -8679201204, 260365018060, 372576911846])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![7, -3, -1, 0, 2]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![7, -2, -1, 0, 2]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     

lemma PowJ0_3 : J0 ^ 3 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0, 0, 0], ![-5, 3, 1, -1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     

lemma PowJ0_4 : J0 ^ 4 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0, 0, 0], ![29, 5, -1, -1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02]
 rfl     
