import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_462051_1.RI3_1_462051_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![64, 75, -6]

def alpha1 := B.equivFun.symm ![-19, -5, 1]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-2018, -928, 159]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![-1, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![19, 0, 0], ![-1, 1, 0]] ![![19, 0, 0], ![-1, 1, 0]]
  ![![361, 0, 0], ![-39, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![361, 0, 0], ![-19, 19, 0]], ![![-19, 19, 0], ![1, -2, 1]]]
 hmul := by decide
 f := ![![![![0, 23504, -10583], ![0, -1786, 0]], ![![0, 0, 0], ![3805301, -24548, 0]]], ![![![0, -2542, 1144], ![0, 213, 0]], ![![0, 0, 0], ![-411719, 2656, 0]]]]
 g := ![![![![12949, -332, 0], ![119852, 0, 0]], ![![-661, 56, -1], ![-6118, 361, 0]]], ![![![-661, 56, -1], ![-6118, 361, 0]], ![![43, -1, 0], ![398, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![361, 0, 0], ![-39, 1, 0]] ![![19, 0, 0], ![-1, 1, 0]]
  ![![6859, 0, 0], ![-2205, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![6859, 0, 0], ![-361, 361, 0]], ![![-741, 19, 0], ![39, -40, 1]]]
 hmul := by decide
 f := ![![![![217842265524, -2090378362781, 45436527698], ![2162084485339, 100945927640, 0]], ![![963045577080, -18320491610640, 0], ![-1301412942, -466412, 0]]], ![![![-70032804856, 672023216462, -14607117082], ![-695075588189, -32452501492, 0]], ![![-309603753000, 5889745090440, 0], ![418383450, 149944, 0]]]]
 g := ![![![![14319271, -6494, 0], ![44542346, 0, 0]], ![![-751789, 2546, -1], ![-2338558, 6859, 0]]], ![![![-1545699, 2906, -1], ![-4808140, 6859, 0]], ![![82281, -37, 0], ![255948, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![6859, 0, 0], ![-2205, 1, 0]] ![![19, 0, 0], ![-1, 1, 0]]
  ![![130321, 0, 0], ![-36500, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![130321, 0, 0], ![-6859, 6859, 0]], ![![-41895, 19, 0], ![2205, -2206, 1]]]
 hmul := by decide
 f := ![![![![71465504280922, -1330951544371548, -2892620905141], ![709295129988164, 66136495746610, 0]], ![![106178449999673, -4034787903656021, 0], ![-24726845898, -8861828, 0]]], ![![![-20015923064646, 372770387377332, 810159783731], ![-198658036416594, -18523384448884, 0]], ![![-29738259146160, 1130055753112651, 0], ![6925448160, 2482004, 0]]]]
 g := ![![![![3330698001, -91252, 0], ![11892051892, 0, 0]], ![![-175234579, 41301, -1], ![-625664262, 130321, 0]]], ![![![-1070654495, 65833, -1], ![-3822705874, 130321, 0]], ![![56365605, -1544, 0], ![201249918, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ03 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0) J0
  ![![130321, 0, 0], ![-36500, 1, 0]] ![![19, 0, 0], ![-1, 1, 0]]
  ![![2476099, 0, 0], ![1136389, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![2476099, 0, 0], ![-130321, 130321, 0]], ![![-693500, 19, 0], ![36500, -36501, 1]]]
 hmul := by decide
 f := ![![![![-1506151104045221922, 546015167121134934743, 1489230955815491234], ![-14948549707648827562, -28579988687435485337, 0]], ![![-2568520882230919836, 1952075015409642230052, 0], ![1761576063768, 631405245, 0]]], ![![![-691237894113070730, 250589979492042737692, 683472506165614911], ![-6860536099072226979, -13116593110092844839, 0]], ![![-1178805340878626571, 895891666631867533848, 0], ![808463457198, 289779180, 0]]]]
 g := ![![![![870903529043, 766378, 0], ![-1897627799422, 0, 0]], ![![-45838582903, -1176726, -1], ![99878535684, 2476099, 0]]], ![![![-243922489692, -1351036, -1], ![531487222072, 2476099, 0]], ![![12837188434, 11296, 0], ![-27971187194, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ04 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0) J0
  ![![2476099, 0, 0], ![1136389, 1, 0]] ![![19, 0, 0], ![-1, 1, 0]]
  ![![64, 75, -6]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![47045881, 0, 0], ![-2476099, 2476099, 0]], ![![21591391, 19, 0], ![-1136389, 1136388, 1]]]
 hmul := by decide
 f := ![![![![87374462910732444, -2315329498603926242629, -6397733864193342602], ![867191544389019516, 121518125804043271996, 0]], ![![-90932375253933920, 5058750486548415995516, 0], ![628124, -4052, 0]]]]
 g := ![![![![-109646, 780, 4713]], ![![44219, 3118, -207]]], ![![![-50321, 358, 2163]], ![![20294, 1431, -95]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow6 : J0 ^ 6 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-23, -3, 1]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![2, 0, 0], ![-23, -3, 1]] ![![2, 0, 0], ![-23, -3, 1]]
  ![![-19, -5, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![-46, -6, 2]], ![![-46, -6, 2], ![-401, 77, -1]]]
 hmul := by decide
 f := ![![![![-81, 603, -84], ![159, 0, 0]], ![![0, 0, 0], ![-19, 0, 0]]]]
 g := ![![![![-41, -15, -2]], ![![-226, -83, -11]]], ![![![-226, -83, -11]], ![![-1276, -459, -60]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow2 : J1 ^ 2 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-5602372, -2045851, -271930])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis) 
   timesTableT_eq_Table _ (by norm_num)
  decide

lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-23, -3, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![19, 0, 0], ![-1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![19, 0, 0], ![-1, 1, 0]] ![![2, 0, 0], ![-23, -3, 1]]
  ![![38, 0, 0], ![-17, -3, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![38, 0, 0], ![-437, -57, 19]], ![![-2, 2, 0], ![178, 16, -4]]]
 hmul := by decide
 f := ![![![![4, 60, -38], ![2, 0, 0]], ![![-380, 703, 0], ![0, 0, 0]]], ![![![20, -24, 16], ![1, 0, 0]], ![![170, -313, 0], ![0, 0, 0]]]]
 g := ![![![![52134, 5817, -589], ![-23788, -15390, 0]], ![![-596589, -66564, 6738], ![272365, 176130, 0]]], ![![![-2843, -317, 32], ![1304, 840, 0]], ![![243378, 27155, -2749], ![-111092, -71850, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![38, 0, 0], ![-17, -3, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![361, 0, 0], ![-39, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![361, 0, 0], ![-39, 1, 0]] ![![2, 0, 0], ![-23, -3, 1]]
  ![![722, 0, 0], ![-321, -3, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![722, 0, 0], ![-8303, -1083, 361]], ![![-78, 2, 0], ![1052, 130, -42]]]
 hmul := by decide
 f := ![![![![-127037, 973857, -20371], ![-9948, 0, 0]], ![![-116964, 9149545, 0], ![0, 0, 0]]], ![![![56482, -432864, 9054], ![4423, 0, 0]], ![![52002, -4066845, 0], ![0, 0, 0]]]]
 g := ![![![![119500, -261843, -2683], ![-51262, -662796, 0]], ![![-1364098, 2996679, 30695], ![594567, 7585332, 0]]], ![![![-12881, 28315, 290], ![5636, 71672, 0]], ![![173172, -379777, -3891], ![-74688, -961316, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![722, 0, 0], ![-321, -3, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl

lemma PowJ0_3J1_0 : J0 ^ 3*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![6859, 0, 0], ![-2205, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     
def MulR31_J0_3J1_1 : IdealMulEqCertificate timesTableO (((J0*J0)*J0)) J1
  ![![6859, 0, 0], ![-2205, 1, 0]] ![![2, 0, 0], ![-23, -3, 1]]
  ![![13718, 0, 0], ![-6097, -3, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![13718, 0, 0], ![-157757, -20577, 6859]], ![![-4410, 2, 0], ![50870, 6628, -2208]]]
 hmul := by decide
 f := ![![![![-2756712824, 21330306880, 109436394], ![-238544550, 0, 0]], ![![-41839900, 67464307779, 0], ![0, 0, 0]]], ![![![1225227256, -9480303011, -48639253], ![106021665, 0, 0]], ![![18595850, -29984663790, 0], ![0, 0, 0]]]]
 g := ![![![![-3676715, 171666054, 84852], ![1605006, 388534914, 0]], ![![42117591, -1964622600, -971090], ![-18279235, -4446566238, 0]]], ![![![1186312, -55187344, -27279], ![-506262, -124906528, 0]], ![![-13579080, 633511537, 313137], ![5899140, 1433838238, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_3J1_1 : J0 ^ 3*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![13718, 0, 0], ![-6097, -3, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR31_J0_3J1_1]
 rfl

lemma PowJ0_4J1_0 : J0 ^ 4*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![130321, 0, 0], ![-36500, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02]
 rfl     
def MulR41_J0_4J1_1 : IdealMulEqCertificate timesTableO ((((J0*J0)*J0)*J0)) J1
  ![![130321, 0, 0], ![-36500, 1, 0]] ![![2, 0, 0], ![-23, -3, 1]]
  ![![260642, 0, 0], ![-129559, -3, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![260642, 0, 0], ![-2997383, -390963, 130321]], ![![-73000, 2, 0], ![839655, 109513, -36503]]]
 hmul := by decide
 f := ![![![![-52898176292615, 409381886885414, 2288397211651], ![-4599604357184, 0, 0]], ![![-9733675490, 1486306696718061, 0], ![0, 0, 0]]], ![![![26294437655653, -203494094815534, -1137508360974], ![2286355002895, 0, 0]], ![![4838380855, -738808055646993, 0], ![0, 0, 0]]]]
 g := ![![![![674676026913, -699737447824819, -16205999541], ![-327311486859, -1408097147950727, 0]], ![![-7758755219589, 8046961531127680, 186368551922], ![3764074475100, 16193078728132901, 0]]], ![![![-188961545427, 195980823185459, 4538938340], ![91672902659, 394376546572313, 0]], ![![2173455225046, -2254190233772901, -52207304335], ![-1054427711307, -4536156881385958, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_4J1_1 : J0 ^ 4*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![260642, 0, 0], ![-129559, -3, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR41_J0_4J1_1]
 rfl

lemma PowJ0_5J1_0 : J0 ^ 5*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2476099, 0, 0], ![1136389, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03]
 rfl     
def MulR51_J0_5J1_1 : IdealMulEqCertificate timesTableO (((((J0*J0)*J0)*J0)*J0)) J1
  ![![2476099, 0, 0], ![1136389, 1, 0]] ![![2, 0, 0], ![-23, -3, 1]]
  ![![4952198, 0, 0], ![-1172127, -3, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![4952198, 0, 0], ![-56950277, -7428297, 2476099]], ![![2272778, 2, 0], ![-26136792, -3409154, 1136386]]]
 hmul := by decide
 f := ![![![![-657206665684934319, 5086209524245480360, 28578693355417360], ![-57148284313766960, 0, 0]], ![![3041937143480, -11269218138541734120, 0], ![0, 0, 0]]], ![![![155553085201511103, -1203845951034502929, -6764240465866297], ![13526326501443693, 0, 0]], ![![-719990731020, 2667291341958738600, 0], ![0, 0, 0]]]]
 g := ![![![![11727427929883, -93547990615457514, -239438173562], ![-2719073642672, -395249321103677316, 0]], ![![-134865412877896, 1075801833626755332, 2753538846356], ![31269349366827, 4545366945731127072, 0]]], ![![![5382225153688, -42933221776459736, -109888541055], ![-1247896786662, -181397020377425184, 0]], ![![-61895207996019, 493729095623501102, 1263710659232], ![14350772998590, 2086053249999751380, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_5J1_1 : J0 ^ 5*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4952198, 0, 0], ![-1172127, -3, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR51_J0_5J1_1]
 rfl
