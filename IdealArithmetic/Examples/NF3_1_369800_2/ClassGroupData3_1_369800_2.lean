import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_369800_2.RI3_1_369800_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-408, -21, 7]

def alpha1 := B.equivFun.symm ![4682, 1325, 200]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-27964, 2487, -74]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-45, -4, 1]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0], ![-45, -4, 1]] ![![2, 0, 0], ![-45, -4, 1]]
  ![![2, 0, 0], ![-46, -3, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![-90, -8, 2]], ![![-90, -8, 2], ![-376, -9, 5]]]
 hmul := by decide
 f := ![![![![-28123, 112382, -21398], ![397951, 0, -16020]], ![![0, 0, 0], ![-1068, 0, 3]]], ![![![788177, -3146308, 599066], ![-11141474, 0, 448515]], ![![0, 0, 0], ![29901, 0, -84]]]]
 g := ![![![![2, 0, 0], ![0, 0, 0]], ![![1, -1, 0], ![2, 0, 0]]], ![![![1, -1, 0], ![2, 0, 0]], ![![19, 9, -2], ![9, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![2, 0, 0], ![-46, -3, 1]] ![![2, 0, 0], ![-45, -4, 1]]
  ![![-408, -21, 7]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![4, 0, 0], ![-90, -8, 2]], ![![-92, -6, 2], ![-8, 21, -3]]]
 hmul := by decide
 f := ![![![![-1131, 4494, -875], ![17031, 0, -693]], ![![0, 0, 0], ![21, 0, 0]]]]
 g := ![![![![-1311, -371, -56]], ![![633, 179, 27]]], ![![![-8053, -2279, -344]], ![![3882, 1099, 166]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![-3, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![7, 0, 0], ![-3, 1, 0]] ![![7, 0, 0], ![-3, 1, 0]]
  ![![49, 0, 0], ![-24, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![49, 0, 0], ![-21, 7, 0]], ![![-21, 7, 0], ![10, -6, 2]]]
 hmul := by decide
 f := ![![![![-1844733, 8884298, -6194060], ![2059792, 21950334, 0]], ![![0, 0, 0], ![-1905218, -1470, 0]]], ![![![911076, -4387755, 3059106], ![-1017275, -10840773, 0]], ![![0, 0, 0], ![940944, 726, 0]]]]
 g := ![![![![-9, 815, -68], ![49, 1666, 0]], ![![20, -408, 34], ![7, -833, 0]]], ![![![20, -408, 34], ![7, -833, 0]], ![![0, 216, -18], ![18, 442, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![49, 0, 0], ![-24, 1, 0]] ![![7, 0, 0], ![-3, 1, 0]]
  ![![4682, 1325, 200]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![343, 0, 0], ![-147, 49, 0]], ![![-168, 7, 0], ![73, -27, 2]]]
 hmul := by decide
 f := ![![![![-851682178259, 4118506032656, -2895923285574], ![953364652492, 10162852562499, 0]], ![![383138102060, -189824193538, 0], ![-166176904, -132510, 0]]]]
 g := ![![![![4824, 725, -150]], ![![-8971, -1143, 250]]], ![![![-3349, -474, 100]], ![![6039, 739, -164]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-227752458, -64451023, -9728168])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![7, 0, 0], ![-3, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![49, 0, 0], ![-24, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-45, -4, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![2, 0, 0], ![-45, -4, 1]] ![![7, 0, 0], ![-3, 1, 0]]
  ![![14, 0, 0], ![-41, -4, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![14, 0, 0], ![-6, 2, 0]], ![![-315, -28, 7], ![458, 38, -10]]]
 hmul := by decide
 f := ![![![![-989, 5295, -3631], ![1183, 12684, 0]], ![![14, 0, 0], ![0, 0, 0]]], ![![![2198281, -11759219, 8063214], ![-2622007, -28166682, 0]], ![![-31093, 0, -4], ![0, 0, 0]]]]
 g := ![![![![2038, 108, 3], ![-5922, -840, 0]], ![![315877, 16590, 555], ![-929638, -131688, 2]]], ![![![-4479131, -235218, -7885], ![13184129, 1867572, -28]], ![![6083243, 319458, 10708], ![-17905654, -2536392, 38]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![14, 0, 0], ![-41, -4, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![2, 0, 0], ![-45, -4, 1]] ![![49, 0, 0], ![-24, 1, 0]]
  ![![98, 0, 0], ![-69, -4, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![98, 0, 0], ![-48, 2, 0]], ![![-2205, -196, 49], ![1403, 122, -31]]]
 hmul := by decide
 f := ![![![![-42154, 1719186, -143393], ![55762, 3511928, 0]], ![![98, 0, 0], ![0, 0, 0]]], ![![![93551513, -3814296920, 318140897], ![-123663942, -7791787344, 0]], ![![-217433, 0, -4], ![0, 0, 0]]]]
 g := ![![![![88616, -1720, -2235], ![-62230, -40180, 0]], ![![1945487, -37850, -49080], ![-1368692, -882648, 2]]], ![![![-196899220, 3830904, 4967322], ![138527459, 89332194, -196]], ![![122587291, -2385078, -3092600], ![-86245653, -55617238, 122]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![98, 0, 0], ![-69, -4, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-46, -3, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![2, 0, 0], ![-46, -3, 1]] ![![7, 0, 0], ![-3, 1, 0]]
  ![![14, 0, 0], ![-44, -3, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![14, 0, 0], ![-6, 2, 0]], ![![-322, -21, 7], ![462, 34, -8]]]
 hmul := by decide
 f := ![![![![-2, 17, -12], ![7, 42, 0]], ![![0, 0, 0], ![0, 0, 0]]], ![![![230, -1222, 839], ![-272, -2931, 0]], ![![-3, 0, 0], ![0, 0, 0]]]]
 g := ![![![![253, 54, 12], ![-693, -105, 0]], ![![-101, -26, -7], ![373, 55, 0]]], ![![![-4841, -1140, -280], ![15477, 2310, 0]], ![![6929, 1628, 399], ![-22069, -3295, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![14, 0, 0], ![-44, -3, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![2, 0, 0], ![-46, -3, 1]] ![![49, 0, 0], ![-24, 1, 0]]
  ![![98, 0, 0], ![-44, -3, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![98, 0, 0], ![-48, 2, 0]], ![![-2254, -147, 49], ![1428, 97, -29]]]
 hmul := by decide
 f := ![![![![-9, 815, -68], ![49, 1666, 0]], ![![0, 0, 0], ![0, 0, 0]]], ![![![1365, -54791, 4570], ![-1735, -111928, 0]], ![![-3, 0, 0], ![0, 0, 0]]]]
 g := ![![![![61421, 5307, -857], ![-27734, -22344, 0]], ![![-30120, -2603, 420], ![13680, 10968, 0]]], ![![![-1407709, -121635, 19641], ![635971, 512148, 0]], ![![891732, 77051, -12442], ![-402813, -324420, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![98, 0, 0], ![-44, -3, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl
