import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_959175_1.RI3_1_959175_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-1379721215357, -401354532686, -60476501207]

def alpha1 := B.equivFun.symm ![-304499617, -88577533, -13346951]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![14788779351151, -35753534905620, 6129394308642]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-35, -2, 1]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0], ![-35, -2, 1]] ![![2, 0, 0], ![-35, -2, 1]]
  ![![4, 0, 0], ![-33, -2, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![-70, -4, 2]], ![![-70, -4, 2], ![-175, 50, -5]]]
 hmul := by decide
 f := ![![![![-139, 82, -436], ![2382, 300, 0]], ![![0, 0, 0], ![4, 0, 0]]], ![![![107888, -57151, 306843], ![-1677248, -211317, 0]], ![![0, 0, 0], ![-2833, -2, 0]]]]
 g := ![![![![33, 2, 6], ![-64, -8, 0]], ![![-116, -8, -115], ![1142, 136, 0]]], ![![![-116, -8, -115], ![1142, 136, 0]], ![![-398, -12, -339], ![3351, 400, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![4, 0, 0], ![-33, -2, 1]] ![![2, 0, 0], ![-35, -2, 1]]
  ![![-1379721215357, -401354532686, -60476501207]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![8, 0, 0], ![-140, -8, 4]], ![![-66, -4, 2], ![-245, 46, -3]]]
 hmul := by decide
 f := ![![![![72165583685554819680, -63622446711965456169, 202598255847815448013], ![-1097976139861336164014, -136612751925388584055, 0]], ![![19315531404544310667, -23143386157885869, 0], ![-338517528671597, -401354532686, 0]]]]
 g := ![![![![-13630544, -844478, 346859]], ![![-25373180, 9031254, -1235487]]], ![![![-19501862, 4093388, -444314]], ![![1100968785, 47980702, -24427541]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-35, -1, 1]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![2, 0, 0], ![-35, -1, 1]] ![![2, 0, 0], ![-35, -1, 1]]
  ![![4, 0, 0], ![35, 3, -1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![-70, -2, 2]], ![![-70, -2, 2], ![385, 81, -13]]]
 hmul := by decide
 f := ![![![![5386151, 52837155, 32523104], ![-104414346, -13075209, 0]], ![![0, 0, 0], ![-21844, 6, 0]]], ![![![43089830, 422704499, 260189305], ![-835329125, -104603469, 0]], ![![0, 0, 0], ![-174755, 48, 0]]]]
 g := ![![![![5741, -12468, 1132], ![40816, 5184, 0]], ![![-98035, 211948, -19234], ![-693918, -88140, 0]]], ![![![-98035, 211948, -19234], ![-693918, -88140, 0]], ![![438445, -948072, 86039], ![3104031, 394266, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![4, 0, 0], ![35, 3, -1]] ![![2, 0, 0], ![-35, -1, 1]]
  ![![-304499617, -88577533, -13346951]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![8, 0, 0], ![-140, -4, 4]], ![![70, 6, -2], ![175, -49, 7]]]
 hmul := by decide
 f := ![![![![-11015059471920081174, -107263860959360307290, -66462706920721834511], ![213164117777920657100, 26710943802095247751, 0]], ![![209998674588327768, -249798814423466, 0], ![635115426577, 323883126, 0]]]]
 g := ![![![![-164224, 941, 2207]], ![![2387700, 158057, -62557]]], ![![![-884870, -103288, 31116]], ![![-7687575, 580727, 8099]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![21688670091718276670375049391, 6309134013707292922322115756, 950666604514475904757981410])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-35, -1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![35, 3, -1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-35, -2, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![2, 0, 0], ![-35, -2, 1]] ![![2, 0, 0], ![-35, -1, 1]]
  ![![2, 0, 0], ![1, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![-70, -2, 2]], ![![-70, -4, 2], ![105, 65, -10]]]
 hmul := by decide
 f := ![![![![5653, 54782, 33915], ![-108859, -13632, 0]], ![![123, 0, 0], ![-2, 0, 0]]], ![![![2774, 26741, 16554], ![-53135, -6654, 0]], ![![60, 0, 0], ![-1, 0, 0]]]]
 g := ![![![![2, 0, 0], ![0, 0, 0]], ![![-29, 5, 1], ![-12, 0, 0]]], ![![![-29, 4, 1], ![-12, 0, 0]], ![![38, 18, -5], ![29, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![2, 0, 0], ![-35, -2, 1]] ![![4, 0, 0], ![35, 3, -1]]
  ![![4, 0, 0], ![-1, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![8, 0, 0], ![70, 6, -2]], ![![-140, -8, 4], ![455, -35, 0]]]
 hmul := by decide
 f := ![![![![660565868, -1428317827, 129620405], ![4676307998, 593974836, 0]], ![![1263, 0, 0], ![-4, 0, 0]]], ![![![-164757692, 356249619, -32329793], ![-1166360114, -148148616, 0]], ![![-315, 0, 0], ![1, 0, 0]]]]
 g := ![![![![2, 0, 0], ![0, 0, 0]], ![![17, 2, 0], ![-2, -1, 0]]], ![![![-33, -4, 0], ![8, 2, 0]], ![![107, -2, 0], ![-27, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![-1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![-33, -2, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![4, 0, 0], ![-33, -2, 1]] ![![2, 0, 0], ![-35, -1, 1]]
  ![![4, 0, 0], ![1, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![8, 0, 0], ![-140, -4, 4]], ![![-66, -4, 2], ![35, 63, -8]]]
 hmul := by decide
 f := ![![![![3433790739, 33420005357, 20715521404], ![-66443579410, -8325851555, 0]], ![![69961968, -378, 0], ![-4, 0, 0]]], ![![![872064587, 8487530193, 5261028880], ![-16874380488, -2114479507, 0]], ![![17767930, -96, 0], ![-1, 0, 0]]]]
 g := ![![![![2, 0, 0], ![0, 0, 0]], ![![-32, -32, -33], ![-12, 68, 0]]], ![![![-15, -15, -15], ![-6, 31, 0]], ![![7, 7, -9], ![7, 14, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![4, 0, 0], ![-33, -2, 1]] ![![4, 0, 0], ![35, 3, -1]]
  ![![4, 0, 0], ![-69, -3, 2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![16, 0, 0], ![140, 12, -4]], ![![-132, -8, 4], ![525, -29, -2]]]
 hmul := by decide
 f := ![![![![3383314900443, -7315620313395, 663895627034], ![23951316237209, 3042247241700, 0]], ![![3037167, 0, 0], ![-12, 0, 0]]], ![![![-58360675108795, 126191192038147, -11451903868069], ![-413149537206328, -52477409906310, 0]], ![![-52389778, 0, 0], ![207, 0, 0]]]]
 g := ![![![![4, 0, 0], ![0, 0, 0]], ![![35, 3, -1], ![0, 0, 0]]], ![![![36, 1, -1], ![4, 0, 0]], ![![45, -11, 2], ![-5, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![-69, -3, 2]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl
