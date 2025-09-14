import IdealArithmetic.Examples.SmallDisc.PrimesBelowSmallDisc2
import IdealArithmetic.Examples.SmallDisc.NonPrincipalExampleSmallDisc

noncomputable section

lemma ideal_mul_span_singleton_coe (O R : Type*) [CommRing O] [CommRing R]
  [Algebra R O] {r m : ℕ} [NeZero r] (B : Basis (Fin r) R O)
  (I : Ideal O) (v : Fin m → Fin r → R)
  (hI : I = Ideal.span (Set.range (fun i => B.equivFun.symm (v i)))) (r : R) :
  Ideal.span {(algebraMap R O r)} * I = Ideal.span (Set.range (fun i => B.equivFun.symm ((r • v) i))) := by
  rw [hI, Ideal.span_mul_span] ; congr
  simp only [Set.mem_singleton_iff, Basis.equivFun_symm_apply, Set.mem_range, Set.iUnion_exists,
    Set.iUnion_iUnion_eq', Set.iUnion_singleton_eq_range, Set.iUnion_iUnion_eq_left, Pi.smul_apply,
    map_smul]
  refine congrArg (f := Set.range) ?_
  simp only [Basis.equivFun_symm_apply, Algebra.smul_def, Pi.smul_apply, Pi.mul_apply,
    Pi.algebraMap_apply, Algebra.id.map_eq_id, RingHom.id_apply, map_mul]

/- def R43RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J ^ 2) ![2, 0, 1, 0, 1] ![![2, 0, 0, 0, 0], ![1, 0, 1, 0, 0]]
  ![![4 ,0 ,2, 0, 2], ![2 ,2 ,-2 , 0 , 2]] where
T := Table
heq := timesTableT_eq_Table
hI := by
  simp only [pow_succ, pow_one, pow_zero, one_mul]
  exact ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ0
hmul := by decide


def E43RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I43N1) (Ideal.span {B.equivFun.symm ![2, 0, 1, 0, 1]} * J ^ 2)
  ![![86, 0, 0, 0, 0], ![12, 2, 0, 0, 0]] ![![4 ,0 ,2, 0, 2], ![2 ,2 ,-2 , 0 , 2]] where
T := Table
heq := timesTableT_eq_Table
hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ;exact {out := by decide}
hieq2 := by exact ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R43RS1
g := ![![![ 12 , 2 , 9 , 7, 20], ![11 ,0 ,-28 , 0 , 0]], ![![2 ,0 , 1 , 1 , 3], ![2 , 0, -4 , 0 , 0]]]
h := ![![![-5470 , -2632 ,-11012 , -2922 , 120], ![39202 , -721 , 78300 , -5159,   0]], ![![-2003 , -965 ,-4027 ,-1074 ,  43], ![14355 , -249 ,28635, -1848 ,   0]]]
hle1 := by decide
hle2 := by decide


lemma R43N1 : Ideal.span {2} * I43N1 =  Ideal.span {B.equivFun.symm ![2, 0, 1, 0, 1]} * J ^ 2 := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E43RS1

def R43RS2 : IdealMulPrincipalCertificate O ℤ timesTableO J ![2, -1, 1, 0, 1] ![![2, 0, 0, 0, 0], ![1, 1, 0, 1, 0]]
  ![![4 ,-2 , 2 , 0 , 2], ![6, -6 , 2 ,-2 , 0]] where
T := Table
heq := timesTableT_eq_Table
hI := rfl
hmul := by decide

def E43RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I43N2) (Ideal.span {B.equivFun.symm ![2, -1, 1, 0, 1]} * J ^ 1)
  ![![86, 0, 0, 0, 0], ![-24 ,  2  ,0 , 0 , 0]] ![![4 ,-2 , 2 , 0 , 2], ![6, -6 , 2 ,-2 , 0]] where
T := Table
heq := timesTableT_eq_Table
hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ;exact {out := by decide}
hieq2 := by
  rw [pow_one]
  exact ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R43RS2
g := ![![![-8196, 0, -248756, 177757, -203375], ![-86067, 355509, 0, -13167, 51253]], ![![2126, 0, 64613, -46172, 52826], ![22360, -92343, 0, 3420, -13312]]]
h := ![![![13910, -5360, 64096, -11542, 68], ![49844, 4165, 230615, -2923, 0]], ![![16233, -6250, 74796, -13465, 79], ![58168, 4878, 269115, -3397, 0]]]
hle1 := by decide
hle2 := by decide


lemma R43N2 : Ideal.span {2} * I43N2 =  Ideal.span {B.equivFun.symm ![2, -1, 1, 0, 1]} * J ^ 1 := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E43RS2
#exit

def R41RS1 : IdealMulPrincipalCertificate O ℤ timesTableO J ![6, 1, 1, 2, 1] ![![2, 0, 0, 0, 0], ![1, 1, 0, 1, 0]]
  ![![12, 2, 2, 4, 2], ![10, 2, -2, 4, 2]] where
T := Table
heq := timesTableT_eq_Table
hI := rfl
hmul := by decide

def E41RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I41N1) (Ideal.span {B.equivFun.symm ![6, 1, 1, 2, 1]} * J ^ 1)
  ![![82, 0, 0, 0, 0], ![18, 2, 0, 0, 0]] ![![12, 2, 2, 4, 2], ![10, 2, -2, 4, 2]] where
T := Table
heq := timesTableT_eq_Table
hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ;exact {out := by decide}
hieq2 := by
  rw [pow_one]
  exact ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R41RS1
g := ![![![14539, -29975, -12715, 8174, -19069], ![-3629, 38142, -12714, 0, 0]], ![![3355, -6917, -2934, 1886, -4400], ![-837, 8801, -2934, 0, 0]]]
h := ![![![4044, 957, 5531, -602, -199], ![-18422, 396, -24378, 8160, 0]], ![![1288, 297, 1735, -194, -63], ![-5867, 149, -7650, 2584, 0]]]
hle1 := by decide
hle2 := by decide

lemma R41N1 : Ideal.span {2} * I41N1 =  Ideal.span {B.equivFun.symm ![6, 1, 1, 2, 1]} * J ^ 1 := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E41RS1


def R41RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J ^ 2) ![6, 0, 1, 0, 1] ![![2, 0, 0, 0, 0], ![1, 0, 1, 0, 0]]
  ![![12, 0, 2, 0, 2], ![6, 2, 2, 0, 2]] where
T := Table
heq := timesTableT_eq_Table
hI := by
  simp only [pow_succ, pow_one, pow_zero, one_mul]
  exact ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ0
hmul := by decide

def E41RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I41N2) (Ideal.span {B.equivFun.symm ![6, 0, 1, 0, 1]} * J ^ 2)
  ![![82, 0, 0, 0, 0], ![-6, 2, 0, 0, 0]] ![![12, 0, 2, 0, 2], ![6, 2, 2, 0, 2]] where
T := Table
heq := timesTableT_eq_Table
hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ;exact {out := by decide}
hieq2 := by
  exact ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R41RS2
g := ![![![5, 2, -3, -3, 1], ![1, 0, -4, 0, 0]], ![![-1, 0, 0, 0, 0], ![1, 0, 0, 0, 0]]]
h := ![![![822, -5757, 16351, -12066, 307], ![11232, 1223, 228474, -12586, 0]], ![![489, -3432, 9749, -7194, 183], ![6682, 731, 136224, -7502, 0]]]
hle1 := by decide
hle2 := by decide

lemma R41N2 : Ideal.span {2} * I41N2 =  Ideal.span {B.equivFun.symm ![6, 0, 1, 0, 1]} * J ^ 2 := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E41RS2

def R29RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J ^ 2) ![6, 0, -1, 0, 1] ![![2, 0, 0, 0, 0], ![1, 0, 1, 0, 0]]
  ![![12, 0, -2, 0, 2], ![6, 2, 0, 0, 0]] where
T := Table
heq := timesTableT_eq_Table
hI := by
  simp only [pow_succ, pow_one, pow_zero, one_mul]
  exact ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ0
hmul := by decide

def E29RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I29N1) (Ideal.span {B.equivFun.symm ![6, 0, -1, 0, 1]} * J ^ 2)
  ![![58, 0, 0, 0, 0], ![6, 2, 0, 0, 0]] ![![12, 0, -2, 0, 2], ![6, 2, 0, 0, 0]] where
T := Table
heq := timesTableT_eq_Table
hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ;exact {out := by decide}
hieq2 := by
  exact ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R29RS1
g := ![![![-7, 11, -36, -3, 7], ![21, 0, 0, 0, -12]], ![![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0]]]
h := ![![![-72, -382, -1126, -645, 30], ![698, -92, 10656, -869, 0]], ![![-57, -289, -846, -486, 22], ![552, -58, 8004, -638, 0]]]
hle1 := by decide
hle2 := by decide

lemma R29N1 : Ideal.span {2} * I29N1 =  Ideal.span {B.equivFun.symm ![6, 0, -1, 0, 1]} * J ^ 2 := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E29RS1

def R29RS2 : IdealMulPrincipalCertificate O ℤ timesTableO J ![2, 1, -1, 0, 1] ![![2, 0, 0, 0, 0], ![1, 1, 0, 1, 0]]
  ![![4, 2, -2, 0, 2], ![2, 0, 2, -4, 2]] where
T := Table
heq := timesTableT_eq_Table
hI := rfl
hmul := by decide

def E29RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I29N2) (Ideal.span {B.equivFun.symm ![2, 1, -1, 0, 1]} * J ^ 1)
  ![![58, 0, 0, 0, 0], ![16, 2, 0, 0, 0]] ![![4, 2, -2, 0, 2], ![2, 0, 2, -4, 2]] where
T := Table
heq := timesTableT_eq_Table
hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ;exact {out := by decide}
hieq2 := by
  rw [pow_one]
  exact ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R29RS2
g := ![![![659, 4352, 8299, -265, 7376], ![2375, -14749, -1840, 0, 0]], ![![247, 1631, 3111, -99, 2765], ![890, -5529, -690, 0, 0]]]
h := ![![![-6454, -4127, -33483, -7824, 73], ![23396, -3203, 121912, -2116, 0]], ![![-2387, -1521, -12305, -2874, 27], ![8653, -1168, 44800, -782, 0]]]
hle1 := by decide
hle2 := by decide

lemma R29N2 : Ideal.span {2} * I29N2 =  Ideal.span {B.equivFun.symm ![2, 1, -1, 0, 1]} * J ^ 1 := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E29RS2

def R17RS1 : IdealMulPrincipalCertificate O ℤ timesTableO J ![-2, 1, 1, 0, -1] ![![2, 0, 0, 0, 0], ![1, 1, 0, 1, 0]]
  ![![-4, 2, 2, 0, -2], ![-2, 2, 0, 4, 0]] where
T := Table
heq := timesTableT_eq_Table
hI := rfl
hmul := by decide

def E17RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I17N1) (Ideal.span {B.equivFun.symm ![-2, 1, 1, 0, -1]} * J ^ 1)
  ![![34, 0, 0, 0, 0], ![-16, 2, 0, 0, 0]] ![![-4, 2, 2, 0, -2], ![-2, 2, 0, 4, 0]] where
T := Table
heq := timesTableT_eq_Table
hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ;exact {out := by decide}
hieq2 := by
  rw [pow_one]
  exact ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R17RS1
g := ![![![-262, 294, -127, -116, 5], ![-41, -17, 268, 0, 0]], ![![5, -3, -3, 0, -2], ![2, 7, 0, 0, 0]]]
h := ![![![30, 0, 35, -18, 1], ![64, 18, 81, -18, 0]], ![![-97, 22, -64, 16, 0], ![-206, 4, -135, 0, 0]]]
hle1 := by decide
hle2 := by decide

lemma R17N1 : Ideal.span {2} * I17N1 =  Ideal.span {B.equivFun.symm ![-2, 1, 1, 0, -1]} * J ^ 1 := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E17RS1

def R17RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J ^ 2) ![10, 1, 0, 2, 2] ![![2, 0, 0, 0, 0], ![1, 0, 1, 0, 0]]
  ![![20, 2, 0, 4, 4], ![14, 0, 0, 2, 2]] where
T := Table
heq := timesTableT_eq_Table
hI := by
  simp only [pow_succ, pow_one, pow_zero, one_mul]
  exact ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ0
hmul := by decide

def E17RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I17N2) (Ideal.span {B.equivFun.symm ![10, 1, 0, 2, 2]} * J ^ 2)
  ![![34, 0, 0, 0, 0], ![-8, 2, 0, 0, 0]] ![![20, 2, 0, 4, 4], ![14, 0, 0, 2, 2]] where
T := Table
heq := timesTableT_eq_Table
hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ;exact {out := by decide}
hieq2 := by
  exact ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R17RS2
g := ![![![-19, 19, 0, 2, 0], ![13, 0, 0, 13, 1]], ![![-8, -27, 49, 0, -12], ![20, 0, 0, -2, 24]]]
h := ![![![9538, -4952, 11807, -6520, 111], ![40534, 2000, 51651, -1885, 0]], ![![6007, -3117, 7425, -4101, 70], ![25528, 1255, 32481, -1189, 0]]]
hle1 := by decide
hle2 := by decide

lemma R17N2 : Ideal.span {2} * I17N2 =  Ideal.span {B.equivFun.symm ![10, 1, 0, 2, 2]} * J ^ 2 := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E17RS2

def R11RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J ^ 2) ![2, 1, 0, 0, 0] ![![2, 0, 0, 0, 0], ![1, 0, 1, 0, 0]]
  ![![4, 2, 0, 0, 0], ![2, 2, 2, 2, 0]] where
T := Table
heq := timesTableT_eq_Table
hI := by
  simp only [pow_succ, pow_one, pow_zero, one_mul]
  exact ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ0
hmul := by decide

def E11RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I11N1) (Ideal.span {B.equivFun.symm ![2, 1, 0, 0, 0]} * J ^ 2)
  ![![22, 0, 0, 0, 0], ![4, 2, 0, 0, 0]] ![![4, 2, 0, 0, 0], ![2, 2, 2, 2, 0]] where
T := Table
heq := timesTableT_eq_Table
hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ;exact {out := by decide}
hieq2 := by
  exact ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R11RS1
g := ![![![-15, 27, 14, -1, 14], ![1, 0, -27, 19, 0]], ![![-3, 6, 3, 0, 3], ![0, 0, -6, 4, 0]]]
h := ![![![6, 5, 3, 14, 3], ![-32, 11, -44, -33, 0]], ![![5, 4, 2, 13, 3], ![-27, 11, -38, -33, 0]]]
hle1 := by decide
hle2 := by decide

lemma R11N1 : Ideal.span {2} * I11N1 =  Ideal.span {B.equivFun.symm ![2, 1, 0, 0, 0]} * J ^ 2 := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E11RS1

def R11RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J) ![6, -1, -1, 0, 1] ![![2, 0, 0, 0, 0], ![1, 1, 0, 1, 0]]
  ![![12, -2, -2, 0, 2], ![6, 2, 0, 0, 0]] where
T := Table
heq := timesTableT_eq_Table
hI := by rfl
hmul := by decide

def E11RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I11N2) (Ideal.span {B.equivFun.symm ![6, -1, -1, 0, 1]} * J ^ 1)
  ![![22, 0, 0, 0, 0], ![6, 2, 0, 0, 0]] ![![12, -2, -2, 0, 2], ![6, 2, 0, 0, 0]] where
T := Table
heq := timesTableT_eq_Table
hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ;exact {out := by decide}
hieq2 := by
  rw [pow_one]
  exact ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R11RS2
g := ![![![231, -604, 243, 15, 27], ![403, -55, -430, 0, 0]], ![![93, -240, 97, 7, 11], ![159, -22, -172, 0, 0]]]
h := ![![![-642, -1231, -3720, -2361, 64], ![2356, -952, 14040, -703, 0]], ![![-393, -755, -2274, -1446, 38], ![1442, -572, 8580, -418, 0]]]
hle1 := by decide
hle2 := by decide

lemma R11N2 : Ideal.span {2} * I11N2 =  Ideal.span {B.equivFun.symm ![6, -1, -1, 0, 1]} * J ^ 1 := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E11RS2

def R7RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J) ![2, 1, 1, 2, 1] ![![2, 0, 0, 0, 0], ![1, 1, 0, 1, 0]]
  ![![4, 2, 2, 4, 2], ![6, -2, -2, 0, 2]] where
T := Table
heq := timesTableT_eq_Table
hI := rfl
hmul := by decide

def E7RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I7N1) (Ideal.span {B.equivFun.symm ![2, 1, 1, 2, 1]} * J ^ 1)
  ![![14, 0, 0, 0, 0], ![-6, 2, 0, 0, 0]] ![![4, 2, 2, 4, 2], ![6, -2, -2, 0, 2]] where
T := Table
heq := timesTableT_eq_Table
hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ;exact {out := by decide}
hieq2 := by
  rw [pow_one]
  exact ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R7RS1
g := ![![![-114, -36, -323, -36, -242], ![-91, 486, 162, 0, 0]], ![![38, 12, 108, 12, 81], ![31, -163, -54, 0, 0]]]
h := ![![![278, -132, 201, -141, -2], ![648, 80, 517, 15, 0]], ![![273, -130, 193, -135, -2], ![636, 74, 495, 15, 0]]]
hle1 := by decide
hle2 := by decide

lemma R7N1 : Ideal.span {2} * I7N1 =  Ideal.span {B.equivFun.symm ![2, 1, 1, 2, 1]} * J ^ 1 := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E7RS1

def R7RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J ^ 2) ![2, -1, 0, 0, 0] ![![2, 0, 0, 0, 0], ![1, 0, 1, 0, 0]]
  ![![4, -2, 0, 0, 0], ![2, -2, 2, -2, 0]] where
T := Table
heq := timesTableT_eq_Table
hI := by
  simp only [pow_succ, pow_one, pow_zero, one_mul]
  exact ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ0
hmul := by decide

def E7RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I7N2) (Ideal.span {B.equivFun.symm ![2, -1, 0, 0, 0]} * J ^ 2)
  ![![14, 0, 0, 0, 0], ![-4, 2, 0, 0, 0]] ![![4, -2, 0, 0, 0], ![2, -2, 2, -2, 0]] where
T := Table
heq := timesTableT_eq_Table
hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ;exact {out := by decide}
hieq2 := by
  exact ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R7RS2
g := ![![![-87, 204, -87, 1, -131], ![-87, 0, 263, 135, 0]], ![![-1, 0, -1, 0, -1], ![0, 0, 2, 0, 0]]]
h := ![![![-234, 241, -292, 288, 12], ![-820, -112, -1092, -84, 0]], ![![-223, 228, -277, 273, 12], ![-781, -112, -1040, -84, 0]]]
hle1 := by decide
hle2 := by decide

lemma R7N2 : Ideal.span {2} * I7N2 =  Ideal.span {B.equivFun.symm ![2, -1, 0, 0, 0]} * J ^ 2 := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E7RS2

def R2RS0 : IdealMulPrincipalCertificate O ℤ timesTableO (J ^ 2) ![0, 1, 0, 0, 0] ![![2, 0, 0, 0, 0], ![1, 0, 1, 0, 0]]
  ![![0, 2, 0, 0, 0], ![0, 2, 0, 2, 0]] where
T := Table
heq := timesTableT_eq_Table
hI := by
  simp only [pow_succ, pow_one, pow_zero, one_mul]
  exact ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ0
hmul := by decide

def E2RS0 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I2N0) (Ideal.span {B.equivFun.symm ![0, 1, 0, 0, 0]} * J ^ 2)
  ![![4, 0, 0, 0, 0], ![0, 0, 2, 0, 0]] ![![0, 2, 0, 0, 0], ![0, 2, 0, 2, 0]] where
T := Table
heq := timesTableT_eq_Table
hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ;exact {out := by decide}
hieq2 := by
  exact ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R2RS0
g := ![![![1, -1, 1, 0, 0], ![3, 0, 0, 0, 1]], ![![-3, 3, 0, -2, 0], ![0, 2, 0, 3, 0]]]
h := ![![![0, 0, 0, -1, 0], ![0, 1, 0, 0, 0]], ![![1, -1, 0, 0, 0], ![0, 0, 0, -1, 0]]]
hle1 := by decide
hle2 := by decide

lemma R2N0 : Ideal.span {2} * I2N0 =  Ideal.span {B.equivFun.symm ![0, 1, 0, 0, 0]} * J ^ 2 := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E2RS0

lemma R2N1 : Ideal.span {1} * I2N1 =  Ideal.span {1} * J ^ 1 := by
  rw [pow_one]
  rfl
-/
def R2RS0 : IdealMulPrincipalCertificate O ℤ timesTableO (J ^ 2) ![0, 1, 0, 0, 0] ![![2, 0, 0, 0, 0], ![1, 0, 1, 0, 0]]
  ![![0, 2, 0, 0, 0], ![0, 2, 0, 2, 0]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by
      simp only [pow_succ, pow_one, pow_zero, one_mul]
      exact ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ0
    hmul := by decide

def E2RS0 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I2N0) (Ideal.span {B.equivFun.symm ![0, 1, 0, 0, 0]} * J ^ 2)
      ![![4, 0, 0, 0, 0], ![0, 0, 2, 0, 0]] ![![0, 2, 0, 0, 0], ![0, 2, 0, 2, 0]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by
      exact ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R2RS0
    g := ![![![1, -1, 1, 0, 0], ![3, 0, 0, 0, 1]], ![![-3, 3, 0, -2, 0], ![0, 2, 0, 3, 0]]]
    h := ![![![0, 0, 0, -1, 0], ![0, 1, 0, 0, 0]], ![![1, -1, 0, 0, 0], ![0, 0, 0, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {2} * I2N0 =  Ideal.span {B.equivFun.symm ![0, 1, 0, 0, 0]} * J ^ 2 := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E2RS0


def R2RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J ^ 1) ![1, 0, 0, 0, 0] ![![2, 0, 0, 0, 0], ![1, 1, 0, 1, 0]]
  ![![2, 0, 0, 0, 0], ![1, 1, 0, 1, 0]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by
      simp only [pow_succ, pow_one, pow_zero, one_mul]
      rfl
    hmul := by decide

def E2RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {1} * I2N1) (Ideal.span {B.equivFun.symm ![1, 0, 0, 0, 0]} * J ^ 1)
      ![![2, 0, 0, 0, 0], ![1, 1, 0, 1, 0]] ![![2, 0, 0, 0, 0], ![1, 1, 0, 1, 0]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 1 ; decide ; exact {out := by decide}
    hieq2 := by
      exact ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R2RS1
    g := ![![![4, -1, 1, 2, 0], ![-2, 0, -2, 0, 0]], ![![2, -2, 1, 1, 0], ![1, 0, -2, 0, 0]]]
    h := ![![![4, -1, 1, 2, 0], ![-2, 0, -2, 0, 0]], ![![2, -2, 1, 1, 0], ![1, 0, -2, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {1} * I2N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0, 0, 0]} * J ^ 1 := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E2RS1


def R7RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J ^ 1) ![2, 1, 1, 2, 1] ![![2, 0, 0, 0, 0], ![1, 1, 0, 1, 0]]
  ![![4, 2, 2, 4, 2], ![6, -2, -2, 0, 2]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by
      simp only [pow_succ, pow_one, pow_zero, one_mul]
      rfl
    hmul := by decide

def E7RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I7N1) (Ideal.span {B.equivFun.symm ![2, 1, 1, 2, 1]} * J ^ 1)
      ![![14, 0, 0, 0, 0], ![-6, 2, 0, 0, 0]] ![![4, 2, 2, 4, 2], ![6, -2, -2, 0, 2]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by
      exact ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R7RS1
    g := ![![![-114, -36, -323, -36, -242], ![-91, 486, 162, 0, 0]], ![![38, 12, 108, 12, 81], ![31, -163, -54, 0, 0]]]
    h := ![![![278, -132, 201, -141, -2], ![648, 80, 517, 15, 0]], ![![273, -130, 193, -135, -2], ![636, 74, 495, 15, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {2} * I7N1 =  Ideal.span {B.equivFun.symm ![2, 1, 1, 2, 1]} * J ^ 1 := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E7RS1


def R7RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J ^ 2) ![2, -1, 0, 0, 0] ![![2, 0, 0, 0, 0], ![1, 0, 1, 0, 0]]
  ![![4, -2, 0, 0, 0], ![2, -2, 2, -2, 0]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by
      simp only [pow_succ, pow_one, pow_zero, one_mul]
      exact ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ0
    hmul := by decide

def E7RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I7N2) (Ideal.span {B.equivFun.symm ![2, -1, 0, 0, 0]} * J ^ 2)
      ![![14, 0, 0, 0, 0], ![-4, 2, 0, 0, 0]] ![![4, -2, 0, 0, 0], ![2, -2, 2, -2, 0]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by
      exact ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R7RS2
    g := ![![![-87, 204, -87, 1, -131], ![-87, 0, 263, 135, 0]], ![![-1, 0, -1, 0, -1], ![0, 0, 2, 0, 0]]]
    h := ![![![-234, 241, -292, 288, 12], ![-820, -112, -1092, -84, 0]], ![![-223, 228, -277, 273, 12], ![-781, -112, -1040, -84, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N2 : Ideal.span {2} * I7N2 =  Ideal.span {B.equivFun.symm ![2, -1, 0, 0, 0]} * J ^ 2 := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E7RS2


def R11RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J ^ 2) ![2, 1, 0, 0, 0] ![![2, 0, 0, 0, 0], ![1, 0, 1, 0, 0]]
  ![![4, 2, 0, 0, 0], ![2, 2, 2, 2, 0]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by
      simp only [pow_succ, pow_one, pow_zero, one_mul]
      exact ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ0
    hmul := by decide

def E11RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I11N1) (Ideal.span {B.equivFun.symm ![2, 1, 0, 0, 0]} * J ^ 2)
      ![![22, 0, 0, 0, 0], ![4, 2, 0, 0, 0]] ![![4, 2, 0, 0, 0], ![2, 2, 2, 2, 0]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by
      exact ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R11RS1
    g := ![![![-15, 27, 14, -1, 14], ![1, 0, -27, 19, 0]], ![![-3, 6, 3, 0, 3], ![0, 0, -6, 4, 0]]]
    h := ![![![6, 5, 3, 14, 3], ![-32, 11, -44, -33, 0]], ![![5, 4, 2, 13, 3], ![-27, 11, -38, -33, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {2} * I11N1 =  Ideal.span {B.equivFun.symm ![2, 1, 0, 0, 0]} * J ^ 2 := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E11RS1


def R11RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J ^ 1) ![6, -1, -1, 0, 1] ![![2, 0, 0, 0, 0], ![1, 1, 0, 1, 0]]
  ![![12, -2, -2, 0, 2], ![6, 2, 0, 0, 0]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by
      simp only [pow_succ, pow_one, pow_zero, one_mul]
      rfl
    hmul := by decide

def E11RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I11N2) (Ideal.span {B.equivFun.symm ![6, -1, -1, 0, 1]} * J ^ 1)
      ![![22, 0, 0, 0, 0], ![6, 2, 0, 0, 0]] ![![12, -2, -2, 0, 2], ![6, 2, 0, 0, 0]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by
      exact ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R11RS2
    g := ![![![231, -604, 243, 15, 27], ![403, -55, -430, 0, 0]], ![![93, -240, 97, 7, 11], ![159, -22, -172, 0, 0]]]
    h := ![![![-642, -1231, -3720, -2361, 64], ![2356, -952, 14040, -703, 0]], ![![-393, -755, -2274, -1446, 38], ![1442, -572, 8580, -418, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N2 : Ideal.span {2} * I11N2 =  Ideal.span {B.equivFun.symm ![6, -1, -1, 0, 1]} * J ^ 1 := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E11RS2


def R17RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J ^ 1) ![-2, 1, 1, 0, -1] ![![2, 0, 0, 0, 0], ![1, 1, 0, 1, 0]]
  ![![-4, 2, 2, 0, -2], ![-2, 2, 0, 4, 0]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by
      simp only [pow_succ, pow_one, pow_zero, one_mul]
      rfl
    hmul := by decide

def E17RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I17N1) (Ideal.span {B.equivFun.symm ![-2, 1, 1, 0, -1]} * J ^ 1)
      ![![34, 0, 0, 0, 0], ![-16, 2, 0, 0, 0]] ![![-4, 2, 2, 0, -2], ![-2, 2, 0, 4, 0]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by
      exact ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R17RS1
    g := ![![![-262, 294, -127, -116, 5], ![-41, -17, 268, 0, 0]], ![![5, -3, -3, 0, -2], ![2, 7, 0, 0, 0]]]
    h := ![![![30, 0, 35, -18, 1], ![64, 18, 81, -18, 0]], ![![-97, 22, -64, 16, 0], ![-206, 4, -135, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {2} * I17N1 =  Ideal.span {B.equivFun.symm ![-2, 1, 1, 0, -1]} * J ^ 1 := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E17RS1


def R17RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J ^ 2) ![10, 1, 0, 2, 2] ![![2, 0, 0, 0, 0], ![1, 0, 1, 0, 0]]
  ![![20, 2, 0, 4, 4], ![14, 0, 0, 2, 2]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by
      simp only [pow_succ, pow_one, pow_zero, one_mul]
      exact ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ0
    hmul := by decide

def E17RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I17N2) (Ideal.span {B.equivFun.symm ![10, 1, 0, 2, 2]} * J ^ 2)
      ![![34, 0, 0, 0, 0], ![-8, 2, 0, 0, 0]] ![![20, 2, 0, 4, 4], ![14, 0, 0, 2, 2]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by
      exact ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R17RS2
    g := ![![![-19, 19, 0, 2, 0], ![13, 0, 0, 13, 1]], ![![-8, -27, 49, 0, -12], ![20, 0, 0, -2, 24]]]
    h := ![![![9538, -4952, 11807, -6520, 111], ![40534, 2000, 51651, -1885, 0]], ![![6007, -3117, 7425, -4101, 70], ![25528, 1255, 32481, -1189, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N2 : Ideal.span {2} * I17N2 =  Ideal.span {B.equivFun.symm ![10, 1, 0, 2, 2]} * J ^ 2 := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E17RS2


def R29RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J ^ 2) ![6, 0, -1, 0, 1] ![![2, 0, 0, 0, 0], ![1, 0, 1, 0, 0]]
  ![![12, 0, -2, 0, 2], ![6, 2, 0, 0, 0]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by
      simp only [pow_succ, pow_one, pow_zero, one_mul]
      exact ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ0
    hmul := by decide

def E29RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I29N1) (Ideal.span {B.equivFun.symm ![6, 0, -1, 0, 1]} * J ^ 2)
      ![![58, 0, 0, 0, 0], ![6, 2, 0, 0, 0]] ![![12, 0, -2, 0, 2], ![6, 2, 0, 0, 0]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by
      exact ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R29RS1
    g := ![![![-7, 11, -36, -3, 7], ![21, 0, 0, 0, -12]], ![![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0]]]
    h := ![![![-72, -382, -1126, -645, 30], ![698, -92, 10656, -869, 0]], ![![-57, -289, -846, -486, 22], ![552, -58, 8004, -638, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {2} * I29N1 =  Ideal.span {B.equivFun.symm ![6, 0, -1, 0, 1]} * J ^ 2 := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E29RS1


def R29RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J ^ 1) ![2, 1, -1, 0, 1] ![![2, 0, 0, 0, 0], ![1, 1, 0, 1, 0]]
  ![![4, 2, -2, 0, 2], ![2, 0, 2, -4, 2]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by
      simp only [pow_succ, pow_one, pow_zero, one_mul]
      rfl
    hmul := by decide

def E29RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I29N2) (Ideal.span {B.equivFun.symm ![2, 1, -1, 0, 1]} * J ^ 1)
      ![![58, 0, 0, 0, 0], ![16, 2, 0, 0, 0]] ![![4, 2, -2, 0, 2], ![2, 0, 2, -4, 2]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by
      exact ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R29RS2
    g := ![![![659, 4352, 8299, -265, 7376], ![2375, -14749, -1840, 0, 0]], ![![247, 1631, 3111, -99, 2765], ![890, -5529, -690, 0, 0]]]
    h := ![![![-6454, -4127, -33483, -7824, 73], ![23396, -3203, 121912, -2116, 0]], ![![-2387, -1521, -12305, -2874, 27], ![8653, -1168, 44800, -782, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N2 : Ideal.span {2} * I29N2 =  Ideal.span {B.equivFun.symm ![2, 1, -1, 0, 1]} * J ^ 1 := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E29RS2


def R41RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J ^ 1) ![6, 1, 1, 2, 1] ![![2, 0, 0, 0, 0], ![1, 1, 0, 1, 0]]
  ![![12, 2, 2, 4, 2], ![10, 2, -2, 4, 2]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by
      simp only [pow_succ, pow_one, pow_zero, one_mul]
      rfl
    hmul := by decide

def E41RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I41N1) (Ideal.span {B.equivFun.symm ![6, 1, 1, 2, 1]} * J ^ 1)
      ![![82, 0, 0, 0, 0], ![18, 2, 0, 0, 0]] ![![12, 2, 2, 4, 2], ![10, 2, -2, 4, 2]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by
      exact ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R41RS1
    g := ![![![14539, -29975, -12715, 8174, -19069], ![-3629, 38142, -12714, 0, 0]], ![![3355, -6917, -2934, 1886, -4400], ![-837, 8801, -2934, 0, 0]]]
    h := ![![![4044, 957, 5531, -602, -199], ![-18422, 396, -24378, 8160, 0]], ![![1288, 297, 1735, -194, -63], ![-5867, 149, -7650, 2584, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {2} * I41N1 =  Ideal.span {B.equivFun.symm ![6, 1, 1, 2, 1]} * J ^ 1 := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E41RS1


def R41RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J ^ 2) ![6, 0, 1, 0, 1] ![![2, 0, 0, 0, 0], ![1, 0, 1, 0, 0]]
  ![![12, 0, 2, 0, 2], ![6, 2, 2, 0, 2]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by
      simp only [pow_succ, pow_one, pow_zero, one_mul]
      exact ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ0
    hmul := by decide

def E41RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I41N2) (Ideal.span {B.equivFun.symm ![6, 0, 1, 0, 1]} * J ^ 2)
      ![![82, 0, 0, 0, 0], ![-6, 2, 0, 0, 0]] ![![12, 0, 2, 0, 2], ![6, 2, 2, 0, 2]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by
      exact ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R41RS2
    g := ![![![5, 2, -3, -3, 1], ![1, 0, -4, 0, 0]], ![![-1, 0, 0, 0, 0], ![1, 0, 0, 0, 0]]]
    h := ![![![822, -5757, 16351, -12066, 307], ![11232, 1223, 228474, -12586, 0]], ![![489, -3432, 9749, -7194, 183], ![6682, 731, 136224, -7502, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N2 : Ideal.span {2} * I41N2 =  Ideal.span {B.equivFun.symm ![6, 0, 1, 0, 1]} * J ^ 2 := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E41RS2


def R43RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J ^ 2) ![2, 0, 1, 0, 1] ![![2, 0, 0, 0, 0], ![1, 0, 1, 0, 0]]
  ![![4, 0, 2, 0, 2], ![2, 2, -2, 0, 2]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by
      simp only [pow_succ, pow_one, pow_zero, one_mul]
      exact ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ0
    hmul := by decide

def E43RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I43N1) (Ideal.span {B.equivFun.symm ![2, 0, 1, 0, 1]} * J ^ 2)
      ![![86, 0, 0, 0, 0], ![12, 2, 0, 0, 0]] ![![4, 0, 2, 0, 2], ![2, 2, -2, 0, 2]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by
      exact ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R43RS1
    g := ![![![12, 2, 9, 7, 20], ![11, 0, -28, 0, 0]], ![![2, 0, 1, 1, 3], ![2, 0, -4, 0, 0]]]
    h := ![![![-5470, -2632, -11012, -2922, 120], ![39202, -721, 78300, -5159, 0]], ![![-2003, -965, -4027, -1074, 43], ![14355, -249, 28635, -1848, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {2} * I43N1 =  Ideal.span {B.equivFun.symm ![2, 0, 1, 0, 1]} * J ^ 2 := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E43RS1


def R43RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J ^ 1) ![2, -1, 1, 0, 1] ![![2, 0, 0, 0, 0], ![1, 1, 0, 1, 0]]
  ![![4, -2, 2, 0, 2], ![6, -6, 2, -2, 0]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by
      simp only [pow_succ, pow_one, pow_zero, one_mul]
      rfl
    hmul := by decide

def E43RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I43N2) (Ideal.span {B.equivFun.symm ![2, -1, 1, 0, 1]} * J ^ 1)
      ![![86, 0, 0, 0, 0], ![-24, 2, 0, 0, 0]] ![![4, -2, 2, 0, 2], ![6, -6, 2, -2, 0]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by
      exact ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R43RS2
    g := ![![![-8196, 0, -248756, 177757, -203375], ![-86067, 355509, 0, -13167, 51253]], ![![2126, 0, 64613, -46172, 52826], ![22360, -92343, 0, 3420, -13312]]]
    h := ![![![13910, -5360, 64096, -11542, 68], ![49844, 4165, 230615, -2923, 0]], ![![16233, -6250, 74796, -13465, 79], ![58168, 4878, 269115, -3397, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N2 : Ideal.span {2} * I43N2 =  Ideal.span {B.equivFun.symm ![2, -1, 1, 0, 1]} * J ^ 1 := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E43RS2
