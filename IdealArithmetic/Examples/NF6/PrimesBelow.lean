import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Examples.NF6.RI6
import IdealArithmetic.ClassGroupGeneration

open Classical Polynomial

noncomputable section

lemma B_one : B 0 = 1 := by
  refine basisOfBuilderLists_zero_eq_one _ _ BQ

lemma B_one_repr : B.equivFun.symm ![1, 0, 0, 0, 0] = 1 := by
  rw [Basis.equivFun_symm_eq_repr_symm']
  apply_fun B.repr
  rw [← B_one]
  simp only [Basis.repr_symm_apply, Basis.repr_linearCombination, Fin.isValue, Basis.repr_self]
  ext i
  fin_cases i <;> norm_num
  · exact LinearEquiv.injective B.repr

lemma B_int_repr {n : ℤ} : B.equivFun.symm ![n, 0, 0, 0, 0] = n := by
  suffices B.equivFun.symm ![n, 0, 0, 0, 0] = n • 1 by convert this ; simp only [zsmul_eq_mul,mul_one]
  rw [← B_one_repr, ← LinearEquiv.map_smul]
  simp only [Basis.equivFun_symm_apply, zsmul_eq_mul, Matrix.smul_cons, smul_eq_mul, mul_one,
    mul_zero, Matrix.smul_empty]


instance : IsDomain O := by sorry

--------------------------------------------------------------
-- Ideals above 3

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] i)))

def SI3N0: IdealEqSpanCertificate O ℤ timesTableO I3N0
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0]]
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 3]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 1, 0, 2, 0], ![3, -1, 2, 3, 12], ![0, 0, 0, -2, -3]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, 0, 0, 0]], ![![0, -1, 0, -1, 0], ![1, 0, 2, 0, 0]], ![![0, 0, 0, 0, 1], ![0, 0, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 1, 0, 2, 0], ![1, -1, 2, 3, 4], ![0, 0, 0, -2, -1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 9 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI3N0)

def MemCI3N0 : IdealMemCertificate O ℤ B I3N0
  ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 3]] ![5583, -3658, 3709, 4702, 22416] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI3N0
 g := ![1861, -3658, 3709, 4702, 7472]
 hmem := by decide

def P3P0 : CertificateIrreducibleZModOfList' 3 2 2 1 [2, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 2], [0, 1]]
 g := ![![[1, 1]],![[2, 2]]]
 h' := ![![[1, 2], [0, 1]],![[0, 1], [1, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [2, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : PrimeIdeal O 3 where
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I3N0
  hcard := NI3N0
  P := [2, 2, 1]
  f := ofList [2, 2, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P3P0
  hneq := by decide
  hlen := by decide
  c := ![5583, -3658, 3709, 4702, 22416]
  a := ![-17, 4, -15, -20, -68]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI3N0
  hpmem := by
    show  _ ∈ I3N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI3N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := PrimeIdeal_isPrime PI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0], ![2, 3, -3, -1, -5]] i)))

def SI3N1: IdealEqSpanCertificate O ℤ timesTableO I3N1
 ![![3, 0, 0, 0, 0], ![2, 3, -3, -1, -5]]
 ![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![2, 2, 1, 0, 0], ![1, 1, 0, 1, 0], ![0, 1, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![2, 3, -3, -1, -5], ![-3, 0, 1, 1, 3], ![3, -3, 2, -1, 3], ![0, 3, -3, -3, -12], ![-2, -1, 1, 2, 4]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![1, 0, 0, 1, 1], ![0, 3, 0, 0, -3]], ![![1, -2, 2, 1, 3], ![2, 3, 0, 0, -2]], ![![0, -1, 1, 1, 2], ![1, 1, 0, 0, -1]], ![![-1, -2, 2, 1, 4], ![2, 1, 0, 0, -1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-2, -2, 3, 0, 0], ![-1, -1, 0, 3, 0], ![0, -1, 0, 0, 3]], ![![3, 5, -3, -1, -5], ![-2, -2, 1, 1, 3], ![0, -3, 2, -1, 3], ![3, 8, -3, -3, -12], ![-2, -3, 1, 2, 4]]]
  hle1 := by decide
  hle2 := by decide

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 9 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI3N1)

def MemCI3N1 : IdealMemCertificate O ℤ B I3N1
  ![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![2, 2, 1, 0, 0], ![1, 1, 0, 1, 0], ![0, 1, 0, 0, 1]] ![5600, -3662, 3724, 4722, 22484] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI3N1
 g := ![-2190, -12772, 3724, 4722, 22484]
 hmem := by decide

def P3P1 : CertificateIrreducibleZModOfList' 3 2 2 1 [2, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 2], [0, 1]]
 g := ![![[2, 1]],![[1, 2]]]
 h' := ![![[2, 2], [0, 1]],![[0, 1], [2, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [1, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N1 : PrimeIdeal O 3 where
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I3N1
  hcard := NI3N1
  P := [2, 1, 1]
  f := ofList [2, 1, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P3P1
  hneq := by decide
  hlen := by decide
  c := ![5600, -3662, 3724, 4722, 22484]
  a := ![-17, 4, -15, -20, -68]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI3N1
  hpmem := by
    show  _ ∈ I3N1.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI3N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := PrimeIdeal_isPrime PI3N1

def I3N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] i)))

def SI3N2: IdealEqSpanCertificate O ℤ timesTableO I3N2
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0]]
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![1, 1, 0, 0, 0], ![0, 1, 1, 0, 0], ![0, 1, 1, 2, 0], ![3, -1, 2, 4, 12], ![0, 0, 0, -2, -2]]]
  hmulB := by decide
  f := ![![![0, -1, 0, 0, 0], ![3, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0]], ![![0, -1, 0, 0, 0], ![2, 1, 0, 0, 0]], ![![0, -1, -1, -1, 0], ![0, 1, 2, 0, 0]], ![![0, 2, 2, 4, -1], ![0, 2, -8, 0, -2]]]
  g := ![![![1, 0, 0, 0, 0], ![-1, 3, 0, 0, 0], ![-2, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![0, 1, 0, 0, 0], ![-1, 1, 1, 0, 0], ![-1, 1, 1, 2, 0], ![0, -1, 2, 4, 12], ![0, 0, 0, -2, -2]]]
  hle1 := by decide
  hle2 := by decide

lemma NI3N2 : Nat.card (O ⧸ I3N2) = 3 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI3N2)

lemma isPrimeI3N2 : Ideal.IsPrime I3N2 := prime_ideal_of_norm_prime hp3.out _ NI3N2

def MulI3N0 : IdealMulEqCertificate O ℤ timesTableO (I3N0) I3N1
  ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] ![![3, 0, 0, 0, 0], ![2, 3, -3, -1, -5]]
  ![![3, 0, 0, 0, 0], ![0, -6, 4, 1, 6]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![9, 0, 0, 0, 0], ![6, 9, -9, -3, -15]], ![![0, 3, 0, 0, 0], ![-3, 0, 1, 1, 3]]]
 hmul := by decide
 f :=  ![![![![-2, -1, 1, 0, 2], ![1, -3, 0, 0, 2]], ![![2, 1, 0, 0, 0], ![0, 0, 0, 0, 0]]], ![![![-7, 0, 0, -2, 1], ![0, -15, 0, 0, 10]], ![![8, 5, 0, 0, 0], ![4, 0, 0, 0, 0]]]]
 g :=  ![![![![3, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![2, 3, -3, -1, -5], ![0, 0, 0, 0, 0]]], ![![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![-1, 2, -1, 0, -1], ![1, 0, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI3N1 : IdealMulEqCertificate O ℤ timesTableO (I3N0*I3N1) I3N2
  ![![3, 0, 0, 0, 0], ![0, -6, 4, 1, 6]] ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0]]
  ![![3, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI3N0
 hI2 := rfl
 M :=  ![![![9, 0, 0, 0, 0], ![3, 3, 0, 0, 0]], ![![0, -18, 12, 3, 18], ![3, -3, 0, 0, 0]]]
 hmul := by decide
 f :=  ![![![![0, -3286, -3339, -7600, 480], ![1, -2207, 12160, 0, 768]], ![![16, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]]
 g :=  ![![![![3, 0, 0, 0, 0]], ![![1, 1, 0, 0, 0]]], ![![![0, -6, 4, 1, 6]], ![![1, -1, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide


def PBC3 : PrimesBelowPCertificate 3 ![I3N0, I3N1, I3N2] where
  Ip := by
    intro i
    fin_cases i
    exact isPrimeI3N0
    exact isPrimeI3N1
    exact isPrimeI3N2
  hPprod := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI3N1, Set.range_unique]
    dsimp ; congr
    erw [B_int_repr]
    rfl


-- Ideals above 2

def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] i)))

def SI2N0: IdealEqSpanCertificate O ℤ timesTableO I2N0
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]]
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 1, 0, 2, 0], ![3, -1, 2, 3, 12], ![0, 0, 0, -2, -3]]]
  hmulB := by decide
  f := ![![![4, -2, 1, 3, 12], ![2, 2, 0, -2, 0]], ![![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, 0, 0, 0]], ![![2, 0, 0, 2, 6], ![-1, 2, 0, -1, 0]], ![![0, 0, 0, 1, 2], ![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![-1, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-1, 1, 0, 2, 0], ![0, -1, 2, 3, 12], ![1, 0, 0, -2, -3]]]
  hle1 := by decide
  hle2 := by decide

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0
def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![2, 0, -2, -1, -3]] i)))

def SI2N1: IdealEqSpanCertificate O ℤ timesTableO I2N1
 ![![2, 0, 0, 0, 0], ![2, 0, -2, -1, -3]]
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![2, 0, -2, -1, -3], ![-3, 1, -2, -1, -3], ![-3, -4, -1, -1, -3], ![0, -2, -2, 1, 0], ![0, 1, 1, 0, 2]]]
  hmulB := by decide
  f := ![![![18, 0, 7, 4, 12], ![-2, 8, 2, 0, 0]], ![![3, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]], ![![9, 0, 4, 2, 6], ![-1, 4, 1, 0, 0]], ![![8, -4, -6, -4, -12], ![-8, 2, -2, 1, 0]], ![![13, 0, 5, 4, 11], ![-1, 6, 2, -1, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-1, 2, 0, 0, 0], ![-1, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![2, 0, -2, -1, -3], ![-1, 1, -2, -1, -3], ![1, -4, -1, -1, -3], ![2, -2, -2, 1, 0], ![-1, 1, 1, 0, 2]]]
  hle1 := by decide
  hle2 := by decide

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![-2, -1, 2, 1, 3]] i)))

def SI2N2: IdealEqSpanCertificate O ℤ timesTableO I2N2
 ![![2, 0, 0, 0, 0], ![-2, -1, 2, 1, 3]]
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![-2, -1, 2, 1, 3], ![3, -1, 1, 1, 3], ![3, 3, 1, -1, 3], ![-3, 3, 0, -4, -12], ![0, -1, -1, 2, 1]]]
  hmulB := by decide
  f := ![![![4, 0, 2, -1, 2], ![0, -2, 0, 0, 2]], ![![-6, 3, 2, -4, -7], ![-2, 2, 0, -1, 2]], ![![-15, 4, 4, -6, -13], ![-5, 5, 0, -2, 2]], ![![2, 0, 1, 0, 1], ![0, -1, 0, 0, 1]], ![![9, -2, -2, 3, 7], ![3, -3, 0, 1, -1]]]
  g := ![![![1, 0, 0, 0, 0], ![-1, 2, 0, 0, 0], ![-1, 0, 2, 0, 0], ![-1, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![-2, -1, 2, 1, 3], ![1, -1, 1, 1, 3], ![0, 3, 1, -1, 3], ![-1, 3, 0, -4, -12], ![0, -1, -1, 2, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulEqCertificate O ℤ timesTableO (I2N0) I2N1
  ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] ![![2, 0, 0, 0, 0], ![2, 0, -2, -1, -3]]
  ![![2, 0, 0, 0, 0], ![1, 4, -3, -1, -5]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![4, 0, 0, 0, 0], ![4, 0, -4, -2, -6]], ![![0, 2, 0, 0, 0], ![-3, 1, -2, -1, -3]]]
 hmul := by decide
 f :=  ![![![![-4329, 701, -1347, -784, -2274], ![824, -2103, -211, 57, 0]], ![![-29, 0, 0, 0, 0], ![-34, -10, 0, 2, 0]]], ![![![-16641, 2695, -5187, -3013, -8741], ![3166, -8085, -809, 214, 0]], ![![-113, 0, 0, 0, 0], ![-134, -39, 0, 6, 0]]]]
 g :=  ![![![![-3, 4, 3, 1, 7], ![-2, -8, 0, -4, 0]], ![![-10, 12, 4, 1, 12], ![-6, -20, 0, -10, 0]]], ![![![-3, 0, 2, 1, 3], ![0, -2, 0, 0, 0]], ![![-3, 0, 0, 0, 0], ![0, -1, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI2N1 : IdealMulEqCertificate O ℤ timesTableO (I2N0*I2N1) I2N1
  ![![2, 0, 0, 0, 0], ![1, 4, -3, -1, -5]] ![![2, 0, 0, 0, 0], ![2, 0, -2, -1, -3]]
  ![![2, 0, 0, 0, 0], ![3, 3, -2, -1, -4]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI2N0
 hI2 := rfl
 M :=  ![![![4, 0, 0, 0, 0], ![4, 0, -4, -2, -6]], ![![2, 8, -6, -2, -10], ![-1, 13, -10, -3, -16]]]
 hmul := by decide
 f :=  ![![![![-50140, 8094, -15408, -9215, -26525], ![9670, -24282, -2698, 901, 0]], ![![0, 0, 0, 0, 0], ![-128, 13, 0, -3, 0]]], ![![![-396111, 63945, -121736, -72805, -209569], ![76386, -191835, -21315, 7119, 0]], ![![0, 0, 0, 0, 0], ![-1011, 105, 0, -21, 0]]]]
 g :=  ![![![![5, -7, 0, -1, 4], ![2, 4, 0, 0, 0]], ![![5, -7, -2, -2, 1], ![2, 4, 0, 0, 0]]], ![![![-11, 7, 2, 3, -1], ![2, -6, 0, 0, 0]], ![![-23, 19, 3, 6, -6], ![1, -14, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI2N2 : IdealMulEqCertificate O ℤ timesTableO (I2N0*I2N1*I2N1) I2N2
  ![![2, 0, 0, 0, 0], ![3, 3, -2, -1, -4]] ![![2, 0, 0, 0, 0], ![-2, -1, 2, 1, 3]]
  ![![2, 0, 0, 0, 0], ![2, 5, -5, -2, -8]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI2N1
 hI2 := rfl
 M :=  ![![![4, 0, 0, 0, 0], ![-4, -2, 4, 2, 6]], ![![6, 6, -4, -2, -8], ![0, -11, 11, 4, 20]]]
 hmul := by decide
 f :=  ![![![![-3381, 701, 29, -824, -2286], ![-776, 1563, 0, -177, 75]], ![![-3, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]], ![![![-47065, 9744, 384, -11440, -31776], ![-10800, 21759, 0, -2454, 1029]], ![![-36, 0, 0, 0, 0], ![5, 0, 0, 0, 0]]]]
 g :=  ![![![![2, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![-2, -1, 2, 1, 3], ![0, 0, 0, 0, 0]]], ![![![1, -2, 3, 1, 4], ![2, 0, 0, 0, 0]], ![![1, -3, 3, 1, 6], ![-1, 0, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI2N3 : IdealMulEqCertificate O ℤ timesTableO (I2N0*I2N1*I2N1*I2N2) I2N2
  ![![2, 0, 0, 0, 0], ![2, 5, -5, -2, -8]] ![![2, 0, 0, 0, 0], ![-2, -1, 2, 1, 3]]
  ![![2, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI2N2
 hI2 := rfl
 M :=  ![![![4, 0, 0, 0, 0], ![-4, -2, 4, 2, 6]], ![![4, 10, -10, -4, -16], ![2, -20, 12, 4, 22]]]
 hmul := by decide
 f :=  ![![![![-6600, 1364, 32, -1586, -4443], ![-1505, 3057, 0, -339, 129]], ![![0, 0, 0, 0, 0], ![3, 0, 0, 0, 0]]]]
 g :=  ![![![![2, 0, 0, 0, 0]], ![![-2, -1, 2, 1, 3]]], ![![![2, 5, -5, -2, -8]], ![![1, -10, 6, 2, 11]]]]
 hle1 := by decide
 hle2 := by decide

def PBC2 : PrimesBelowPCertificate 2 ![I2N0, I2N1, I2N1, I2N2, I2N2] where
  Ip := by
    intro i
    fin_cases i
    exact isPrimeI2N0
    exact isPrimeI2N1
    exact isPrimeI2N1
    exact isPrimeI2N2
    exact isPrimeI2N2
  hPprod := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI2N3, Set.range_unique]
    dsimp ; congr
    erw [B_int_repr]
    rfl


-- Ideals above 5

def I5N : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0, 0, 0], ![2, 1, 0, 0, 0]] i)))

def SI5N: IdealEqSpanCertificate O ℤ timesTableO I5N
 ![![5, 0, 0, 0, 0], ![2, 1, 0, 0, 0]]
 ![![5, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![5, 0, 0, 0, 0], ![0, 5, 0, 0, 0], ![0, 0, 5, 0, 0], ![0, 0, 0, 5, 0], ![0, 0, 0, 0, 5]], ![![2, 1, 0, 0, 0], ![0, 2, 1, 0, 0], ![0, 1, 2, 2, 0], ![3, -1, 2, 5, 12], ![0, 0, 0, -2, -1]]]
  hmulB := by decide
  f := ![![![111, 56, 49, 70, 96], ![-215, -15, -75, -40, 0]], ![![54, 26, 23, 34, 48], ![-104, -5, -35, -20, 0]], ![![55, 27, 25, 36, 48], ![-107, -4, -40, -20, 0]], ![![53, 26, 24, 35, 48], ![-101, -6, -37, -20, 0]], ![![88, 44, 39, 56, 77], ![-170, -11, -60, -32, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-2, 5, 0, 0, 0], ![-1, 0, 5, 0, 0], ![-3, 0, 0, 5, 0], ![-4, 0, 0, 0, 5]], ![![0, 1, 0, 0, 0], ![-1, 2, 1, 0, 0], ![-2, 1, 2, 2, 0], ![-12, -1, 2, 5, 12], ![2, 0, 0, -2, -1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI5N : Nat.card (O ⧸ I5N) = 5 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI5N)

lemma isPrimeI5N : Ideal.IsPrime I5N := prime_ideal_of_norm_prime hp5.out _ NI5N
def MulI5N0 : IdealMulEqCertificate O ℤ timesTableO (I5N) I5N
  ![![5, 0, 0, 0, 0], ![2, 1, 0, 0, 0]] ![![5, 0, 0, 0, 0], ![2, 1, 0, 0, 0]]
  ![![5, 0, 0, 0, 0], ![1, -1, -2, -1, -3]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![25, 0, 0, 0, 0], ![10, 5, 0, 0, 0]], ![![10, 5, 0, 0, 0], ![4, 4, 1, 0, 0]]]
 hmul := by decide
 f :=  ![![![![16201279, 9554492, 1837911, 1600330, 2142240], ![-39167515, -3859329, -1765215, -892464, 0]], ![![0, 0, 0, 0, 0], ![8036, -19824, -348, 4, 0]]], ![![![12463118, 7349961, 1413847, 1231084, 1647957], ![-30130298, -2968856, -1357926, -686544, 0]], ![![0, 0, 0, 0, 0], ![6184, -15252, -268, 3, 0]]]]
 g :=  ![![![![1135, -10, 780, 270, 690], ![-550, 1600, 100, 0, 0]], ![![1045, 0, 720, 253, 639], ![-505, 1470, 100, 0, 0]]], ![![![1045, 0, 720, 253, 639], ![-505, 1470, 100, 0, 0]], ![![615, 1, 423, 149, 375], ![-299, 864, 60, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI5N1 : IdealMulEqCertificate O ℤ timesTableO (I5N*I5N) I5N
  ![![5, 0, 0, 0, 0], ![1, -1, -2, -1, -3]] ![![5, 0, 0, 0, 0], ![2, 1, 0, 0, 0]]
  ![![5, 0, 0, 0, 0], ![1, 6, -3, -1, -5]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI5N0
 hI2 := rfl
 M :=  ![![![25, 0, 0, 0, 0], ![10, 5, 0, 0, 0]], ![![5, -5, -10, -5, -15], ![-1, -2, -7, -3, -9]]]
 hmul := by decide
 f :=  ![![![![-255332124, -150583281, -29040690, -25280341, -33706629], ![617297238, 60744039, 28104673, 14022048, 0]], ![![0, 0, 0, 0, 0], ![-168611, 18174, 336, 0, 0]]], ![![![-90879140, -53596386, -10336315, -8997912, -11997038], ![219711650, 21620333, 10003166, 4990800, 0]], ![![0, 0, 0, 0, 0], ![-60013, 6468, 120, 0, 0]]]]
 g :=  ![![![![-35, 15, 45, 10, 20], ![-25, -75, 0, 0, 0]], ![![-6, 4, 9, 2, 4], ![-5, -15, 0, 0, 0]]], ![![![-15, 5, 16, 3, 5], ![-10, -30, 0, 0, 0]], ![![-2, -1, 1, 0, 0], ![0, -3, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI5N2 : IdealMulEqCertificate O ℤ timesTableO (I5N*I5N*I5N) I5N
  ![![5, 0, 0, 0, 0], ![1, 6, -3, -1, -5]] ![![5, 0, 0, 0, 0], ![2, 1, 0, 0, 0]]
  ![![5, 0, 0, 0, 0], ![1, 4, 2, 1, 2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI5N1
 hI2 := rfl
 M :=  ![![![25, 0, 0, 0, 0], ![10, 5, 0, 0, 0]], ![![5, 30, -15, -5, -25], ![-1, 11, -2, -1, -7]]]
 hmul := by decide
 f :=  ![![![![3080, 1826, 515, 485, 373], ![-7484, -559, -829, -144, 0]], ![![0, 0, 0, 0, 0], ![67, -24, 0, 0, 0]]], ![![![324, 170, -317, -354, 115], ![-702, -449, 1017, -72, 0]], ![![0, 0, 0, 0, 0], ![-145, 48, 0, 0, 0]]]]
 g :=  ![![![![4, -4, -2, -1, -2], ![5, 0, 0, 0, 0]], ![![1, -3, -2, -1, -2], ![5, 0, 0, 0, 0]]], ![![![0, 4, -5, -2, -7], ![2, 1, 0, 0, 0]], ![![0, 3, 0, 0, -1], ![-1, 0, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI5N3 : IdealMulEqCertificate O ℤ timesTableO (I5N*I5N*I5N*I5N) I5N
  ![![5, 0, 0, 0, 0], ![1, 4, 2, 1, 2]] ![![5, 0, 0, 0, 0], ![2, 1, 0, 0, 0]]
  ![![5, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI5N2
 hI2 := rfl
 M :=  ![![![25, 0, 0, 0, 0], ![10, 5, 0, 0, 0]], ![![5, 20, 10, 5, 10], ![5, 10, 10, 5, 10]]]
 hmul := by decide
 f :=  ![![![![378471, 223192, 42838, 37238, 49920], ![-914953, -90256, -41087, -20784, 0]], ![![0, 0, 0, 0, 0], ![-96, 0, 0, 0, 0]]]]
 g :=  ![![![![5, 0, 0, 0, 0]], ![![2, 1, 0, 0, 0]]], ![![![1, 4, 2, 1, 2]], ![![1, 2, 2, 1, 2]]]]
 hle1 := by decide
 hle2 := by decide

def PBC5 : PrimesBelowPCertificate 5 ![I5N, I5N, I5N, I5N, I5N] where
  Ip := by
    intro i
    fin_cases i
    exact isPrimeI5N
    exact isPrimeI5N
    exact isPrimeI5N
    exact isPrimeI5N
    exact isPrimeI5N
  hPprod := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI5N3, Set.range_unique]
    dsimp ; congr
    erw [B_int_repr]
    rfl

-- Ideals above 7

instance hp7 : Fact (Nat.Prime 7) := by decide

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 1, 1, 0, 1]] i)))

def SI7N0: IdealEqSpanCertificate O ℤ timesTableO I7N0
 ![![1, 1, 1, 0, 1]]
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![6, 3, 1, 0, 0], ![5, 6, 0, 1, 0], ![2, 5, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![1, 1, 1, 0, 1], ![0, 2, 1, 0, -3], ![0, 1, 2, 8, 9], ![12, -4, 8, 5, 36], ![-2, 2, -2, -6, -15]]]
  hmulB := by decide
  f := ![![![-15, -13, 15, 6, 25]], ![![18, -6, -1, -2, -3]], ![![-6, -11, 11, 4, 18]], ![![3, -15, 11, 3, 17]], ![![10, -8, 3, 0, 4]]]
  g := ![![![-1, -1, 1, 0, 1], ![0, 2, 1, 0, -3], ![-10, -14, 2, 8, 9], ![-19, -34, 8, 5, 36], ![10, 17, -2, -6, -15]]]
  hle1 := by decide
  hle2 := by decide

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 49 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI7N0)

def MemCI7N0 : IdealMemCertificate O ℤ B I7N0
  ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![6, 3, 1, 0, 0], ![5, 6, 0, 1, 0], ![2, 5, 0, 0, 1]] ![790, 805, 265, -2322, -2785] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI7N0
 g := ![2340, 3981, 265, -2322, -2785]
 hmem := by decide

def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [4, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 6], [0, 1]]
 g := ![![[2, 2], [6, 1]],![[0, 5], [5, 6]]]
 h' := ![![[6, 6], [4, 4], [0, 1]],![[0, 1], [0, 3], [6, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [1, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : PrimeIdeal O 7 where
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I7N0
  hcard := NI7N0
  P := [4, 1, 1]
  f := ofList [4, 1, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P7P0
  hneq := by decide
  hlen := by decide
  c := ![790, 805, 265, -2322, -2785]
  a := ![4, -7, 1, -4, 17]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI7N0
  hpmem := by
    show  _ ∈ I7N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI7N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := PrimeIdeal_isPrime PI7N0
def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -1, 1, 0, 1]] i)))

def SI7N1: IdealEqSpanCertificate O ℤ timesTableO I7N1
 ![![-1, -1, 1, 0, 1]]
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![2, 2, 1, 0, 0], ![5, 3, 0, 1, 0], ![4, 4, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![-1, -1, 1, 0, 1], ![0, 0, -1, 0, -3], ![0, -1, 0, 4, 9], ![6, -2, 4, -3, 12], ![-2, 2, -2, -2, -11]]]
  hmulB := by decide
  f := ![![![-5, 1, -5, -2, -7]], ![![-6, -8, -3, -2, -3]], ![![-4, -3, -4, -2, -5]], ![![-7, -3, -6, -3, -8]], ![![-6, -4, -4, -2, -5]]]
  g := ![![![-1, -1, 1, 0, 1], ![2, 2, -1, 0, -3], ![-8, -7, 0, 4, 9], ![-5, -7, 4, -3, 12], ![8, 8, -2, -2, -11]]]
  hle1 := by decide
  hle2 := by decide

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 49 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI7N1)

def MemCI7N1 : IdealMemCertificate O ℤ B I7N1
  ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![2, 2, 1, 0, 0], ![5, 3, 0, 1, 0], ![4, 4, 0, 0, 1]] ![349, -214, 234, 292, 1371] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI7N1
 g := ![-1009, -1006, 234, 292, 1371]
 hmem := by decide

def P7P1 : CertificateIrreducibleZModOfList' 7 2 2 2 [5, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 6], [0, 1]]
 g := ![![[2, 2], [4, 1]],![[3, 5], [1, 6]]]
 h' := ![![[4, 6], [1, 4], [0, 1]],![[0, 1], [3, 3], [4, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [6, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N1 : PrimeIdeal O 7 where
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I7N1
  hcard := NI7N1
  P := [5, 3, 1]
  f := ofList [5, 3, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P7P1
  hneq := by decide
  hlen := by decide
  c := ![349, -214, 234, 292, 1371]
  a := ![4, -1, 4, 5, 17]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI7N1
  hpmem := by
    show  _ ∈ I7N1.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI7N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := PrimeIdeal_isPrime PI7N1
def I7N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 0, 0, 0, 1]] i)))

def SI7N2: IdealEqSpanCertificate O ℤ timesTableO I7N2
 ![![1, 0, 0, 0, 1]]
 ![![7, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![1, 0, 0, 0, 1], ![0, 1, 0, -2, -3], ![-6, 2, -3, 0, -15], ![0, -5, 1, 13, 24], ![4, 0, 2, -4, 3]]]
  hmulB := by decide
  f := ![![![15, 0, 10, 4, 13]], ![![6, 3, 4, 2, 5]], ![![9, 2, 9, 4, 12]], ![![9, 1, 7, 3, 9]], ![![1, 0, 0, 0, 0]]]
  g := ![![![0, 0, 0, 0, 1], ![1, 1, 0, -2, -3], ![2, 2, -3, 0, -15], ![-8, -5, 1, 13, 24], ![1, 0, 2, -4, 3]]]
  hle1 := by decide
  hle2 := by decide

lemma NI7N2 : Nat.card (O ⧸ I7N2) = 7 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI7N2)

lemma isPrimeI7N2 : Ideal.IsPrime I7N2 := prime_ideal_of_norm_prime hp7.out _ NI7N2
def MulI7N0 : IdealMulEqCertificate O ℤ timesTableO (I7N0) I7N1
  ![![1, 1, 1, 0, 1]] ![![-1, -1, 1, 0, 1]]
  ![![-3, 0, -2, 2, -4]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![-3, 0, -2, 2, -4]]]
 hmul := by decide
 f :=  ![![![![1, 0, 0, 0, 0]]]]
 g :=  ![![![![1, 0, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI7N1 : IdealMulEqCertificate O ℤ timesTableO (I7N0*I7N1) I7N2
  ![![-3, 0, -2, 2, -4]] ![![1, 0, 0, 0, 1]]
  ![![7, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI7N0
 hI2 := rfl
 M :=  ![![![-7, -14, 0, 42, 63]]]
 hmul := by decide
 f :=  ![![![![11, -18, 2, -2, 3]]]]
 g :=  ![![![![-1, -2, 0, 6, 9]]]]
 hle1 := by decide
 hle2 := by decide

def PBC7 : PrimesBelowPCertificate 7 ![I7N0, I7N1, I7N2] where
  Ip := by
    intro i
    fin_cases i
    exact isPrimeI7N0
    exact isPrimeI7N1
    exact isPrimeI7N2
  hPprod := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI7N1, Set.range_unique]
    dsimp ; congr
    erw [B_int_repr]
    rfl

-- Primes above 11

instance hp11 : Fact (Nat.Prime 11) := by decide

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0], ![-3, 9, -3, -1, -5]] i)))

def SI11N0: IdealEqSpanCertificate O ℤ timesTableO I11N0
 ![![11, 0, 0, 0, 0], ![-3, 9, -3, -1, -5]]
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![9, 3, 1, 0, 0], ![3, 6, 0, 1, 0], ![10, 4, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]], ![![-3, 9, -3, -1, -5], ![-3, -5, 7, 1, 3], ![3, 3, -3, 11, 3], ![18, -3, 9, 10, 60], ![-2, -1, 1, -10, -19]]]
  hmulB := by decide
  f := ![![![787, 466, -1226, -118, -294], ![660, 2200, -22, 0, 0]], ![![1305, 782, -2039, -189, -489], ![1089, 3652, -44, 0, 0]], ![![969, 579, -1513, -144, -364], ![809, 2712, -29, 0, 0]], ![![927, 552, -1446, -135, -346], ![776, 2592, -30, 0, 0]], ![![1190, 708, -1856, -176, -445], ![996, 3328, -36, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-9, -3, 11, 0, 0], ![-3, -6, 0, 11, 0], ![-10, -4, 0, 0, 11]], ![![7, 4, -3, -1, -5], ![-9, -4, 7, 1, 3], ![-3, -6, -3, 11, 3], ![-63, -30, 9, 10, 60], ![19, 12, 1, -10, -19]]]
  hle1 := by decide
  hle2 := by decide

lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI11N0)

def MemCI11N0 : IdealMemCertificate O ℤ B I11N0
  ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![9, 3, 1, 0, 0], ![3, 6, 0, 1, 0], ![10, 4, 0, 0, 1]] ![7106, -4202, 4564, 4712, 26139] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI11N0
 g := ![-28136, -13702, 4564, 4712, 26139]
 hmem := by decide

def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [10, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 10], [0, 1]]
 g := ![![[8, 1], [0, 9], [1]],![[5, 10], [6, 2], [1]]]
 h' := ![![[8, 10], [0, 10], [1, 8], [0, 1]],![[0, 1], [3, 1], [10, 3], [8, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [4, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : PrimeIdeal O 11 where
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I11N0
  hcard := NI11N0
  P := [10, 3, 1]
  f := ofList [10, 3, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P11P0
  hneq := by decide
  hlen := by decide
  c := ![7106, -4202, 4564, 4712, 26139]
  a := ![-19, 5, -17, -21, -75]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI11N0
  hpmem := by
    show  _ ∈ I11N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI11N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := PrimeIdeal_isPrime PI11N0
def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0], ![-1, 4, -2, -1, -3]] i)))

def SI11N1: IdealEqSpanCertificate O ℤ timesTableO I11N1
 ![![11, 0, 0, 0, 0], ![-1, 4, -2, -1, -3]]
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![5, 4, 1, 0, 0], ![1, 6, 0, 1, 0], ![4, 5, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]], ![![-1, 4, -2, -1, -3], ![-3, -2, 2, -1, -3], ![-3, 0, -4, 7, -3], ![12, -6, 6, 10, 48], ![0, 1, 1, -8, -13]]]
  hmulB := by decide
  f := ![![![10769, 7216, -6996, 3236, 10716], ![-286, 39116, 462, 0, 0]], ![![1769, 1185, -1148, 531, 1761], ![-44, 6424, 77, 0, 0]], ![![5376, 3604, -3493, 1615, 5349], ![-146, 19528, 231, 0, 0]], ![![1944, 1302, -1262, 584, 1935], ![-49, 7060, 84, 0, 0]], ![![4720, 3163, -3066, 1418, 4697], ![-125, 17144, 203, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-5, -4, 11, 0, 0], ![-1, -6, 0, 11, 0], ![-4, -5, 0, 0, 11]], ![![2, 3, -2, -1, -3], ![0, 1, 2, -1, -3], ![2, -1, -4, 7, -3], ![-20, -30, 6, 10, 48], ![5, 10, 1, -8, -13]]]
  hle1 := by decide
  hle2 := by decide

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 121 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI11N1)

def MemCI11N1 : IdealMemCertificate O ℤ B I11N1
  ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![5, 4, 1, 0, 0], ![1, 6, 0, 1, 0], ![4, 5, 0, 0, 1]] ![81173, -41165, 48740, 29303, 255868] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI11N1
 g := ![-110482, -153753, 48740, 29303, 255868]
 hmem := by decide

def P11P1 : CertificateIrreducibleZModOfList' 11 2 2 3 [4, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 10], [0, 1]]
 g := ![![[6, 3], [8, 4], [1]],![[0, 8], [0, 7], [1]]]
 h' := ![![[9, 10], [1, 6], [7, 9], [0, 1]],![[0, 1], [0, 5], [0, 2], [9, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [2, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N1 : PrimeIdeal O 11 where
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I11N1
  hcard := NI11N1
  P := [4, 2, 1]
  f := ofList [4, 2, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P11P1
  hneq := by decide
  hlen := by decide
  c := ![81173, -41165, 48740, 29303, 255868]
  a := ![-57, 20, -47, -57, -230]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI11N1
  hpmem := by
    show  _ ∈ I11N1.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI11N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := PrimeIdeal_isPrime PI11N1
def I11N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0], ![4, 1, 0, 0, 0]] i)))

def SI11N2: IdealEqSpanCertificate O ℤ timesTableO I11N2
 ![![11, 0, 0, 0, 0], ![4, 1, 0, 0, 0]]
 ![![11, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]], ![![4, 1, 0, 0, 0], ![0, 4, 1, 0, 0], ![0, 1, 4, 2, 0], ![3, -1, 2, 7, 12], ![0, 0, 0, -2, 1]]]
  hmulB := by decide
  f := ![![![1130, 286, 225, 319, 420], ![-2816, -77, -407, -385, 0]], ![![485, 123, 97, 137, 180], ![-1209, -33, -176, -165, 0]], ![![646, 163, 128, 182, 240], ![-1610, -43, -231, -220, 0]], ![![807, 205, 161, 228, 300], ![-2011, -57, -291, -275, 0]], ![![510, 128, 102, 145, 191], ![-1270, -32, -185, -175, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-4, 11, 0, 0, 0], ![-6, 0, 11, 0, 0], ![-8, 0, 0, 11, 0], ![-5, 0, 0, 0, 11]], ![![0, 1, 0, 0, 0], ![-2, 4, 1, 0, 0], ![-4, 1, 4, 2, 0], ![-11, -1, 2, 7, 12], ![1, 0, 0, -2, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI11N2 : Nat.card (O ⧸ I11N2) = 11 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI11N2)

lemma isPrimeI11N2 : Ideal.IsPrime I11N2 := prime_ideal_of_norm_prime hp11.out _ NI11N2
def MulI11N0 : IdealMulEqCertificate O ℤ timesTableO (I11N0) I11N1
  ![![11, 0, 0, 0, 0], ![-3, 9, -3, -1, -5]] ![![11, 0, 0, 0, 0], ![-1, 4, -2, -1, -3]]
  ![![11, 0, 0, 0, 0], ![1, -14, 17, 6, 27]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![121, 0, 0, 0, 0], ![-11, 44, -22, -11, -33]], ![![-33, 99, -33, -11, -55], ![-27, -29, 25, 3, 8]]]
 hmul := by decide
 f :=  ![![![![4678450488, 3136865629, -3039991859, 1404685927, 4654983277], ![-129149092, 16995106788, 202077720, 0, 0]], ![![157587, 26040, 0, 0, 0], ![22, 0, 0, 0, 0]]], ![![![152468766, 102229123, -99072084, 45778171, 151703990], ![-4208921, 553863520, 6585579, 0, 0]], ![![5175, 840, 0, 0, 0], ![2, 0, 0, 0, 0]]]]
 g :=  ![![![![10, 14, -17, -6, -27], ![11, 0, 0, 0, 0]], ![![-1, 4, -2, -1, -3], ![0, 0, 0, 0, 0]]], ![![![-3, 9, -3, -1, -5], ![0, 0, 0, 0, 0]], ![![-3, 5, -7, -3, -14], ![6, 0, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI11N1 : IdealMulEqCertificate O ℤ timesTableO (I11N0*I11N1) I11N2
  ![![11, 0, 0, 0, 0], ![1, -14, 17, 6, 27]] ![![11, 0, 0, 0, 0], ![4, 1, 0, 0, 0]]
  ![![11, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI11N0
 hI2 := rfl
 M :=  ![![![121, 0, 0, 0, 0], ![44, 11, 0, 0, 0]], ![![11, -154, 187, 66, 297], ![22, -44, 66, 22, 99]]]
 hmul := by decide
 f :=  ![![![![549442, 144903, 126142, 163892, 201873], ![-1370638, -36813, -248509, -187460, 0]], ![![1071, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]]
 g :=  ![![![![11, 0, 0, 0, 0]], ![![4, 1, 0, 0, 0]]], ![![![1, -14, 17, 6, 27]], ![![2, -4, 6, 2, 9]]]]
 hle1 := by decide
 hle2 := by decide

def PBC11 : PrimesBelowPCertificate 11 ![I11N0, I11N1, I11N2] where
  Ip := by
    intro i
    fin_cases i
    exact isPrimeI11N0
    exact isPrimeI11N1
    exact isPrimeI11N2
  hPprod := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI11N1, Set.range_unique]
    dsimp ; congr
    erw [B_int_repr]
    rfl


---- Ideal above 13

instance hp13 : Fact (Nat.Prime 13) := by decide

def I13N : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0]] i)))

def SI13N: IdealEqSpanCertificate O ℤ timesTableO I13N
 ![![13, 0, 0, 0, 0]]
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI13N : Nat.card (O ⧸ I13N) = 371293 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI13N)

def MemCI13N : IdealMemCertificate O ℤ B I13N
  ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]] ![7892668849, 15836162836, -334903452, -47135215296, -71252044968] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI13N
 g := ![607128373, 1218166372, -25761804, -3625785792, -5480926536]
 hmem := by decide

def P13P : CertificateIrreducibleZModOfList' 13 5 2 3 [9, 4, 0, 9, 12, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [7, 3, 11, 9, 1], [5, 6, 2, 7, 8], [12, 12, 1, 8, 9], [3, 4, 12, 2, 8], [0, 1]]
 g := ![![[5, 5, 11, 0, 12], [1, 1], []],![[5, 8, 5, 10, 10, 1, 5, 9], [12, 0, 10, 9], [5, 6, 4, 11, 10, 9, 2, 1]],![[8, 5, 2, 3, 3, 12, 11, 7], [5, 3, 5, 1], [2, 3, 4, 9, 1, 4, 10, 5]],![[5, 8, 0, 9, 3, 10, 8, 1], [7, 4, 1, 12], [10, 7, 12, 9, 12, 7, 8, 1]],![[0, 10, 7, 12, 1, 11, 0, 7], [12, 6, 12, 3], [9, 8, 4, 8, 1, 1, 12, 5]]]
 h' := ![![[7, 3, 11, 9, 1], [4, 0, 9, 4, 5], [0, 0, 0, 1], [0, 1]],![[5, 6, 2, 7, 8], [10, 11, 2, 12, 10], [12, 3, 4, 2, 10], [7, 3, 11, 9, 1]],![[12, 12, 1, 8, 9], [3, 12, 0, 8, 10], [3, 12, 5, 11, 12], [5, 6, 2, 7, 8]],![[3, 4, 12, 2, 8], [2, 1, 5, 5, 4], [0, 11, 7, 5, 8], [12, 12, 1, 8, 9]],![[0, 1], [0, 2, 10, 10, 10], [11, 0, 10, 7, 9], [3, 4, 12, 2, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 12, 2, 5], [], [], []]
 b := ![[], [6, 3, 10, 9, 8], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N : PrimeIdeal O 13 where
  r := 5
  n := 5
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I13N
  hcard := NI13N
  P := [9, 4, 0, 9, 12, 1]
  f := ofList [9, 4, 0, 9, 12, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P13P
  hneq := by decide
  hlen := by decide
  c := ![7892668849, 15836162836, -334903452, -47135215296, -71252044968]
  a := ![11, -4, 9, 9, 42]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI13N
  hpmem := by
    show  _ ∈ I13N.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI13N]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI13N : Ideal.IsPrime I13N := PrimeIdeal_isPrime PI13N
def PBC13 : PrimesBelowPCertificate 13 ![I13N] where
  Ip := by
    intro i
    fin_cases i
    exact isPrimeI13N
  hPprod := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    unfold I13N
    rw [Set.range_unique]
    dsimp ; congr
    erw [B_int_repr]
    rfl


def PB17 : PrimesBelowBoundCertificate O
