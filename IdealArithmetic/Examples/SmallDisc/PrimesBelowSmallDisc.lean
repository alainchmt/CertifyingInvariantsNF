import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Examples.SmallDisc.RISmallDisc
import IdealArithmetic.ClassGroupGeneration

open Classical Polynomial

noncomputable section


-- Primes below 2
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] i)))

def SI2N0: IdealEqSpanCertificate O ℤ timesTableO I2N0
 ![![2, 0, 0, 0, 0], ![0, 0, 1, 0, 0]]
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![0, 0, 1, 0, 0], ![0, 1, 0, 2, 0], ![0, 0, 0, 0, 1], ![2, -3, 0, -1, 0], ![0, 2, -5, 0, 0]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, -1, 0], ![0, 1, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0]], ![![1, -2, 0, -1, 0], ![0, 1, 0, -1, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![0, 0, 1, 0, 0], ![0, 1, 0, 2, 0], ![0, 0, 0, 0, 1], ![1, -3, 0, -1, 0], ![0, 2, -5, 0, 0]]]
  hle1 := by decide
  hle2 := by decide

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0
def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![1, 1, 0, 1, 0]] i)))

def SI2N1: IdealEqSpanCertificate O ℤ timesTableO I2N1
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 1, 0]]
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![1, 1, 0, 1, 0], ![0, 1, 1, 0, 1], ![2, -2, 1, 1, 0], ![0, 1, -3, 1, 0], ![2, -5, 2, -5, 1]]]
  hmulB := by decide
  f := ![![![4, -1, 1, 2, 0], ![-2, 0, -2, 0, 0]], ![![-4, 1, -1, -3, -1], ![2, 2, 3, 1, 0]], ![![-6, 0, -1, -5, -1], ![5, 2, 4, 1, 0]], ![![6, -3, 2, 4, 1], ![-1, -2, -5, -1, 0]], ![![2, -1, 0, 1, 0], ![-1, 1, -1, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![-1, 0, 2, 0, 0], ![-1, 0, 0, 2, 0], ![-1, 0, 0, 0, 2]], ![![0, 1, 0, 1, 0], ![-1, 1, 1, 0, 1], ![0, -2, 1, 1, 0], ![1, 1, -3, 1, 0], ![2, -5, 2, -5, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulEqCertificate O ℤ timesTableO (I2N0) I2N1
  ![![2, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] ![![2, 0, 0, 0, 0], ![1, 1, 0, 1, 0]]
  ![![4, 0, 0, 1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![4, 0, 0, 0, 0], ![2, 2, 0, 2, 0]], ![![0, 0, 2, 0, 0], ![2, -2, 1, 1, 0]]]
 hmul := by decide
 f :=  ![![![![-366, 108, -109, -256, -75], ![149, 148, 288, 69, 0]], ![![-11, 0, 0, 0, 0], ![10, 2, 0, -1, 0]]]]
 g :=  ![![![![2, -2, 2, 0, 0]], ![![3, -2, 0, 2, -1]]], ![![![0, -1, 1, -2, 1]], ![![2, -5, 4, -3, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI2N1 : IdealMulEqCertificate O ℤ timesTableO (I2N0*I2N1) I2N1
  ![![4, 0, 0, 1, 1]] ![![2, 0, 0, 0, 0], ![1, 1, 0, 1, 0]]
  ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI2N0
 hI2 := rfl
 M :=  ![![![8, 0, 0, 2, 2], ![6, 0, -1, 0, 1]]]
 hmul := by decide
 f :=  ![![![![-1, 1, -1, 2, -1], ![1, 1, 0, 0, 1]]], ![![![-4, 4, -4, 4, -1], ![4, 0, 0, -1, 2]]]]
 g :=  ![![![![4, 0, 0, 1, 1], ![0, 0, 0, 0, 0]], ![![3, 0, 0, 0, 0], ![0, 0, 0, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI2N2 : IdealMulEqCertificate O ℤ timesTableO (I2N0*I2N1*I2N1) I2N1
  ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] ![![2, 0, 0, 0, 0], ![1, 1, 0, 1, 0]]
  ![![2, 0, 0, 0, 0], ![4, 1, 1, 2, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI2N1
 hI2 := rfl
 M :=  ![![![4, 0, 0, 0, 0], ![2, 2, 0, 2, 0]], ![![0, 2, 0, 0, 0], ![0, 1, 1, 0, 1]]]
 hmul := by decide
 f :=  ![![![![232, -73, 70, 165, 44], ![-89, -94, -187, -45, 0]], ![![0, 0, 0, 0, 0], ![9, 0, 0, 3, 0]]], ![![![712, -219, 215, 508, 136], ![-278, -290, -572, -138, 0]], ![![0, 0, 0, 0, 0], ![28, 0, 0, 9, 0]]]]
 g :=  ![![![![2, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![-1, 0, -1, 0, 0], ![2, -1, 0, 0, 0]]], ![![![0, 0, -1, 0, 1], ![2, -2, 0, 0, 0]], ![![-2, 0, 0, -1, 0], ![1, 0, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI2N3 : IdealMulEqCertificate O ℤ timesTableO (I2N0*I2N1*I2N1*I2N1) I2N1
  ![![2, 0, 0, 0, 0], ![4, 1, 1, 2, 1]] ![![2, 0, 0, 0, 0], ![1, 1, 0, 1, 0]]
  ![![2, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI2N2
 hI2 := rfl
 M :=  ![![![4, 0, 0, 0, 0], ![2, 2, 0, 2, 0]], ![![8, 2, 2, 4, 2], ![8, 0, -2, 2, 2]]]
 hmul := by decide
 f :=  ![![![![118, -34, 37, 78, 23], ![-47, -43, -88, -18, 0]], ![![0, 0, 0, 0, 0], ![-3, 0, 0, 0, 0]]]]
 g :=  ![![![![2, 0, 0, 0, 0]], ![![1, 1, 0, 1, 0]]], ![![![4, 1, 1, 2, 1]], ![![4, 0, -1, 1, 1]]]]
 hle1 := by decide
 hle2 := by decide

def PBC2 : PrimesBelowPCertificate 2 ![I2N0, I2N1, I2N1, I2N1, I2N1] where
  Ip := by
    intro i
    fin_cases i
    exact isPrimeI2N0
    exact isPrimeI2N1
    exact isPrimeI2N1
    exact isPrimeI2N1
    exact isPrimeI2N1
  hPprod := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI2N3, Set.range_unique]
    dsimp ; congr
    erw [B_int_repr]
    rfl

  --- Primes below 3

def I3N : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0]] i)))

def SI3N: IdealEqSpanCertificate O ℤ timesTableO I3N
 ![![3, 0, 0, 0, 0]]
 ![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI3N : Nat.card (O ⧸ I3N) = 243 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI3N)

def MemCI3N : IdealMemCertificate O ℤ B I3N
  ![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]] ![3952002, -2904210, -1647600, 3591990, -1966200] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI3N
 g := ![1317334, -968070, -549200, 1197330, -655400]
 hmem := by decide

def P3P : CertificateIrreducibleZModOfList' 3 5 2 1 [1, 0, 2, 2, 2, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 0, 0, 1], [2, 2, 2, 1], [2, 0, 1, 1, 1], [0, 0, 0, 0, 2], [0, 1]]
 g := ![![[]],![[1, 1, 2, 1, 1]],![[0, 0, 2, 1, 1]],![[2, 0, 2, 2, 2, 2, 1, 1]],![[0, 2, 0, 2, 2, 1, 2, 2]]]
 h' := ![![[0, 0, 0, 1], [0, 1]],![[2, 2, 2, 1], [0, 0, 0, 1]],![[2, 0, 1, 1, 1], [2, 2, 2, 1]],![[0, 0, 0, 0, 2], [2, 0, 1, 1, 1]],![[0, 1], [0, 0, 0, 0, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 0, 1], [], [], []]
 b := ![[], [0, 0, 2, 1, 2], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N : PrimeIdeal O 3 where
  r := 5
  n := 5
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I3N
  hcard := NI3N
  P := [1, 0, 2, 2, 2, 1]
  f := ofList [1, 0, 2, 2, 2, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P3P
  hneq := by decide
  hlen := by decide
  c := ![3952002, -2904210, -1647600, 3591990, -1966200]
  a := ![-1, 10, 0, 10, 0]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI3N
  hpmem := by
    show  _ ∈ I3N.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI3N]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI3N : Ideal.IsPrime I3N := PrimeIdeal_isPrime PI3N
def PBC3 : PrimesBelowPCertificate 3 ![I3N] where
  Ip := by
    intro i
    fin_cases i
    exact isPrimeI3N
  hPprod := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    unfold I3N
    rw [Set.range_unique]
    dsimp ; congr
    erw [B_int_repr]
    rfl

--- Primes below 5

def I5N : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -1, 0, 0, 0]] i)))

def SI5N: IdealEqSpanCertificate O ℤ timesTableO I5N
 ![![1, -1, 0, 0, 0]]
 ![![5, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![1, -1, 0, 0, 0], ![0, 1, -2, 0, 0], ![0, -1, 1, -2, 0], ![0, 0, 1, 1, -1], ![-4, 5, 0, 0, 1]]]
  hmulB := by decide
  f := ![![![21, 3, 2, 4, 4]], ![![20, 3, 2, 4, 4]], ![![10, 1, 1, 2, 2]], ![![16, 2, 1, 3, 3]], ![![5, 0, 0, 0, 1]]]
  g := ![![![1, -1, 0, 0, 0], ![0, 1, -2, 0, 0], ![2, -1, 1, -2, 0], ![-1, 0, 1, 1, -1], ![-5, 5, 0, 0, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI5N : Nat.card (O ⧸ I5N) = 5 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI5N)

lemma isPrimeI5N : Ideal.IsPrime I5N := prime_ideal_of_norm_prime hp5.out _ NI5N
def MulI5N0 : IdealMulEqCertificate O ℤ timesTableO (I5N) I5N
  ![![1, -1, 0, 0, 0]] ![![1, -1, 0, 0, 0]]
  ![![1, -2, 2, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![1, -2, 2, 0, 0]]]
 hmul := by decide
 f :=  ![![![![1, 0, 0, 0, 0]]]]
 g :=  ![![![![1, 0, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI5N1 : IdealMulEqCertificate O ℤ timesTableO (I5N*I5N) I5N
  ![![1, -2, 2, 0, 0]] ![![1, -1, 0, 0, 0]]
  ![![1, -5, 6, -4, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI5N0
 hI2 := rfl
 M :=  ![![![1, -5, 6, -4, 0]]]
 hmul := by decide
 f :=  ![![![![1, 0, 0, 0, 0]]]]
 g :=  ![![![![1, 0, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI5N2 : IdealMulEqCertificate O ℤ timesTableO (I5N*I5N*I5N) I5N
  ![![1, -5, 6, -4, 0]] ![![1, -1, 0, 0, 0]]
  ![![1, -12, 12, -16, 4]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI5N1
 hI2 := rfl
 M :=  ![![![1, -12, 12, -16, 4]]]
 hmul := by decide
 f :=  ![![![![1, 0, 0, 0, 0]]]]
 g :=  ![![![![1, 0, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI5N3 : IdealMulEqCertificate O ℤ timesTableO (I5N*I5N*I5N*I5N) I5N
  ![![1, -12, 12, -16, 4]] ![![1, -1, 0, 0, 0]]
  ![![5, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI5N2
 hI2 := rfl
 M :=  ![![![-15, -5, 20, -40, 20]]]
 hmul := by decide
 f :=  ![![![![10149, 1023, 614, 1564, 1992]]]]
 g :=  ![![![![-3, -1, 4, -8, 4]]]]
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

--- Primes below 7

instance hp7 : Fact (Nat.Prime 7) := by decide

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-15, -2, -2, -3, -3]] i)))

def SI7N0: IdealEqSpanCertificate O ℤ timesTableO I7N0
 ![![-15, -2, -2, -3, -3]]
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![4, 0, 6, 1, 0], ![1, 3, 4, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![-15, -2, -2, -3, -3], ![-12, -2, -1, -4, -3], ![-6, 1, 0, -1, -2], ![2, 3, 2, 2, 1], ![-2, 0, 4, 3, 0]]]
  hmulB := by decide
  f := ![![![-1, 0, 1, -1, 0]], ![![0, 0, 1, 2, -1]], ![![-2, 3, -1, 1, 1]], ![![-2, 2, 0, 0, 1]], ![![-1, 2, -1, 2, 0]]]
  g := ![![![0, 1, 4, -3, -3], ![1, 1, 5, -4, -3], ![0, 1, 2, -1, -2], ![-1, 0, -2, 2, 1], ![-2, 0, -2, 3, 0]]]
  hle1 := by decide
  hle2 := by decide

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 343 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI7N0)

def MemCI7N0 : IdealMemCertificate O ℤ B I7N0
  ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![4, 0, 6, 1, 0], ![1, 3, 4, 0, 1]] ![-79, 164, -130, 36, 22] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI7N0
 g := ![-35, 14, -62, 36, 22]
 hmem := by decide

def P7P0 : CertificateIrreducibleZModOfList' 7 3 2 2 [3, 3, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 1, 6], [1, 5, 1], [0, 1]]
 g := ![![[1, 4, 4], [1]],![[1, 3], [3, 2, 5, 6]],![[6, 3, 4, 4], [1, 0, 6, 1]]]
 h' := ![![[4, 1, 6], [4, 4, 5], [0, 1]],![[1, 5, 1], [6, 5], [4, 1, 6]],![[0, 1], [5, 5, 2], [1, 5, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2], []]
 b := ![[], [4, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : PrimeIdeal O 7 where
  r := 5
  n := 3
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I7N0
  hcard := NI7N0
  P := [3, 3, 2, 1]
  f := ofList [3, 3, 2, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P7P0
  hneq := by decide
  hlen := by decide
  c := ![-79, 164, -130, 36, 22]
  a := ![-1, 1, -1, 0, 1]
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
def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0, 0], ![-3, 1, 0, 0, 0]] i)))

def SI7N1: IdealEqSpanCertificate O ℤ timesTableO I7N1
 ![![7, 0, 0, 0, 0], ![-3, 1, 0, 0, 0]]
 ![![7, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]], ![![-3, 1, 0, 0, 0], ![0, -3, 2, 0, 0], ![0, 1, -3, 2, 0], ![0, 0, -1, -3, 1], ![4, -5, 0, 0, -3]]]
  hmulB := by decide
  f := ![![![124, -80, 200, -126, -6], ![287, 77, 504, 42, 0]], ![![82, -54, 134, -84, -4], ![190, 49, 336, 28, 0]], ![![102, -65, 166, -105, -5], ![236, 67, 420, 35, 0]], ![![6, 0, 0, -1, 0], ![14, 6, 4, 0, 0]], ![![108, -70, 172, -108, -5], ![250, 64, 432, 36, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-4, 7, 0, 0, 0], ![-6, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![-6, 0, 0, 0, 7]], ![![-1, 1, 0, 0, 0], ![0, -3, 2, 0, 0], ![2, 1, -3, 2, 0], ![0, 0, -1, -3, 1], ![6, -5, 0, 0, -3]]]
  hle1 := by decide
  hle2 := by decide

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def I7N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0, 0], ![-2, 1, 0, 0, 0]] i)))

def SI7N2: IdealEqSpanCertificate O ℤ timesTableO I7N2
 ![![7, 0, 0, 0, 0], ![-2, 1, 0, 0, 0]]
 ![![7, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]], ![![-2, 1, 0, 0, 0], ![0, -2, 2, 0, 0], ![0, 1, -2, 2, 0], ![0, 0, -1, -2, 1], ![4, -5, 0, 0, -2]]]
  hmulB := by decide
  f := ![![![-91, 200, -382, 336, 30], ![-322, -154, -1386, -210, 0]], ![![-77, 171, -325, 286, 25], ![-272, -126, -1176, -175, 0]], ![![-73, 164, -314, 274, 25], ![-258, -122, -1134, -175, 0]], ![![-74, 168, -321, 281, 25], ![-262, -122, -1158, -175, 0]], ![![-39, 86, -164, 144, 13], ![-138, -65, -594, -90, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-5, 7, 0, 0, 0], ![-5, 0, 7, 0, 0], ![-6, 0, 0, 7, 0], ![-3, 0, 0, 0, 7]], ![![-1, 1, 0, 0, 0], ![0, -2, 2, 0, 0], ![-1, 1, -2, 2, 0], ![2, 0, -1, -2, 1], ![5, -5, 0, 0, -2]]]
  hle1 := by decide
  hle2 := by decide

lemma NI7N2 : Nat.card (O ⧸ I7N2) = 7 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI7N2)

lemma isPrimeI7N2 : Ideal.IsPrime I7N2 := prime_ideal_of_norm_prime hp7.out _ NI7N2
def MulI7N0 : IdealMulEqCertificate O ℤ timesTableO (I7N0) I7N1
  ![![-15, -2, -2, -3, -3]] ![![7, 0, 0, 0, 0], ![-3, 1, 0, 0, 0]]
  ![![7, 0, 0, 0, 0], ![2, 3, 2, 2, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![-105, -14, -14, -21, -21], ![33, 4, 5, 5, 6]]]
 hmul := by decide
 f :=  ![![![![-106042, -2050201, 1387767, 2235, -2], ![-247431, -4868880, -7802, 14, 0]]], ![![![-50463, -975652, 660412, 1064, -1], ![-117747, -2317008, -3713, 7, 0]]]]
 g :=  ![![![![-15, -2, -2, -3, -3], ![0, 0, 0, 0, 0]], ![![3, -2, -1, -1, 0], ![6, 0, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI7N1 : IdealMulEqCertificate O ℤ timesTableO (I7N0*I7N1) I7N2
  ![![7, 0, 0, 0, 0], ![2, 3, 2, 2, 1]] ![![7, 0, 0, 0, 0], ![-2, 1, 0, 0, 0]]
  ![![7, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI7N0
 hI2 := rfl
 M :=  ![![![49, 0, 0, 0, 0], ![-14, 7, 0, 0, 0]], ![![14, 21, 14, 14, 7], ![0, -7, 0, 0, 0]]]
 hmul := by decide
 f :=  ![![![![-398271, 245713, -106897, 115788, 1216], ![-1393954, -43869, -413760, -8507, 0]], ![![-5, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]]
 g :=  ![![![![7, 0, 0, 0, 0]], ![![-2, 1, 0, 0, 0]]], ![![![2, 3, 2, 2, 1]], ![![0, -1, 0, 0, 0]]]]
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

--- Primes below 11

instance hp11 : Fact (Nat.Prime 11) := by decide

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, -1, 0, 1, 1]] i)))

def SI11N0: IdealEqSpanCertificate O ℤ timesTableO I11N0
 ![![7, -1, 0, 1, 1]]
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![3, 8, 3, 1, 0], ![4, 2, 8, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![7, -1, 0, 1, 1], ![4, 2, -3, 0, 1], ![2, -2, 2, -3, 0], ![-2, 1, 1, 2, -2], ![-6, 7, 2, -1, 2]]]
  hmulB := by decide
  f := ![![![1, 1, 1, 1, 0]], ![![0, 2, 1, 2, 1]], ![![2, -2, 1, 1, 1]], ![![1, 1, 1, 2, 1]], ![![2, -1, 1, 1, 1]]]
  g := ![![![0, -1, -1, 1, 1], ![0, 0, -1, 0, 1], ![1, 2, 1, -3, 0], ![0, -1, 1, 2, -2], ![-1, 1, -1, -1, 2]]]
  hle1 := by decide
  hle2 := by decide

lemma NI11N0 : Nat.card (O ⧸ I11N0) = 1331 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI11N0)

def MemCI11N0 : IdealMemCertificate O ℤ B I11N0
  ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![3, 8, 3, 1, 0], ![4, 2, 8, 0, 1]] ![-10411, 9675, 3853, -4870, 3291] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI11N0
 g := ![-815, 3823, -715, -4870, 3291]
 hmem := by decide

def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [5, 4, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 2, 3], [8, 8, 8], [0, 1]]
 g := ![![[2, 9, 9], [0, 9, 1], []],![[6, 1, 6, 3], [0, 6, 6, 5], [5, 9]],![[10, 7, 0, 10], [7, 0, 6, 10], [0, 9]]]
 h' := ![![[1, 2, 3], [0, 10, 3], [0, 0, 1], [0, 1]],![[8, 8, 8], [4, 2, 10], [9, 5, 8], [1, 2, 3]],![[0, 1], [8, 10, 9], [9, 6, 2], [8, 8, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 4], []]
 b := ![[], [3, 5, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : PrimeIdeal O 11 where
  r := 5
  n := 3
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I11N0
  hcard := NI11N0
  P := [5, 4, 2, 1]
  f := ofList [5, 4, 2, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P11P0
  hneq := by decide
  hlen := by decide
  c := ![-10411, 9675, 3853, -4870, 3291]
  a := ![-2, 8, -1, 13, 0]
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
def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0], ![2, 1, 0, 0, 0]] i)))

def SI11N1: IdealEqSpanCertificate O ℤ timesTableO I11N1
 ![![11, 0, 0, 0, 0], ![2, 1, 0, 0, 0]]
 ![![11, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]], ![![2, 1, 0, 0, 0], ![0, 2, 2, 0, 0], ![0, 1, 2, 2, 0], ![0, 0, -1, 2, 1], ![4, -5, 0, 0, 2]]]
  hmulB := by decide
  f := ![![![13, 12, 11, 22, 3], ![-66, 11, -88, -33, 0]], ![![2, 3, 3, 14, 3], ![-10, 11, -44, -33, 0]], ![![11, 11, 10, 20, 3], ![-56, 6, -77, -33, 0]], ![![-1, -1, 0, 1, 0], ![6, 5, -5, 0, 0]], ![![5, 6, 7, 14, 2], ![-24, 7, -56, -21, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-2, 11, 0, 0, 0], ![-9, 0, 11, 0, 0], ![-1, 0, 0, 11, 0], ![-7, 0, 0, 0, 11]], ![![0, 1, 0, 0, 0], ![-2, 2, 2, 0, 0], ![-2, 1, 2, 2, 0], ![0, 0, -1, 2, 1], ![0, -5, 0, 0, 2]]]
  hle1 := by decide
  hle2 := by decide

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def I11N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0], ![3, 1, 0, 0, 0]] i)))

def SI11N2: IdealEqSpanCertificate O ℤ timesTableO I11N2
 ![![11, 0, 0, 0, 0], ![3, 1, 0, 0, 0]]
 ![![11, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![10, 0, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]], ![![3, 1, 0, 0, 0], ![0, 3, 2, 0, 0], ![0, 1, 3, 2, 0], ![0, 0, -1, 3, 1], ![4, -5, 0, 0, 3]]]
  hmulB := by decide
  f := ![![![-251, -492, -1525, -858, 56], ![924, -385, 5643, -616, 0]], ![![-75, -148, -455, -258, 16], ![276, -110, 1683, -176, 0]], ![![-37, -71, -215, -120, 8], ![136, -49, 792, -88, 0]], ![![-182, -353, -1090, -613, 40], ![670, -273, 4032, -440, 0]], ![![-226, -446, -1386, -780, 51], ![832, -352, 5130, -560, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-3, 11, 0, 0, 0], ![-1, 0, 11, 0, 0], ![-8, 0, 0, 11, 0], ![-10, 0, 0, 0, 11]], ![![0, 1, 0, 0, 0], ![-1, 3, 2, 0, 0], ![-2, 1, 3, 2, 0], ![-3, 0, -1, 3, 1], ![-1, -5, 0, 0, 3]]]
  hle1 := by decide
  hle2 := by decide

lemma NI11N2 : Nat.card (O ⧸ I11N2) = 11 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI11N2)

lemma isPrimeI11N2 : Ideal.IsPrime I11N2 := prime_ideal_of_norm_prime hp11.out _ NI11N2
def MulI11N0 : IdealMulEqCertificate O ℤ timesTableO (I11N0) I11N1
  ![![7, -1, 0, 1, 1]] ![![11, 0, 0, 0, 0], ![2, 1, 0, 0, 0]]
  ![![11, 0, 0, 0, 0], ![6, 0, -1, -3, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![77, -11, 0, 11, 11], ![18, 0, -3, 2, 3]]]
 hmul := by decide
 f :=  ![![![![-20830916710397, 26545017690881, 22732921364831, 1695, -4065015623456], ![69854870049168, -125031067497248, -9322, 0, 22357585929008]]], ![![![-11601919372860, 14784426402459, 12661253676507, 944, -2264037832244], ![38906140396046, -69636895215596, -5192, 0, 12452208077342]]]]
 g :=  ![![![![1, -1, 1, 4, 0], ![11, 0, 0, 0, 0]], ![![0, 0, 0, 1, 0], ![3, 0, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI11N1 : IdealMulEqCertificate O ℤ timesTableO (I11N0*I11N1) I11N2
  ![![11, 0, 0, 0, 0], ![6, 0, -1, -3, 1]] ![![11, 0, 0, 0, 0], ![3, 1, 0, 0, 0]]
  ![![11, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI11N0
 hI2 := rfl
 M :=  ![![![121, 0, 0, 0, 0], ![33, 11, 0, 0, 0]], ![![66, 0, -11, -33, 11], ![22, 0, 0, -11, 0]]]
 hmul := by decide
 f :=  ![![![![-31686049, -60769216, -180779617, -124228468, 527966], ![116184580, -46562539, 691964413, -5806426, 0]], ![![-1200, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]]
 g :=  ![![![![11, 0, 0, 0, 0]], ![![3, 1, 0, 0, 0]]], ![![![6, 0, -1, -3, 1]], ![![2, 0, 0, -1, 0]]]]
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

--- Primes below 13

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
  ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]] ![-73307, 66781, 159562, 98787, -15639] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI13N
 g := ![-5639, 5137, 12274, 7599, -1203]
 hmem := by decide

def P13P : CertificateIrreducibleZModOfList' 13 5 2 3 [6, 11, 1, 7, 5, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 6, 10, 2, 5], [7, 12, 7, 9, 6], [5, 10, 3, 7, 8], [8, 10, 6, 8, 7], [0, 1]]
 g := ![![[2, 11, 2, 7, 12], [8, 1], []],![[3, 11, 11, 4, 6, 8, 0, 2], [5, 0, 9, 10], [8, 8, 9, 8, 1, 9, 6, 8]],![[6, 2, 12, 5, 5, 6, 8, 7], [7, 9, 10, 3], [1, 10, 3, 4, 1, 7, 9, 8]],![[6, 4, 9, 12, 0, 3, 11, 7], [10, 1, 4, 9], [3, 3, 5, 0, 2, 10, 6, 5]],![[12, 3, 2, 8, 11, 3, 10, 8], [0, 5, 9, 10], [8, 4, 6, 3, 2, 11, 7, 5]]]
 h' := ![![[1, 6, 10, 2, 5], [4, 10, 7, 8, 5], [0, 0, 0, 1], [0, 1]],![[7, 12, 7, 9, 6], [8, 0, 4, 4, 4], [5, 12, 1, 7, 7], [1, 6, 10, 2, 5]],![[5, 10, 3, 7, 8], [11, 6, 3, 0, 5], [12, 3, 11, 5, 9], [7, 12, 7, 9, 6]],![[8, 10, 6, 8, 7], [1, 9, 12, 1, 3], [3, 10, 8, 6, 3], [5, 10, 3, 7, 8]],![[0, 1], [3, 1, 0, 0, 9], [9, 1, 6, 7, 7], [8, 10, 6, 8, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 4, 12, 1], [], [], []]
 b := ![[], [3, 8, 5, 5, 5], [], [], []]
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
  P := [6, 11, 1, 7, 5, 1]
  f := ofList [6, 11, 1, 7, 5, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P13P
  hneq := by decide
  hlen := by decide
  c := ![-73307, 66781, 159562, 98787, -15639]
  a := ![-1, 0, -5, -3, 0]
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

--- Primes below 17

instance hp17 : Fact (Nat.Prime 17) := by decide

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9, -4, -3, -3, -2]] i)))

def SI17N0: IdealEqSpanCertificate O ℤ timesTableO I17N0
 ![![-9, -4, -3, -3, -2]]
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![2, 3, 6, 1, 0], ![10, 6, 1, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![-9, -4, -3, -3, -2], ![-8, -2, -5, -6, -3], ![-6, 1, 1, -5, -3], ![-2, 6, 6, 4, -1], ![-10, 10, 9, 7, 1]]]
  hmulB := by decide
  f := ![![![-1, 0, 0, 1, -1]], ![![-4, 4, -1, 0, 1]], ![![2, -5, 4, -1, 0]], ![![0, -1, 1, 0, 0]], ![![-2, 1, 0, 0, 0]]]
  g := ![![![1, 1, 1, -3, -2], ![2, 2, 2, -6, -3], ![2, 2, 2, -5, -3], ![0, 0, -1, 4, -1], ![-2, -1, -2, 7, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI17N0 : Nat.card (O ⧸ I17N0) = 4913 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI17N0)

def MemCI17N0 : IdealMemCertificate O ℤ B I17N0
  ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![2, 3, 6, 1, 0], ![10, 6, 1, 0, 1]] ![3467984920, -4304541600, -70526998, 4380496, -701383490] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI17N0
 g := ![616062284, -6434244, 35563148, 4380496, -701383490]
 hmem := by decide

def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [8, 3, 12, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 0, 7], [8, 16, 10], [0, 1]]
 g := ![![[11, 6, 8], [14, 8], [5, 1], []],![[13, 12, 7, 5], [16, 16], [15, 1], [7, 15]],![[1, 11], [0, 13], [], [4, 15]]]
 h' := ![![[14, 0, 7], [9, 0, 5], [11, 11, 5], [0, 0, 1], [0, 1]],![[8, 16, 10], [12, 9, 12], [15, 9, 4], [4, 12, 16], [14, 0, 7]],![[0, 1], [16, 8], [4, 14, 8], [15, 5], [8, 16, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 4], []]
 b := ![[], [14, 5, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : PrimeIdeal O 17 where
  r := 5
  n := 3
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I17N0
  hcard := NI17N0
  P := [8, 3, 12, 1]
  f := ofList [8, 3, 12, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P17P0
  hneq := by decide
  hlen := by decide
  c := ![3467984920, -4304541600, -70526998, 4380496, -701383490]
  a := ![3, -443, 1, -886, -1]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI17N0
  hpmem := by
    show  _ ∈ I17N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI17N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := PrimeIdeal_isPrime PI17N0
def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0, 0], ![-8, 1, 0, 0, 0]] i)))

def SI17N1: IdealEqSpanCertificate O ℤ timesTableO I17N1
 ![![17, 0, 0, 0, 0], ![-8, 1, 0, 0, 0]]
 ![![17, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![13, 0, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]], ![![-8, 1, 0, 0, 0], ![0, -8, 2, 0, 0], ![0, 1, -8, 2, 0], ![0, 0, -1, -8, 1], ![4, -5, 0, 0, -8]]]
  hmulB := by decide
  f := ![![![2233, -461, 3038, -1020, 30], ![4743, 442, 6630, -510, 0]], ![![1313, -266, 1790, -604, 18], ![2789, 272, 3910, -306, 0]], ![![402, -76, 543, -188, 6], ![854, 94, 1190, -102, 0]], ![![1564, -324, 2131, -715, 21], ![3322, 308, 4650, -357, 0]], ![![1717, -349, 2322, -780, 23], ![3647, 348, 5070, -390, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-9, 17, 0, 0, 0], ![-2, 0, 17, 0, 0], ![-12, 0, 0, 17, 0], ![-13, 0, 0, 0, 17]], ![![-1, 1, 0, 0, 0], ![4, -8, 2, 0, 0], ![-1, 1, -8, 2, 0], ![5, 0, -1, -8, 1], ![9, -5, 0, 0, -8]]]
  hle1 := by decide
  hle2 := by decide

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def I17N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0, 0], ![-4, 1, 0, 0, 0]] i)))

def SI17N2: IdealEqSpanCertificate O ℤ timesTableO I17N2
 ![![17, 0, 0, 0, 0], ![-4, 1, 0, 0, 0]]
 ![![17, 0, 0, 0, 0], ![13, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]], ![![-4, 1, 0, 0, 0], ![0, -4, 2, 0, 0], ![0, 1, -4, 2, 0], ![0, 0, -1, -4, 1], ![4, -5, 0, 0, -4]]]
  hmulB := by decide
  f := ![![![1045, -885, 2830, -1768, 72], ![4437, 493, 12580, -1224, 0]], ![![873, -742, 2372, -1480, 60], ![3707, 408, 10540, -1020, 0]], ![![685, -583, 1873, -1172, 48], ![2909, 332, 8330, -816, 0]], ![![175, -147, 472, -295, 12], ![743, 86, 2100, -204, 0]], ![![252, -210, 666, -416, 17], ![1070, 115, 2960, -288, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-13, 17, 0, 0, 0], ![-9, 0, 17, 0, 0], ![-3, 0, 0, 17, 0], ![-4, 0, 0, 0, 17]], ![![-1, 1, 0, 0, 0], ![2, -4, 2, 0, 0], ![1, 1, -4, 2, 0], ![1, 0, -1, -4, 1], ![5, -5, 0, 0, -4]]]
  hle1 := by decide
  hle2 := by decide

lemma NI17N2 : Nat.card (O ⧸ I17N2) = 17 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI17N2)

lemma isPrimeI17N2 : Ideal.IsPrime I17N2 := prime_ideal_of_norm_prime hp17.out _ NI17N2
def MulI17N0 : IdealMulEqCertificate O ℤ timesTableO (I17N0) I17N1
  ![![-9, -4, -3, -3, -2]] ![![17, 0, 0, 0, 0], ![-8, 1, 0, 0, 0]]
  ![![17, 0, 0, 0, 0], ![1, 1, 8, 4, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![-153, -68, -51, -51, -34], ![64, 30, 19, 18, 13]]]
 hmul := by decide
 f :=  ![![![![-527013481, -23254469913, 5752420089, 20035369, 922], ![-1119903647, -49577031938, -170363336, -15675, 0]]], ![![![1, -4, 1, 0, 0], ![2, -8, 0, 0, 0]]]]
 g :=  ![![![![-9, -4, -3, -3, -2], ![0, 0, 0, 0, 0]], ![![3, 1, -5, -2, 0], ![13, 0, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI17N1 : IdealMulEqCertificate O ℤ timesTableO (I17N0*I17N1) I17N2
  ![![17, 0, 0, 0, 0], ![1, 1, 8, 4, 1]] ![![17, 0, 0, 0, 0], ![-4, 1, 0, 0, 0]]
  ![![17, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI17N0
 hI2 := rfl
 M :=  ![![![289, 0, 0, 0, 0], ![-68, 17, 0, 0, 0]], ![![17, 17, 136, 68, 17], ![0, 0, -34, 0, 0]]]
 hmul := by decide
 f :=  ![![![![63336540300, -17630895343, 8335215082, -4284095668, 7542207], ![269180295342, 1403365961, 36158393064, -128213788, 0]], ![![-3731, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]]
 g :=  ![![![![17, 0, 0, 0, 0]], ![![-4, 1, 0, 0, 0]]], ![![![1, 1, 8, 4, 1]], ![![0, 0, -2, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def PBC17 : PrimesBelowPCertificate 17 ![I17N0, I17N1, I17N2] where
  Ip := by
    intro i
    fin_cases i
    exact isPrimeI17N0
    exact isPrimeI17N1
    exact isPrimeI17N2
  hPprod := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI17N1, Set.range_unique]
    dsimp ; congr
    erw [B_int_repr]
    rfl

--- Primes below 19

instance hp19 : Fact $ Nat.Prime 19 := by decide

def I19N : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0, 0, 0]] i)))

def SI19N: IdealEqSpanCertificate O ℤ timesTableO I19N
 ![![19, 0, 0, 0, 0]]
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI19N : Nat.card (O ⧸ I19N) = 2476099 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI19N)

def MemCI19N : IdealMemCertificate O ℤ B I19N
  ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]] ![14026579, -56119806, 54609971, -45760778, 8167587] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI19N
 g := ![738241, -2953674, 2874209, -2408462, 429873]
 hmem := by decide

def P19P : CertificateIrreducibleZModOfList' 19 5 2 4 [7, 6, 15, 5, 13, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 13, 16, 14, 13], [5, 15, 5, 16, 3], [2, 16, 16, 5, 17], [14, 12, 1, 3, 5], [0, 1]]
 g := ![![[13, 11, 14, 10, 1], [6, 8, 12, 6, 1], [], []],![[6, 8, 9, 6, 17, 5, 16, 14], [10, 14, 5, 5, 9, 7, 3, 13], [13, 18, 1, 5], [13, 17, 10, 17]],![[16, 3, 13, 5, 14, 17, 3, 8], [4, 5, 5, 16, 2, 3, 9, 10], [2, 11], [17, 1, 17, 9]],![[0, 10, 6, 14, 10, 9, 7, 16], [17, 8, 5, 15, 12, 16], [3, 1], [15, 3, 4, 4]],![[14, 4, 10, 15, 17, 13, 0, 16], [15, 2, 3, 11, 0, 16, 16, 4], [0, 3, 14, 5], [2, 5, 9, 6]]]
 h' := ![![[4, 13, 16, 14, 13], [15, 3, 6, 2, 1], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]],![[5, 15, 5, 16, 3], [11, 14, 11, 17, 17], [5, 9, 10, 10, 18], [1, 2, 6, 10, 9], [4, 13, 16, 14, 13]],![[2, 16, 16, 5, 17], [0, 4, 11, 1, 16], [6, 12, 7, 7, 4], [1, 3, 9, 7], [5, 15, 5, 16, 3]],![[14, 12, 1, 3, 5], [8, 5, 11, 3, 12], [15, 7, 12, 12], [13, 10, 11, 18], [2, 16, 16, 5, 17]],![[0, 1], [11, 12, 18, 15, 11], [7, 10, 9, 9, 15], [11, 4, 11, 3, 10], [14, 12, 1, 3, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 8, 8, 18], [], [], []]
 b := ![[], [14, 6, 17, 3, 3], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N : PrimeIdeal O 19 where
  r := 5
  n := 5
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I19N
  hcard := NI19N
  P := [7, 6, 15, 5, 13, 1]
  f := ofList [7, 6, 15, 5, 13, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P19P
  hneq := by decide
  hlen := by decide
  c := ![14026579, -56119806, 54609971, -45760778, 8167587]
  a := ![1, 7, -3, 13, -1]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI19N
  hpmem := by
    show  _ ∈ I19N.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI19N]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI19N : Ideal.IsPrime I19N := PrimeIdeal_isPrime PI19N
def PBC19 : PrimesBelowPCertificate 19 ![I19N] where
  Ip := by
    intro i
    fin_cases i
    exact isPrimeI19N
  hPprod := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    unfold I19N
    rw [Set.range_unique]
    dsimp ; congr
    erw [B_int_repr]
    rfl

--- Primes below 23

instance hp23: Fact $ Nat.Prime 23 := by decide

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-37, -3, -2, -5, -7]] i)))

def SI23N0: IdealEqSpanCertificate O ℤ timesTableO I23N0
 ![![-37, -3, -2, -5, -7]]
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![1, 3, 1, 0, 0], ![20, 15, 0, 1, 0], ![17, 2, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![-37, -3, -2, -5, -7], ![-28, -4, -1, -4, -5], ![-10, -2, -2, -1, -2], ![10, 1, -1, 0, 2], ![-2, -3, 0, -3, -2]]]
  hmulB := by decide
  f := ![![![1, -3, 1, -1, 2]], ![![8, -8, -5, 2, -1]], ![![1, -1, -1, 0, 0]], ![![6, -8, -2, 0, 1]], ![![1, -2, 0, 0, 1]]]
  g := ![![![8, 4, -2, -5, -7], ![6, 3, -1, -4, -5], ![2, 1, -2, -1, -2], ![-1, 0, -1, 0, 2], ![4, 2, 0, -3, -2]]]
  hle1 := by decide
  hle2 := by decide

lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI23N0)

def MemCI23N0 : IdealMemCertificate O ℤ B I23N0
  ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![1, 3, 1, 0, 0], ![20, 15, 0, 1, 0], ![17, 2, 0, 0, 1]] ![13, 0, 1425, 0, 5625] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI23N0
 g := ![-4219, -675, 1425, 0, 5625]
 hmem := by decide

def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [13, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 22], [0, 1]]
 g := ![![[5, 16], [20, 18], [6, 16], [1]],![[0, 7], [0, 5], [1, 7], [1]]]
 h' := ![![[4, 22], [16, 19], [14, 8], [10, 4], [0, 1]],![[0, 1], [0, 4], [0, 15], [3, 19], [4, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [5, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : PrimeIdeal O 23 where
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I23N0
  hcard := NI23N0
  P := [13, 19, 1]
  f := ofList [13, 19, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P23P0
  hneq := by decide
  hlen := by decide
  c := ![13, 0, 1425, 0, 5625]
  a := ![0, 0, 75, 0, 0]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI23N0
  hpmem := by
    show  _ ∈ I23N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI23N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := PrimeIdeal_isPrime PI23N0
def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![21, 1, 1, 3, 4]] i)))

def SI23N1: IdealEqSpanCertificate O ℤ timesTableO I23N1
 ![![21, 1, 1, 3, 4]]
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![7, 17, 1, 0, 0], ![19, 14, 0, 1, 0], ![18, 20, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![21, 1, 1, 3, 4], ![16, 2, -1, 2, 3], ![6, 0, 1, -1, 1], ![-6, 0, 1, 0, -2], ![-2, 5, 1, 1, 1]]]
  hmulB := by decide
  f := ![![![-1, 3, 2, 3, -1]], ![![-4, 6, 3, 4, 3]], ![![-3, 5, 3, 4, 2]], ![![-3, 6, 3, 5, 1]], ![![-4, 7, 4, 5, 2]]]
  g := ![![![-5, -6, 1, 3, 4], ![-3, -3, -1, 2, 3], ![0, -1, 1, -1, 1], ![1, 1, 1, 0, -2], ![-2, -2, 1, 1, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 529 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI23N1)

def MemCI23N1 : IdealMemCertificate O ℤ B I23N1
  ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![7, 17, 1, 0, 0], ![19, 14, 0, 1, 0], ![18, 20, 0, 0, 1]] ![-37, 41, 30, -65, -101] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI23N1
 g := ![122, 107, 30, -65, -101]
 hmem := by decide

def P23P1 : CertificateIrreducibleZModOfList' 23 2 2 4 [9, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 22], [0, 1]]
 g := ![![[18, 18], [17, 12], [17, 1], [1]],![[0, 5], [5, 11], [16, 22], [1]]]
 h' := ![![[22, 22], [8, 8], [8, 9], [14, 22], [0, 1]],![[0, 1], [0, 15], [22, 14], [15, 1], [22, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [2, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N1 : PrimeIdeal O 23 where
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I23N1
  hcard := NI23N1
  P := [9, 1, 1]
  f := ofList [9, 1, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P23P1
  hneq := by decide
  hlen := by decide
  c := ![-37, 41, 30, -65, -101]
  a := ![1, 0, 0, -3, -4]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI23N1
  hpmem := by
    show  _ ∈ I23N1.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI23N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := PrimeIdeal_isPrime PI23N1
def I23N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 1, 1]] i)))

def SI23N2: IdealEqSpanCertificate O ℤ timesTableO I23N2
 ![![3, 0, 0, 1, 1]]
 ![![23, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![21, 0, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![3, 0, 0, 1, 1], ![4, -2, -1, 0, 1], ![2, -1, -2, -1, 0], ![-2, 1, 0, -2, -1], ![-2, 2, 2, -1, -2]]]
  hmulB := by decide
  f := ![![![5, 2, 3, -1, 4]], ![![2, 0, 1, 0, 1]], ![![1, 1, 0, 0, 1]], ![![1, 0, 1, -1, 1]], ![![5, 2, 2, 0, 3]]]
  g := ![![![-1, 0, 0, 1, 1], ![0, -2, -1, 0, 1], ![1, -1, -2, -1, 0], ![1, 1, 0, -2, -1], ![1, 2, 2, -1, -2]]]
  hle1 := by decide
  hle2 := by decide

lemma NI23N2 : Nat.card (O ⧸ I23N2) = 23 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI23N2)

lemma isPrimeI23N2 : Ideal.IsPrime I23N2 := prime_ideal_of_norm_prime hp23.out _ NI23N2
def MulI23N0 : IdealMulEqCertificate O ℤ timesTableO (I23N0) I23N1
  ![![-37, -3, -2, -5, -7]] ![![21, 1, 1, 3, 4]]
  ![![-793, -78, -48, -122, -156]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![-793, -78, -48, -122, -156]]]
 hmul := by decide
 f :=  ![![![![1, 0, 0, 0, 0]]]]
 g :=  ![![![![1, 0, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI23N1 : IdealMulEqCertificate O ℤ timesTableO (I23N0*I23N1) I23N2
  ![![-793, -78, -48, -122, -156]] ![![3, 0, 0, 1, 1]]
  ![![23, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI23N0
 hI2 := rfl
 M :=  ![![![-2231, -230, -138, -345, -437]]]
 hmul := by decide
 f :=  ![![![![-1, 2, -1, 1, 0]]]]
 g :=  ![![![![-97, -10, -6, -15, -19]]]]
 hle1 := by decide
 hle2 := by decide

def PBC23 : PrimesBelowPCertificate 23 ![I23N0, I23N1, I23N2] where
  Ip := by
    intro i
    fin_cases i
    exact isPrimeI23N0
    exact isPrimeI23N1
    exact isPrimeI23N2
  hPprod := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI23N1, Set.range_unique]
    dsimp ; congr
    erw [B_int_repr]
    rfl
