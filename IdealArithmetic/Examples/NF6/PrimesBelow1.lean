import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Examples.NF6.RI6
import IdealArithmetic.ClassGroupGeneration

open Classical Polynomial

noncomputable section



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
def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![4, -2, -1, -1, -2]] i)))

def SI2N2: IdealEqSpanCertificate O ℤ timesTableO I2N2
 ![![2, 0, 0, 0, 0], ![4, -2, -1, -1, -2]]
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![4, -2, -1, -1, -2], ![-3, 4, -4, -1, -6], ![-3, -6, 2, 1, 6], ![3, -3, 0, -2, 0], ![-2, 3, -1, 0, -3]]]
  hmulB := by decide
  f := ![![![0, -2, 5, 2, 8], ![2, 2, 0, 0, 0]], ![![-4, 6, -4, 0, -6], ![0, -2, 0, 1, 0]], ![![0, -1, 3, 1, 4], ![1, 1, 0, 0, 0]], ![![-2, 0, 3, 2, 5], ![2, 1, 0, 0, 0]], ![![12, -23, 25, 5, 40], ![5, 11, 0, -3, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![-1, 2, 0, 0, 0], ![-1, 0, 2, 0, 0], ![-1, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![4, -2, -1, -1, -2], ![-1, 4, -4, -1, -6], ![0, -6, 2, 1, 6], ![4, -3, 0, -2, 0], ![-2, 3, -1, 0, -3]]]
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
  ![![2, 0, 0, 0, 0], ![3, 3, -2, -1, -4]] ![![2, 0, 0, 0, 0], ![4, -2, -1, -1, -2]]
  ![![2, 0, 0, 0, 0], ![2, 5, -5, -2, -8]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI2N1
 hI2 := rfl
 M :=  ![![![4, 0, 0, 0, 0], ![8, -4, -2, -2, -4]], ![![6, 6, -4, -2, -8], ![14, 9, -15, -6, -24]]]
 hmul := by decide
 f :=  ![![![![-4427, 6701, -6998, -1610, -10669], ![-574, -3345, 0, 351, -36]], ![![-3, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]], ![![![-186729, 282686, -295316, -67976, -450239], ![-24258, -141147, 0, 14790, -1524]], ![![-111, 0, 0, 0, 0], ![-5, 0, 0, 0, 0]]]]
 g :=  ![![![![2, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![2, -7, 4, 1, 6], ![2, 0, 0, 0, 0]]], ![![![1, -2, 3, 1, 4], ![2, 0, 0, 0, 0]], ![![4, -3, 0, 0, 0], ![3, 0, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI2N3 : IdealMulEqCertificate O ℤ timesTableO (I2N0*I2N1*I2N1*I2N2) I2N2
  ![![2, 0, 0, 0, 0], ![2, 5, -5, -2, -8]] ![![2, 0, 0, 0, 0], ![4, -2, -1, -1, -2]]
  ![![2, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI2N2
 hI2 := rfl
 M :=  ![![![4, 0, 0, 0, 0], ![8, -4, -2, -2, -4]], ![![4, 10, -10, -4, -16], ![18, 28, -24, -8, -40]]]
 hmul := by decide
 f :=  ![![![![-22110, 33460, -34963, -8050, -53300], ![-2870, -16710, 0, 1746, -180]], ![![0, 0, 0, 0, 0], ![-3, 0, 0, 0, 0]]]]
 g :=  ![![![![2, 0, 0, 0, 0]], ![![4, -2, -1, -1, -2]]], ![![![2, 5, -5, -2, -8]], ![![9, 14, -12, -4, -20]]]]
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
  ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 3]] ![390, -643, 427, 1590, 3828] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI3N0
 g := ![130, -643, 427, 1590, 1276]
 hmem := by decide

def P3P0 : CertificateIrreducibleZModOfList' 3 2 2 1 [2, 1, 1] where
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

def PI3N0 : PrimeIdeal O 3 where
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I3N0
  hcard := NI3N0
  P := [2, 1, 1]
  f := ofList [2, 1, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P3P0
  hneq := by decide
  hlen := by decide
  c := ![390, -643, 427, 1590, 3828]
  a := ![-7, 0, -6, -11, -28]
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
  ![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![2, 2, 1, 0, 0], ![1, 1, 0, 1, 0], ![0, 1, 0, 0, 1]] ![7974780, -4044120, 4807262, 2955584, 25244673] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI3N1
 g := ![-1531776, -13952967, 4807262, 2955584, 25244673]
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
  c := ![7974780, -4044120, 4807262, 2955584, 25244673]
  a := ![573, -192, 476, 572, 2293]
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
  ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![6, 3, 1, 0, 0], ![5, 6, 0, 1, 0], ![2, 5, 0, 0, 1]] ![-399, 404, -176, -168, -1593] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI7N0
 g := ![669, 1415, -176, -168, -1593]
 hmem := by decide

def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [1, 3, 1] where
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
 g := ![![[3, 1], [4, 1]],![[0, 6], [1, 6]]]
 h' := ![![[4, 6], [3, 1], [0, 1]],![[0, 1], [0, 6], [4, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [5, 1]]
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
  P := [1, 3, 1]
  f := ofList [1, 3, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P7P0
  hneq := by decide
  hlen := by decide
  c := ![-399, 404, -176, -168, -1593]
  a := ![1, 3, 3, 7, 5]
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
  ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![2, 2, 1, 0, 0], ![5, 3, 0, 1, 0], ![4, 4, 0, 0, 1]] ![4990, 1143, 2667, -4842, 1182] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI7N1
 g := ![2734, 801, 2667, -4842, 1182]
 hmem := by decide

def P7P1 : CertificateIrreducibleZModOfList' 7 2 2 2 [6, 3, 1] where
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
 g := ![![[4, 2], [4, 1]],![[5, 5], [1, 6]]]
 h' := ![![[4, 6], [4, 3], [0, 1]],![[0, 1], [2, 4], [4, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [3, 2]]
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
  P := [6, 3, 1]
  f := ofList [6, 3, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P7P1
  hneq := by decide
  hlen := by decide
  c := ![4990, 1143, 2667, -4842, 1182]
  a := ![2, 13, 3, 4, -30]
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
  ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![9, 3, 1, 0, 0], ![3, 6, 0, 1, 0], ![10, 4, 0, 0, 1]] ![4608, -5601, 4403, 13118, 34696] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI11N0
 g := ![-38303, -21482, 4403, 13118, 34696]
 hmem := by decide

def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [4, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 10], [0, 1]]
 g := ![![[5, 3], [3, 4], [1]],![[0, 8], [0, 7], [1]]]
 h' := ![![[2, 10], [10, 6], [7, 2], [0, 1]],![[0, 1], [0, 5], [0, 9], [2, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [9, 2]]
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
  P := [4, 9, 1]
  f := ofList [4, 9, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P11P0
  hneq := by decide
  hlen := by decide
  c := ![4608, -5601, 4403, 13118, 34696]
  a := ![-22, 0, -21, -33, -88]
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
  ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![5, 4, 1, 0, 0], ![1, 6, 0, 1, 0], ![4, 5, 0, 0, 1]] ![35416, -18354, 22566, 18734, 120305] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI11N1
 g := ![-52488, -74777, 22566, 18734, 120305]
 hmem := by decide

def P11P1 : CertificateIrreducibleZModOfList' 11 2 2 3 [6, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 10], [0, 1]]
 g := ![![[7, 4], [6, 4], [1]],![[4, 7], [3, 7], [1]]]
 h' := ![![[2, 10], [8, 2], [5, 2], [0, 1]],![[0, 1], [1, 9], [9, 9], [2, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [1, 10]]
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
  P := [6, 9, 1]
  f := ofList [6, 9, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P11P1
  hneq := by decide
  hlen := by decide
  c := ![35416, -18354, 22566, 18734, 120305]
  a := ![42, -11, 41, 45, 167]
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
  ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]] ![19686973219329, -11659780349074, 11981082325849, 10243998085360, 68742264998095] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI13N
 g := ![1514382555333, -896906180698, 921621717373, 787999852720, 5287866538315]
 hmem := by decide

def P13P : CertificateIrreducibleZModOfList' 13 5 2 3 [12, 3, 12, 0, 3, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 0, 10, 2, 5], [4, 6, 1, 11, 11], [10, 0, 6, 1, 12], [10, 6, 9, 12, 11], [0, 1]]
 g := ![![[12, 1, 9, 9, 3], [10, 1], []],![[7, 6, 8, 0, 2, 6, 8, 5], [0, 3, 5, 4], [11, 3, 6, 8, 9, 3, 9, 8]],![[10, 4, 7, 3, 11, 2, 9, 5], [4, 7, 8, 12], [11, 3, 6, 4, 12, 1, 0, 5]],![[0, 2, 9, 12, 1, 6, 1, 12], [9, 8, 7, 9], [10, 1, 1, 4, 12, 10, 6, 12]],![[10, 12, 9, 2, 4, 2, 6, 5], [7, 3, 1, 9], [0, 3, 5, 6, 12, 1, 12, 5]]]
 h' := ![![[12, 0, 10, 2, 5], [10, 10, 7, 1, 9], [0, 0, 0, 1], [0, 1]],![[4, 6, 1, 11, 11], [9, 1, 5, 6, 1], [10, 9, 12, 12, 11], [12, 0, 10, 2, 5]],![[10, 0, 6, 1, 12], [0, 7, 5, 9, 2], [10, 11, 7, 6, 8], [4, 6, 1, 11, 11]],![[10, 6, 9, 12, 11], [12, 5, 6, 5, 12], [9, 10, 1, 3, 10], [10, 0, 6, 1, 12]],![[0, 1], [8, 3, 3, 5, 2], [12, 9, 6, 4, 10], [10, 6, 9, 12, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 5, 9, 8], [], [], []]
 b := ![[], [4, 2, 10, 6, 1], [], [], []]
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
  P := [12, 3, 12, 0, 3, 1]
  f := ofList [12, 3, 12, 0, 3, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P13P
  hneq := by decide
  hlen := by decide
  c := ![19686973219329, -11659780349074, 11981082325849, 10243998085360, 68742264998095]
  a := ![57, -2, 57, 60, 185]
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
instance hp17 : Fact (Nat.Prime 17) := by decide
def I17N : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0, 0]] i)))

def SI17N: IdealEqSpanCertificate O ℤ timesTableO I17N
 ![![17, 0, 0, 0, 0]]
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI17N : Nat.card (O ⧸ I17N) = 1419857 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI17N)

def MemCI17N : IdealMemCertificate O ℤ B I17N
  ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]] ![452807252427, -2198358418122, 755960872149, 5044823853321, 10862346501453] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI17N
 g := ![26635720731, -129315201066, 44468286597, 296754344313, 638961558909]
 hmem := by decide

def P17P : CertificateIrreducibleZModOfList' 17 5 2 4 [13, 7, 2, 5, 4, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 9, 6, 10, 7], [11, 0, 2, 4, 15], [14, 6, 3, 1, 16], [16, 1, 6, 2, 13], [0, 1]]
 g := ![![[10, 6, 5, 5, 1], [8, 11, 13, 1], [], []],![[0, 11, 6, 11, 11, 0, 4, 3], [7, 4], [16, 15, 11, 9], [14, 10, 12, 15]],![[9, 12, 9, 1, 14, 2, 15, 8], [3, 8, 16, 1], [7, 10, 3, 8], [10, 14, 2, 4]],![[16, 16, 6, 15, 16, 16, 1, 13], [9, 11, 10, 8], [8, 3, 11, 16], [0, 14, 11, 1]],![[16, 10, 2, 6, 1, 9, 15, 1], [13, 12, 9, 8], [7, 14, 2, 4], [8, 9, 5, 16]]]
 h' := ![![[6, 9, 6, 10, 7], [15, 5, 10, 4, 16], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]],![[11, 0, 2, 4, 15], [13, 11, 14, 9, 10], [11, 2, 7, 15], [7, 16, 1, 12, 14], [6, 9, 6, 10, 7]],![[14, 6, 3, 1, 16], [10, 13, 1, 6, 8], [7, 5, 3, 7, 16], [8, 3, 2, 12, 5], [11, 0, 2, 4, 15]],![[16, 1, 6, 2, 13], [4, 14, 13, 9, 2], [11, 10, 14, 11, 5], [9, 3, 15, 14, 13], [14, 6, 3, 1, 16]],![[0, 1], [9, 8, 13, 6, 15], [12, 0, 10, 1, 12], [16, 12, 15, 13, 2], [16, 1, 6, 2, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 7, 9, 11], [], [], []]
 b := ![[], [8, 15, 7, 3, 13], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N : PrimeIdeal O 17 where
  r := 5
  n := 5
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I17N
  hcard := NI17N
  P := [13, 7, 2, 5, 4, 1]
  f := ofList [13, 7, 2, 5, 4, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P17P
  hneq := by decide
  hlen := by decide
  c := ![452807252427, -2198358418122, 755960872149, 5044823853321, 10862346501453]
  a := ![-28, 12, -27, -23, -113]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI17N
  hpmem := by
    show  _ ∈ I17N.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI17N]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI17N : Ideal.IsPrime I17N := PrimeIdeal_isPrime PI17N
def PBC17 : PrimesBelowPCertificate 17 ![I17N] where
  Ip := by
    intro i
    fin_cases i
    exact isPrimeI17N
  hPprod := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    unfold I17N
    rw [Set.range_unique]
    dsimp ; congr
    erw [B_int_repr]
    rfl
instance hp19 : Fact (Nat.Prime 19) := by decide
def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0, 0, 0], ![4, 5, -3, -1, -5]] i)))

def SI19N0: IdealEqSpanCertificate O ℤ timesTableO I19N0
 ![![19, 0, 0, 0, 0], ![4, 5, -3, -1, -5]]
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![2, 17, 1, 0, 0], ![2, 9, 0, 1, 0], ![9, 6, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]], ![![4, 5, -3, -1, -5], ![-3, 2, 3, 1, 3], ![3, -1, 4, 3, 3], ![6, 1, 1, 5, 12], ![-2, -1, 1, -2, 0]]]
  hmulB := by decide
  f := ![![![-101731, 85109, 103245, 34235, 98815], ![-43111, -699732, 2052, 0, 0]], ![![-170094, 142312, 172629, 57243, 165219], ![-72105, -1169982, 3420, 0, 0]], ![![-162304, 135788, 164722, 54621, 157653], ![-68787, -1116378, 3264, 0, 0]], ![![-91280, 76369, 92640, 30719, 88664], ![-38690, -627858, 1836, 0, 0]], ![![-101901, 85257, 103419, 34293, 98980], ![-43197, -700920, 2052, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-2, -17, 19, 0, 0], ![-2, -9, 0, 19, 0], ![-9, -6, 0, 0, 19]], ![![3, 5, -3, -1, -5], ![-2, -4, 3, 1, 3], ![-2, -6, 4, 3, 3], ![-6, -7, 1, 5, 12], ![0, 0, 1, -2, 0]]]
  hle1 := by decide
  hle2 := by decide

lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI19N0)

def MemCI19N0 : IdealMemCertificate O ℤ B I19N0
  ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![2, 17, 1, 0, 0], ![2, 9, 0, 1, 0], ![9, 6, 0, 0, 1]] ![20158, -10661, 12258, 8585, 65856] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI19N0
 g := ![-32328, -36392, 12258, 8585, 65856]
 hmem := by decide

def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [3, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 18], [0, 1]]
 g := ![![[6, 4], [3, 6], [1], [1]],![[10, 15], [9, 13], [1], [1]]]
 h' := ![![[1, 18], [10, 2], [6, 14], [16, 1], [0, 1]],![[0, 1], [12, 17], [1, 5], [17, 18], [1, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [12, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : PrimeIdeal O 19 where
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I19N0
  hcard := NI19N0
  P := [3, 18, 1]
  f := ofList [3, 18, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P19P0
  hneq := by decide
  hlen := by decide
  c := ![20158, -10661, 12258, 8585, 65856]
  a := ![-31, 9, -26, -31, -120]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI19N0
  hpmem := by
    show  _ ∈ I19N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI19N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := PrimeIdeal_isPrime PI19N0
def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0, 0, 0], ![-4, 4, -3, -1, -5]] i)))

def SI19N1: IdealEqSpanCertificate O ℤ timesTableO I19N1
 ![![19, 0, 0, 0, 0], ![-4, 4, -3, -1, -5]]
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![18, 12, 1, 0, 0], ![6, 4, 0, 1, 0], ![4, 14, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]], ![![-4, 4, -3, -1, -5], ![-3, -6, 2, 1, 3], ![3, -2, -4, 1, 3], ![3, 2, -1, -6, 0], ![-2, -1, 1, 0, -5]]]
  hmulB := by decide
  f := ![![![-87497, -149680, 46539, 24231, 68511], ![-39729, -500650, 532, 0, 0]], ![![-113859, -194777, 60559, 31532, 89154], ![-51699, -651491, 684, 0, 0]], ![![-154472, -264248, 82159, 42778, 120950], ![-70148, -883864, 934, 0, 0]], ![![-51602, -88272, 27445, 14290, 40403], ![-23435, -295256, 312, 0, 0]], ![![-102318, -175030, 54419, 28335, 80114], ![-46465, -585446, 616, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-18, -12, 19, 0, 0], ![-6, -4, 0, 19, 0], ![-4, -14, 0, 0, 19]], ![![4, 6, -3, -1, -5], ![-3, -4, 2, 1, 3], ![3, 0, -4, 1, 3], ![3, 2, -1, -6, 0], ![0, 3, 1, 0, -5]]]
  hle1 := by decide
  hle2 := by decide

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 361 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI19N1)

def MemCI19N1 : IdealMemCertificate O ℤ B I19N1
  ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![18, 12, 1, 0, 0], ![6, 4, 0, 1, 0], ![4, 14, 0, 0, 1]] ![-6483, 44462, -12989, -96172, -207474] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI19N1
 g := ![86013, 183666, -12989, -96172, -207474]
 hmem := by decide

def P19P1 : CertificateIrreducibleZModOfList' 19 2 2 4 [8, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 18], [0, 1]]
 g := ![![[10, 7], [], [16], [1]],![[1, 12], [], [16], [1]]]
 h' := ![![[15, 18], [0, 11], [12], [11, 15], [0, 1]],![[0, 1], [13, 8], [12], [8, 4], [15, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [5, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N1 : PrimeIdeal O 19 where
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I19N1
  hcard := NI19N1
  P := [8, 4, 1]
  f := ofList [8, 4, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P19P1
  hneq := by decide
  hlen := by decide
  c := ![-6483, 44462, -12989, -96172, -207474]
  a := ![-27, 37, -26, 30, -107]
  z := ![1,0,0,0,0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI19N1
  hpmem := by
    show  _ ∈ I19N1.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI19N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num


lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := PrimeIdeal_isPrime PI19N1
def I19N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0, 0, 0], ![9, 1, 0, 0, 0]] i)))

def SI19N2: IdealEqSpanCertificate O ℤ timesTableO I19N2
 ![![19, 0, 0, 0, 0], ![9, 1, 0, 0, 0]]
 ![![19, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![14, 0, 1, 0, 0], ![18, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]], ![![9, 1, 0, 0, 0], ![0, 9, 1, 0, 0], ![0, 1, 9, 2, 0], ![3, -1, 2, 12, 12], ![0, 0, 0, -2, 6]]]
  hmulB := by decide
  f := ![![![-451970, -98156, -705265, -154584, 3024], ![955757, -65873, 1497276, -4788, 0]], ![![-226026, -49093, -352687, -77304, 1512], ![477965, -32927, 748752, -2394, 0]], ![![-351478, -76335, -548468, -120216, 2352], ![743252, -51223, 1164396, -3724, 0]], ![![-426858, -92700, -666088, -145997, 2856], ![902654, -62220, 1414104, -4522, 0]], ![![-142734, -31004, -222716, -48816, 955], ![301832, -20788, 472824, -1512, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-9, 19, 0, 0, 0], ![-14, 0, 19, 0, 0], ![-18, 0, 0, 19, 0], ![-6, 0, 0, 0, 19]], ![![0, 1, 0, 0, 0], ![-5, 9, 1, 0, 0], ![-9, 1, 9, 2, 0], ![-16, -1, 2, 12, 12], ![0, 0, 0, -2, 6]]]
  hle1 := by decide
  hle2 := by decide

lemma NI19N2 : Nat.card (O ⧸ I19N2) = 19 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI19N2)

lemma isPrimeI19N2 : Ideal.IsPrime I19N2 := prime_ideal_of_norm_prime hp19.out _ NI19N2
def MulI19N0 : IdealMulEqCertificate O ℤ timesTableO (I19N0) I19N1
  ![![19, 0, 0, 0, 0], ![4, 5, -3, -1, -5]] ![![19, 0, 0, 0, 0], ![-4, 4, -3, -1, -5]]
  ![![19, 0, 0, 0, 0], ![-8, -30, 17, 5, 28]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![361, 0, 0, 0, 0], ![-76, 76, -57, -19, -95]], ![![76, 95, -57, -19, -95], ![-33, -5, 6, 4, 11]]]
 hmul := by decide
 f :=  ![![![![-12928834640869159, -22141636669936972, 6865553176979818, 3586962994303068, 10141808059428004], ![-5881256365192294, -74037263224226018, 3697558795380, 0, 0]], ![![-12407879108, 600928, 0, 0, 0], ![76, 0, 0, 0, 0]]], ![![![5392119622523328, 9234424979444470, -2863358147380675, -1495984292792095, -4229758038070984], ![2452845808051252, 30878094655748162, -1542109547366, 0, 0]], ![![5174849108, -250624, 0, 0, 0], ![-32, 0, 0, 0, 0]]]]
 g :=  ![![![![19, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![-4, 4, -3, -1, -5], ![0, 0, 0, 0, 0]]], ![![![4, 5, -3, -1, -5], ![0, 0, 0, 0, 0]], ![![5, 25, -14, -4, -23], ![16, 0, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI19N1 : IdealMulEqCertificate O ℤ timesTableO (I19N0*I19N1) I19N2
  ![![19, 0, 0, 0, 0], ![-8, -30, 17, 5, 28]] ![![19, 0, 0, 0, 0], ![9, 1, 0, 0, 0]]
  ![![19, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI19N0
 hI2 := rfl
 M :=  ![![![361, 0, 0, 0, 0], ![171, 19, 0, 0, 0]], ![![-152, -570, 323, 95, 532], ![-57, -266, 133, 38, 228]]]
 hmul := by decide
 f :=  ![![![![-23549865133958, -2726919082364, -1611019501851, -359497729332, 234406944], ![49716505673843, -146985494973, 3417455360862, -371157768, 0]], ![![5760, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]]
 g :=  ![![![![19, 0, 0, 0, 0]], ![![9, 1, 0, 0, 0]]], ![![![-8, -30, 17, 5, 28]], ![![-3, -14, 7, 2, 12]]]]
 hle1 := by decide
 hle2 := by decide

def PBC19 : PrimesBelowPCertificate 19 ![I19N0, I19N1, I19N2] where
  Ip := by
    intro i
    fin_cases i
    exact isPrimeI19N0
    exact isPrimeI19N1
    exact isPrimeI19N2
  hPprod := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI19N1, Set.range_unique]
    dsimp ; congr
    erw [B_int_repr]
    rfl
instance hp23 : Fact (Nat.Prime 23) := by decide
def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0, 0], ![-6, 2, -3, -1, -5]] i)))

def SI23N0: IdealEqSpanCertificate O ℤ timesTableO I23N0
 ![![23, 0, 0, 0, 0], ![-6, 2, -3, -1, -5]]
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![14, 18, 1, 0, 0], ![12, 18, 0, 1, 0], ![18, 22, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]], ![![-6, 2, -3, -1, -5], ![-3, -8, 0, 1, 3], ![3, -4, -6, -3, 3], ![-3, 4, -5, -14, -24], ![-2, -1, 1, 4, -1]]]
  hmulB := by decide
  f := ![![![-24092, -60954, -477, 7518, 22092], ![-4071, -176364, 207, 0, 0]], ![![-158025, -399781, -3147, 49300, 144890], ![-26749, -1156716, 1311, 0, 0]], ![![-137975, -349060, -2746, 43046, 126508], ![-23351, -1009962, 1149, 0, 0]], ![![-136242, -344674, -2712, 42505, 124918], ![-23060, -997272, 1134, 0, 0]], ![![-170010, -430102, -3384, 53040, 155879], ![-28776, -1244448, 1416, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-14, -18, 23, 0, 0], ![-12, -18, 0, 23, 0], ![-18, -22, 0, 0, 23]], ![![6, 8, -3, -1, -5], ![-3, -4, 0, 1, 3], ![3, 4, -6, -3, 3], ![29, 38, -5, -14, -24], ![-2, -3, 1, 4, -1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI23N0)

def MemCI23N0 : IdealMemCertificate O ℤ B I23N0
  ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![14, 18, 1, 0, 0], ![12, 18, 0, 1, 0], ![18, 22, 0, 0, 1]] ![43219, -14812, 24326, -1006, 103556] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI23N0
 g := ![-93447, -117948, 24326, -1006, 103556]
 hmem := by decide

def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [1, 1, 1] where
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
 g := ![![[1, 1], [1, 1], [1, 1], [1]],![[0, 22], [0, 22], [0, 22], [1]]]
 h' := ![![[22, 22], [22, 22], [22, 22], [22, 22], [0, 1]],![[0, 1], [0, 1], [0, 1], [0, 1], [22, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [8, 16]]
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
  P := [1, 1, 1]
  f := ofList [1, 1, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P23P0
  hneq := by decide
  hlen := by decide
  c := ![43219, -14812, 24326, -1006, 103556]
  a := ![43, -18, 43, 36, 172]
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
def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0, 0], ![-2, 14, -3, -1, -5]] i)))

def SI23N1: IdealEqSpanCertificate O ℤ timesTableO I23N1
 ![![23, 0, 0, 0, 0], ![-2, 14, -3, -1, -5]]
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![11, 9, 1, 0, 0], ![8, 0, 0, 1, 0], ![6, 1, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]], ![![-2, 14, -3, -1, -5], ![-3, -4, 12, 1, 3], ![3, 8, -2, 21, 3], ![33, -8, 19, 26, 120], ![-2, -1, 1, -20, -33]]]
  hmulB := by decide
  f := ![![![165622, 108498, -587019, -41622, -117636], ![155595, 1163616, -2415, 0, 0]], ![![212097, 138937, -751734, -53289, -150639], ![199272, 1490124, -3105, 0, 0]], ![![161180, 105587, -571273, -40501, -114479], ![151426, 1132404, -2355, 0, 0]], ![![57608, 37736, -204180, -14477, -40916], ![54124, 404736, -840, 0, 0]], ![![52429, 34333, -185817, -13174, -37233], ![49273, 368340, -765, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-11, -9, 23, 0, 0], ![-8, 0, 0, 23, 0], ![-6, -1, 0, 0, 23]], ![![3, 2, -3, -1, -5], ![-7, -5, 12, 1, 3], ![-7, 1, -2, 21, 3], ![-48, -13, 19, 26, 120], ![15, 1, 1, -20, -33]]]
  hle1 := by decide
  hle2 := by decide

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 529 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI23N1)

def MemCI23N1 : IdealMemCertificate O ℤ B I23N1
  ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![11, 9, 1, 0, 0], ![8, 0, 0, 1, 0], ![6, 1, 0, 0, 1]] ![821, -302, 480, 60, 2140] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI23N1
 g := ![-773, -294, 480, 60, 2140]
 hmem := by decide

def P23P1 : CertificateIrreducibleZModOfList' 23 2 2 4 [3, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 22], [0, 1]]
 g := ![![[7, 8], [1, 6], [19, 4], [1]],![[0, 15], [13, 17], [4, 19], [1]]]
 h' := ![![[2, 22], [20, 13], [12, 12], [20, 2], [0, 1]],![[0, 1], [0, 10], [13, 11], [1, 21], [2, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [17, 6]]
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
  P := [3, 21, 1]
  f := ofList [3, 21, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P23P1
  hneq := by decide
  hlen := by decide
  c := ![821, -302, 480, 60, 2140]
  a := ![5, -2, 4, 4, 20]
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
def I23N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0, 0], ![-4, 1, 0, 0, 0]] i)))

def SI23N2: IdealEqSpanCertificate O ℤ timesTableO I23N2
 ![![23, 0, 0, 0, 0], ![-4, 1, 0, 0, 0]]
 ![![23, 0, 0, 0, 0], ![19, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![16, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]], ![![-4, 1, 0, 0, 0], ![0, -4, 1, 0, 0], ![0, 1, -4, 2, 0], ![3, -1, 2, -1, 12], ![0, 0, 0, -2, -7]]]
  hmulB := by decide
  f := ![![![12258, -13600, 44514, -22333, 1092], ![68908, 3496, 255783, -2093, 0]], ![![10372, -11512, 37689, -18909, 924], ![58306, 2967, 216568, -1771, 0]], ![![3773, -4183, 13693, -6870, 336], ![21210, 1082, 78683, -644, 0]], ![![8485, -9412, 30818, -15462, 756], ![47698, 2440, 177089, -1449, 0]], ![![1068, -1180, 3870, -1942, 95], ![6004, 322, 22242, -182, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-19, 23, 0, 0, 0], ![-7, 0, 23, 0, 0], ![-16, 0, 0, 23, 0], ![-2, 0, 0, 0, 23]], ![![-1, 1, 0, 0, 0], ![3, -4, 1, 0, 0], ![-1, 1, -4, 2, 0], ![0, -1, 2, -1, 12], ![2, 0, 0, -2, -7]]]
  hle1 := by decide
  hle2 := by decide

lemma NI23N2 : Nat.card (O ⧸ I23N2) = 23 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI23N2)

lemma isPrimeI23N2 : Ideal.IsPrime I23N2 := prime_ideal_of_norm_prime hp23.out _ NI23N2
def MulI23N0 : IdealMulEqCertificate O ℤ timesTableO (I23N0) I23N1
  ![![23, 0, 0, 0, 0], ![-6, 2, -3, -1, -5]] ![![23, 0, 0, 0, 0], ![-2, 14, -3, -1, -5]]
  ![![23, 0, 0, 0, 0], ![22, -19, -15, -9, -22]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![529, 0, 0, 0, 0], ![-46, 322, -69, -23, -115]], ![![-138, 46, -69, -23, -115], ![-26, -103, 24, 19, 72]]]
 hmul := by decide
 f :=  ![![![![3919270168966322846, 2556580497504077237, -13914734314164242255, -1038215507349260865, -2797798110545478820], ![3683695462160600772, 27590609448927738990, -1331295051429725, 0, 0]], ![![121658784503, 4670120, 0, 0, 0], ![345, 0, 0, 0, 0]]], ![![![3746020893474882198, 2443568201889624487, -13299640805767332901, -992321737157940457, -2674122917275716048], ![3520859642623630352, 26370981076471157546, -1272445854211366, 0, 0]], ![![116280921950, 4463680, 0, 0, 0], ![330, 0, 0, 0, 0]]]]
 g :=  ![![![![1, 19, 15, 9, 22], ![23, 0, 0, 0, 0]], ![![-2, 14, -3, -1, -5], ![0, 0, 0, 0, 0]]], ![![![-6, 2, -3, -1, -5], ![0, 0, 0, 0, 0]], ![![-4, -2, 3, 2, 6], ![3, 0, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI23N1 : IdealMulEqCertificate O ℤ timesTableO (I23N0*I23N1) I23N2
  ![![23, 0, 0, 0, 0], ![22, -19, -15, -9, -22]] ![![23, 0, 0, 0, 0], ![-4, 1, 0, 0, 0]]
  ![![23, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI23N0
 hI2 := rfl
 M :=  ![![![529, 0, 0, 0, 0], ![-92, 23, 0, 0, 0]], ![![506, -437, -345, -207, -506], ![-115, 92, 23, 23, 46]]]
 hmul := by decide
 f :=  ![![![![814030, -894328, 2918146, -1464131, 72684], ![4575364, 228708, 16767201, -139531, 0]], ![![-120, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]]
 g :=  ![![![![23, 0, 0, 0, 0]], ![![-4, 1, 0, 0, 0]]], ![![![22, -19, -15, -9, -22]], ![![-5, 4, 1, 1, 2]]]]
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
