
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Examples.NF4_0_76176_2.RI4_0_76176_2
import IdealArithmetic.ClassGroupGeneration

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0], ![0, 1, 0, 0]] i)))

def SI2N0: IdealEqSpanCertificate O ℤ timesTableO I2N0
 ![![2, 0, 0, 0], ![0, 1, 0, 0]] 
 ![![2, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![2, 0, 0, 0], ![0, 2, 0, 0], ![0, 0, 2, 0], ![0, 0, 0, 2]], ![![0, 1, 0, 0], ![0, 0, 1, 0], ![16, -15, -16, 35], ![6, -8, -8, 18]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![1, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 1, 0, 0]], ![![8, -12, -7, 18], ![9, -2, -1, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 2, 0, 0], ![0, 0, 2, 0], ![0, 0, 0, 2]], ![![0, 1, 0, 0], ![0, 0, 1, 0], ![8, -15, -16, 35], ![3, -8, -8, 18]]]
  hle1 := by decide
  hle2 := by decide

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0
def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0], ![3, -1, 0, 1]] i)))

def SI2N1: IdealEqSpanCertificate O ℤ timesTableO I2N1
 ![![2, 0, 0, 0], ![3, -1, 0, 1]] 
 ![![2, 0, 0, 0], ![1, 1, 0, 0], ![1, 0, 1, 0], ![0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![2, 0, 0, 0], ![0, 2, 0, 0], ![0, 0, 2, 0], ![0, 0, 0, 2]], ![![3, -1, 0, 1], ![6, -5, -9, 18], ![-36, -3, -5, 9], ![-16, -4, -6, 11]]]
  hmulB := by decide
  f := ![![![-59, -67, -301, 503], ![200, -68, 2, 0]], ![![-28, -32, -146, 244], ![97, -33, 1, 0]], ![![-31, -33, -150, 251], ![101, -34, 1, 0]], ![![27, 33, 146, -244], ![-96, 33, -1, 0]]]
  g := ![![![1, 0, 0, 0], ![-1, 2, 0, 0], ![-1, 0, 2, 0], ![0, 0, 0, 2]], ![![2, -1, 0, 1], ![10, -5, -9, 18], ![-14, -3, -5, 9], ![-3, -4, -6, 11]]]
  hle1 := by decide
  hle2 := by decide

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulEqCertificate O ℤ timesTableO (I2N0) I2N0
  ![![2, 0, 0, 0], ![0, 1, 0, 0]] ![![2, 0, 0, 0], ![0, 1, 0, 0]]
  ![![2, 0, 0, 0], ![0, 0, -1, 2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![4, 0, 0, 0], ![0, 2, 0, 0]], ![![0, 2, 0, 0], ![0, 0, 1, 0]]]
 hmul := by decide
 f :=  ![![![![-33013, 49600, 26208, -72345], ![-37199, 13104, 4095, 0]], ![![0, 0, 0, 0], ![1269, 72, 3, 0]]], ![![![24, -36, -20, 53], ![27, -8, -3, 0]], ![![0, 0, 0, 0], ![-1, 0, 0, 0]]]]
 g :=  ![![![![2, 0, 0, 0], ![0, 0, 0, 0]], ![![-4, 0, 0, 1], ![0, -2, 0, 0]]], ![![![-4, 0, 0, 1], ![0, -2, 0, 0]], ![![0, 0, 0, 1], ![-1, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI2N1 : IdealMulEqCertificate O ℤ timesTableO (I2N0*I2N0) I2N1
  ![![2, 0, 0, 0], ![0, 0, -1, 2]] ![![2, 0, 0, 0], ![3, -1, 0, 1]]
  ![![2, 0, 0, 0], ![2, -1, -1, 3]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI2N0
 hI2 := rfl
 M :=  ![![![4, 0, 0, 0], ![6, -2, 0, 2]], ![![0, 0, -2, 4], ![4, -5, -7, 13]]]
 hmul := by decide
 f :=  ![![![![-910, -970, -4000, 6753], ![2503, -894, 9, 0]], ![![1, 0, 0, 0], ![0, 0, 0, 0]]], ![![![-924, -989, -4068, 6869], ![2543, -909, 9, 0]], ![![4, 0, 0, 0], ![-1, 0, 0, 0]]]]
 g :=  ![![![![2, 0, 0, 0], ![0, 0, 0, 0]], ![![1, 0, 1, -2], ![2, 0, 0, 0]]], ![![![0, 0, -1, 2], ![0, 0, 0, 0]], ![![3, 0, 0, 0], ![-2, 1, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI2N2 : IdealMulEqCertificate O ℤ timesTableO (I2N0*I2N0*I2N1) I2N1
  ![![2, 0, 0, 0], ![2, -1, -1, 3]] ![![2, 0, 0, 0], ![3, -1, 0, 1]]
  ![![2, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI2N1
 hI2 := rfl
 M :=  ![![![4, 0, 0, 0], ![6, -2, 0, 2]], ![![4, -2, -2, 6], ![-12, -6, -4, 8]]]
 hmul := by decide
 f :=  ![![![![-9376, -10025, -41331, 69785], ![25847, -9237, 93, 0]], ![![0, 0, 0, 0], ![3, 0, 0, 0]]]]
 g :=  ![![![![2, 0, 0, 0]], ![![3, -1, 0, 1]]], ![![![2, -1, -1, 3]], ![![-6, -3, -2, 4]]]]
 hle1 := by decide
 hle2 := by decide

def PBC2 : PrimesBelowPCertificate 2 ![I2N0, I2N0, I2N1, I2N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N0
    exact isPrimeI2N1
    exact isPrimeI2N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI2N2, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0], ![-1, 0, -2, 3]] i)))

def SI3N0: IdealEqSpanCertificate O ℤ timesTableO I3N0
 ![![3, 0, 0, 0], ![-1, 0, -2, 3]] 
 ![![3, 0, 0, 0], ![2, 1, 0, 0], ![2, 0, 1, 0], ![1, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![3, 0, 0, 0], ![0, 3, 0, 0], ![0, 0, 3, 0], ![0, 0, 0, 3]], ![![-1, 0, -2, 3], ![-14, 5, 8, -16], ![32, -6, 5, -8], ![10, 0, 6, -11]]]
  hmulB := by decide
  f := ![![![254, -72, -44, 113], ![63, 36, -6, 0]], ![![164, -46, -28, 72], ![40, 23, -4, 0]], ![![127, -36, -22, 57], ![31, 18, -3, 0]], ![![85, -24, -14, 37], ![22, 12, -2, 0]]]
  g := ![![![1, 0, 0, 0], ![-2, 3, 0, 0], ![-2, 0, 3, 0], ![-1, 0, 0, 3]], ![![0, 0, -2, 3], ![-8, 5, 8, -16], ![14, -6, 5, -8], ![3, 0, 6, -11]]]
  hle1 := by decide
  hle2 := by decide

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0
def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0], ![2, -2, 0, 1]] i)))

def SI3N1: IdealEqSpanCertificate O ℤ timesTableO I3N1
 ![![3, 0, 0, 0], ![2, -2, 0, 1]] 
 ![![3, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![2, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![3, 0, 0, 0], ![0, 3, 0, 0], ![0, 0, 3, 0], ![0, 0, 0, 3]], ![![2, -2, 0, 1], ![6, -6, -10, 18], ![-52, 12, 10, -26], ![-22, 4, 2, -8]]]
  hmulB := by decide
  f := ![![![123, -42, -420, 661], ![333, -120, 6, 0]], ![![-22, 9, 70, -111], ![-53, 20, -1, 0]], ![![-2, 2, 7, -11], ![-3, 2, 0, 0]], ![![82, -28, -280, 441], ![222, -80, 4, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 3, 0, 0], ![0, 0, 3, 0], ![-2, 0, 0, 3]], ![![0, -2, 0, 1], ![-10, -6, -10, 18], ![0, 12, 10, -26], ![-2, 4, 2, -8]]]
  hle1 := by decide
  hle2 := by decide

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulEqCertificate O ℤ timesTableO (I3N0) I3N0
  ![![3, 0, 0, 0], ![-1, 0, -2, 3]] ![![3, 0, 0, 0], ![-1, 0, -2, 3]]
  ![![3, 0, 0, 0], ![0, 0, -1, 2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![9, 0, 0, 0], ![-3, 0, -6, 9]], ![![-3, 0, -6, 9], ![-33, 12, 10, -20]]]
 hmul := by decide
 f :=  ![![![![-355650538, 101688780, 64163404, -162835281], ![-87060699, -50844390, 8266590, 0]], ![![0, 0, 0, 0], ![-339840, -14790, -56, 0]]], ![![![50787842, -14521428, -9162704, 23253310], ![12432500, 7260714, -1180491, 0]], ![![0, 0, 0, 0], ![48530, 2112, 8, 0]]]]
 g :=  ![![![![3, 0, 0, 0], ![0, 0, 0, 0]], ![![3, 1, -2, 2], ![0, 3, 0, 0]]], ![![![3, 1, -2, 2], ![0, 3, 0, 0]], ![![-3, 6, 12, -26], ![26, 6, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI3N1 : IdealMulEqCertificate O ℤ timesTableO (I3N0*I3N0) I3N1
  ![![3, 0, 0, 0], ![0, 0, -1, 2]] ![![3, 0, 0, 0], ![2, -2, 0, 1]]
  ![![3, 0, 0, 0], ![2, -1, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI3N0
 hI2 := rfl
 M :=  ![![![9, 0, 0, 0], ![6, -6, 0, 3]], ![![0, 0, -3, 6], ![8, -4, -6, 10]]]
 hmul := by decide
 f :=  ![![![![1283, -988, -7830, 12286], ![5612, -2320, 22, 0]], ![![-64, 0, 0, 0], ![-3, 0, 0, 0]]], ![![![862, -661, -5238, 8219], ![3756, -1552, 15, 0]], ![![-40, 0, 0, 0], ![-2, 0, 0, 0]]]]
 g :=  ![![![![1, 1, 0, -1], ![3, 0, 0, 0]], ![![0, -1, 0, 0], ![3, 0, 0, 0]]], ![![![0, 0, -1, 2], ![0, 0, 0, 0]], ![![0, 0, -2, 2], ![4, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI3N2 : IdealMulEqCertificate O ℤ timesTableO (I3N0*I3N0*I3N1) I3N1
  ![![3, 0, 0, 0], ![2, -1, 0, 1]] ![![3, 0, 0, 0], ![2, -2, 0, 1]]
  ![![3, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI3N1
 hI2 := rfl
 M :=  ![![![9, 0, 0, 0], ![6, -6, 0, 3]], ![![6, -3, 0, 3], ![-24, 6, 12, -24]]]
 hmul := by decide
 f :=  ![![![![1825, -1314, -10476, 16435], ![7571, -3104, 38, 0]], ![![0, 0, 0, 0], ![2, 0, 0, 0]]]]
 g :=  ![![![![3, 0, 0, 0]], ![![2, -2, 0, 1]]], ![![![2, -1, 0, 1]], ![![-8, 2, 4, -8]]]]
 hle1 := by decide
 hle2 := by decide

def PBC3 : PrimesBelowPCertificate 3 ![I3N0, I3N0, I3N1, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N1
    exact isPrimeI3N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI3N2, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0, 0], ![-1, -1, -2, 4]] i)))

def SI5N0: IdealEqSpanCertificate O ℤ timesTableO I5N0
 ![![5, 0, 0, 0], ![-1, -1, -2, 4]] 
 ![![5, 0, 0, 0], ![0, 5, 0, 0], ![2, 4, 1, 0], ![2, 3, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![5, 0, 0, 0], ![0, 5, 0, 0], ![0, 0, 5, 0], ![0, 0, 0, 5]], ![![-1, -1, -2, 4], ![-8, -3, -1, 2], ![-4, -9, -3, 1], ![-6, -4, 0, -3]]]
  hmulB := by decide
  f := ![![![-17, -12, 0, -9], ![0, 0, 0, -15]], ![![19, 14, 2, 5], ![5, 0, 0, 15]], ![![8, 6, 1, 2], ![2, 0, 0, 6]], ![![5, 4, 2, -2], ![5, 0, 0, 3]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-2, -4, 5, 0], ![-2, -3, 0, 5]], ![![-1, -1, -2, 4], ![-2, -1, -1, 2], ![0, 0, -3, 1], ![0, 1, 0, -3]]]
  hle1 := by decide
  hle2 := by decide

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 25 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI5N0)

def MemCI5N0 : IdealMemCertificate O ℤ B I5N0
  ![![5, 0, 0, 0], ![0, 5, 0, 0], ![2, 4, 1, 0], ![2, 3, 0, 1]] ![-548, -66, 156, -525] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI5N0
 g := ![38, 177, 156, -525]
 hmem := by decide

def P5P0 : CertificateIrreducibleZModOfList' 5 2 2 2 [4, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 4], [0, 1]]
 g := ![![[2, 4], [1]],![[0, 1], [1]]]
 h' := ![![[2, 4], [1, 2], [0, 1]],![[0, 1], [0, 3], [2, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [4, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : PrimeIdeal O 5 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I5N0
  hcard := NI5N0
  P := [4, 3, 1]
  f := ofList [4, 3, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P5P0
  hneq := by decide
  hlen := by decide
  c := ![-548, -66, 156, -525]
  a := ![-16, 14, 15, -35]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI5N0
  hpmem := by 
    show  _ ∈ I5N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI5N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := PrimeIdeal_isPrime PI5N0
def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0, 0], ![-3, 1, 0, 0]] i)))

def SI5N1: IdealEqSpanCertificate O ℤ timesTableO I5N1
 ![![5, 0, 0, 0], ![-3, 1, 0, 0]] 
 ![![5, 0, 0, 0], ![2, 1, 0, 0], ![1, 0, 1, 0], ![0, 0, 0, 5]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![5, 0, 0, 0], ![0, 5, 0, 0], ![0, 0, 5, 0], ![0, 0, 0, 5]], ![![-3, 1, 0, 0], ![0, -3, 1, 0], ![16, -15, -19, 35], ![6, -8, -8, 15]]]
  hmulB := by decide
  f := ![![![13, -4, 0, 0], ![20, 0, 0, 0]], ![![4, -1, 0, 0], ![6, 0, 0, 0]], ![![-1, 4, -1, 0], ![-2, 6, 0, 0]], ![![0, 0, 0, 1], ![0, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![-2, 5, 0, 0], ![-1, 0, 5, 0], ![0, 0, 0, 1]], ![![-1, 1, 0, 0], ![1, -3, 1, 0], ![13, -15, -19, 7], ![6, -8, -8, 3]]]
  hle1 := by decide
  hle2 := by decide

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 25 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI5N1)

def MemCI5N1 : IdealMemCertificate O ℤ B I5N1
  ![![5, 0, 0, 0], ![2, 1, 0, 0], ![1, 0, 1, 0], ![0, 0, 0, 5]] ![-215071, -100524, -162518, 287820] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI5N1
 g := ![29699, -100524, -162518, 57564]
 hmem := by decide

def P5P1 : CertificateIrreducibleZModOfList' 5 2 2 2 [3, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 4], [0, 1]]
 g := ![![[4, 4], [1]],![[1, 1], [1]]]
 h' := ![![[3, 4], [2, 3], [0, 1]],![[0, 1], [1, 2], [3, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [4, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N1 : PrimeIdeal O 5 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I5N1
  hcard := NI5N1
  P := [3, 2, 1]
  f := ofList [3, 2, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P5P1
  hneq := by decide
  hlen := by decide
  c := ![-215071, -100524, -162518, 287820]
  a := ![-6, 8, -60, -13]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI5N1
  hpmem := by 
    show  _ ∈ I5N1.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI5N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := PrimeIdeal_isPrime PI5N1
def MulI5N0 : IdealMulEqCertificate O ℤ timesTableO (I5N0) I5N1
  ![![5, 0, 0, 0], ![-1, -1, -2, 4]] ![![5, 0, 0, 0], ![-3, 1, 0, 0]]
  ![![5, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![25, 0, 0, 0], ![-15, 5, 0, 0]], ![![-5, -5, -10, 20], ![-5, 0, 5, -10]]]
 hmul := by decide
 f :=  ![![![![-51206, 12721, -13106, 23908], ![-75544, 5868, 0, 0]], ![![-29831, 0, 0, 72], ![0, 0, 0, 0]]]]
 g :=  ![![![![5, 0, 0, 0]], ![![-3, 1, 0, 0]]], ![![![-1, -1, -2, 4]], ![![-1, 0, 1, -2]]]]
 hle1 := by decide
 hle2 := by decide

def PBC5 : PrimesBelowPCertificate 5 ![I5N0, I5N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI5N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0], ![-4, 1, 0, 0]] i)))

def SI7N0: IdealEqSpanCertificate O ℤ timesTableO I7N0
 ![![7, 0, 0, 0], ![-4, 1, 0, 0]] 
 ![![7, 0, 0, 0], ![3, 1, 0, 0], ![5, 0, 1, 0], ![0, 0, 0, 7]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![7, 0, 0, 0], ![0, 7, 0, 0], ![0, 0, 7, 0], ![0, 0, 0, 7]], ![![-4, 1, 0, 0], ![0, -4, 1, 0], ![16, -15, -20, 35], ![6, -8, -8, 14]]]
  hmulB := by decide
  f := ![![![17, -4, 0, 0], ![28, 0, 0, 0]], ![![13, -3, 0, 0], ![22, 0, 0, 0]], ![![11, -2, 0, 0], ![18, 1, 0, 0]], ![![0, 0, 0, 1], ![0, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![-3, 7, 0, 0], ![-5, 0, 7, 0], ![0, 0, 0, 1]], ![![-1, 1, 0, 0], ![1, -4, 1, 0], ![23, -15, -20, 5], ![10, -8, -8, 2]]]
  hle1 := by decide
  hle2 := by decide

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 49 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI7N0)

def MemCI7N0 : IdealMemCertificate O ℤ B I7N0
  ![![7, 0, 0, 0], ![3, 1, 0, 0], ![5, 0, 1, 0], ![0, 0, 0, 7]] ![310, 728, 2743, -7252] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI7N0
 g := ![-2227, 728, 2743, -1036]
 hmem := by decide

def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [3, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 6], [0, 1]]
 g := ![![[3, 1], [5, 1]],![[1, 6], [3, 6]]]
 h' := ![![[5, 6], [6, 1], [0, 1]],![[0, 1], [4, 6], [5, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [2, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : PrimeIdeal O 7 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I7N0
  hcard := NI7N0
  P := [3, 2, 1]
  f := ofList [3, 2, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P7P0
  hneq := by decide
  hlen := by decide
  c := ![310, 728, 2743, -7252]
  a := ![-59, 56, 59, -129]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI7N0
  hpmem := by 
    show  _ ∈ I7N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI7N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := PrimeIdeal_isPrime PI7N0
def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0], ![-2, -1, -2, 4]] i)))

def SI7N1: IdealEqSpanCertificate O ℤ timesTableO I7N1
 ![![7, 0, 0, 0], ![-2, -1, -2, 4]] 
 ![![7, 0, 0, 0], ![0, 7, 0, 0], ![4, 6, 1, 0], ![5, 1, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![7, 0, 0, 0], ![0, 7, 0, 0], ![0, 0, 7, 0], ![0, 0, 0, 7]], ![![-2, -1, -2, 4], ![-8, -4, -1, 2], ![-4, -9, -4, 1], ![-6, -4, 0, -4]]]
  hmulB := by decide
  f := ![![![25, 16, 0, 16], ![0, 0, 0, 28]], ![![-6, -3, 0, -4], ![0, 0, 0, -7]], ![![10, 7, 1, 4], ![3, 0, 0, 10]], ![![17, 11, 0, 11], ![0, 0, 0, 19]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-4, -6, 7, 0], ![-5, -1, 0, 7]], ![![-2, 1, -2, 4], ![-2, 0, -1, 2], ![1, 2, -4, 1], ![2, 0, 0, -4]]]
  hle1 := by decide
  hle2 := by decide

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 49 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI7N1)

def MemCI7N1 : IdealMemCertificate O ℤ B I7N1
  ![![7, 0, 0, 0], ![0, 7, 0, 0], ![4, 6, 1, 0], ![5, 1, 0, 1]] ![578, -8, 22, -105] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI7N1
 g := ![145, -5, 22, -105]
 hmem := by decide

def P7P1 : CertificateIrreducibleZModOfList' 7 2 2 2 [2, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 6], [0, 1]]
 g := ![![[6, 4], [2, 1]],![[0, 3], [4, 6]]]
 h' := ![![[2, 6], [3, 2], [0, 1]],![[0, 1], [0, 5], [2, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [3, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N1 : PrimeIdeal O 7 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I7N1
  hcard := NI7N1
  P := [2, 5, 1]
  f := ofList [2, 5, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P7P1
  hneq := by decide
  hlen := by decide
  c := ![578, -8, 22, -105]
  a := ![16, -16, -17, 35]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI7N1
  hpmem := by 
    show  _ ∈ I7N1.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI7N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := PrimeIdeal_isPrime PI7N1
def MulI7N0 : IdealMulEqCertificate O ℤ timesTableO (I7N0) I7N1
  ![![7, 0, 0, 0], ![-4, 1, 0, 0]] ![![7, 0, 0, 0], ![-2, -1, -2, 4]]
  ![![7, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![49, 0, 0, 0], ![-14, -7, -14, 28]], ![![-28, 7, 0, 0], ![0, 0, 7, -14]]]
 hmul := by decide
 f :=  ![![![![698785, 441937, -1278, 451564], ![-4377, 0, 0, 785860]], ![![46272, 192, 0, 0], ![0, 0, 0, 0]]]]
 g :=  ![![![![7, 0, 0, 0]], ![![-2, -1, -2, 4]]], ![![![-4, 1, 0, 0]], ![![0, 0, 1, -2]]]]
 hle1 := by decide
 hle2 := by decide

def PBC7 : PrimesBelowPCertificate 7 ![I7N0, I7N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI7N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}
def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, -2, -2, 4]] i)))

def SI11N0: IdealEqSpanCertificate O ℤ timesTableO I11N0
 ![![3, -2, -2, 4]] 
 ![![11, 0, 0, 0], ![0, 11, 0, 0], ![4, 9, 1, 0], ![0, 4, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![3, -2, -2, 4], ![-8, 1, -2, 2], ![-20, 6, 17, -34], ![-12, 4, 8, -17]]]
  hmulB := by decide
  f := ![![![1, -2, -2, 4]], ![![-8, -1, -2, 2]], ![![-8, -1, -1, 0]], ![![-4, 0, 0, -1]]]
  g := ![![![1, 0, -2, 4], ![0, 1, -2, 2], ![-8, -1, 17, -34], ![-4, 0, 8, -17]]]
  hle1 := by decide
  hle2 := by decide

lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI11N0)

def MemCI11N0 : IdealMemCertificate O ℤ B I11N0
  ![![11, 0, 0, 0], ![0, 11, 0, 0], ![4, 9, 1, 0], ![0, 4, 0, 1]] ![-128645, -20724, 42251, -134816] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI11N0
 g := ![-27059, 12571, 42251, -134816]
 hmem := by decide

def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [8, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 10], [0, 1]]
 g := ![![[4, 9], [7, 1], [1]],![[2, 2], [8, 10], [1]]]
 h' := ![![[1, 10], [10, 8], [3, 1], [0, 1]],![[0, 1], [7, 3], [4, 10], [1, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [6, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : PrimeIdeal O 11 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I11N0
  hcard := NI11N0
  P := [8, 10, 1]
  f := ofList [8, 10, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P11P0
  hneq := by decide
  hlen := by decide
  c := ![-128645, -20724, 42251, -134816]
  a := ![257, -234, -239, 561]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI11N0
  hpmem := by 
    show  _ ∈ I11N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI11N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := PrimeIdeal_isPrime PI11N0
def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 2, 2, -4]] i)))

def SI11N1: IdealEqSpanCertificate O ℤ timesTableO I11N1
 ![![-1, 2, 2, -4]] 
 ![![11, 0, 0, 0], ![0, 11, 0, 0], ![3, 0, 1, 0], ![10, 5, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![-1, 2, 2, -4], ![8, 1, 2, -2], ![20, -6, -15, 34], ![12, -4, -8, 19]]]
  hmulB := by decide
  f := ![![![-3, 2, 2, -4]], ![![8, -1, 2, -2]], ![![1, 0, -1, 2]], ![![2, 1, 2, -3]]]
  g := ![![![3, 2, 2, -4], ![2, 1, 2, -2], ![-25, -16, -15, 34], ![-14, -9, -8, 19]]]
  hle1 := by decide
  hle2 := by decide

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 121 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI11N1)

def MemCI11N1 : IdealMemCertificate O ℤ B I11N1
  ![![11, 0, 0, 0], ![0, 11, 0, 0], ![3, 0, 1, 0], ![10, 5, 0, 1]] ![128, 0, 259, -726] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI11N1
 g := ![601, 330, 259, -726]
 hmem := by decide

def P11P1 : CertificateIrreducibleZModOfList' 11 2 2 3 [9, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 10], [0, 1]]
 g := ![![[9, 5], [8, 5], [1]],![[0, 6], [10, 6], [1]]]
 h' := ![![[7, 10], [5, 4], [2, 7], [0, 1]],![[0, 1], [0, 7], [7, 4], [7, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [9, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N1 : PrimeIdeal O 11 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I11N1
  hcard := NI11N1
  P := [9, 4, 1]
  f := ofList [9, 4, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P11P1
  hneq := by decide
  hlen := by decide
  c := ![128, 0, 259, -726]
  a := ![21, -20, -21, 46]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI11N1
  hpmem := by 
    show  _ ∈ I11N1.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI11N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := PrimeIdeal_isPrime PI11N1
def MulI11N0 : IdealMulEqCertificate O ℤ timesTableO (I11N0) I11N1
  ![![3, -2, -2, 4]] ![![-1, 2, 2, -4]]
  ![![11, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![-11, 0, 0, 0]]]
 hmul := by decide
 f :=  ![![![![-1, 0, 0, 0]]]]
 g :=  ![![![![-1, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def PBC11 : PrimesBelowPCertificate 11 ![I11N0, I11N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
    exact isPrimeI11N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI11N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}
def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0], ![8, -1, 0, 1]] i)))

def SI13N0: IdealEqSpanCertificate O ℤ timesTableO I13N0
 ![![13, 0, 0, 0], ![8, -1, 0, 1]] 
 ![![13, 0, 0, 0], ![8, 1, 0, 0], ![1, 0, 1, 0], ![3, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![13, 0, 0, 0], ![0, 13, 0, 0], ![0, 0, 13, 0], ![0, 0, 0, 13]], ![![8, -1, 0, 1], ![6, 0, -9, 18], ![-36, -3, 0, 9], ![-16, -4, -6, 16]]]
  hmulB := by decide
  f := ![![![643689, 48299, -1539720, 3030781], ![625547, -2224040, 780, 0]], ![![406012, 30465, -971190, 1911688], ![394568, -1402830, 492, 0]], ![![39613, 2973, -94763, 186531], ![38505, -136880, 48, 0]], ![![148543, 11146, -355320, 699411], ![144358, -513240, 180, 0]]]
  g := ![![![1, 0, 0, 0], ![-8, 13, 0, 0], ![-1, 0, 13, 0], ![-3, 0, 0, 13]], ![![1, -1, 0, 1], ![-3, 0, -9, 18], ![-3, -3, 0, 9], ![-2, -4, -6, 16]]]
  hle1 := by decide
  hle2 := by decide

lemma NI13N0 : Nat.card (O ⧸ I13N0) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI13N0)

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := prime_ideal_of_norm_prime hp13.out _ NI13N0
def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0], ![5, -1, 0, 1]] i)))

def SI13N1: IdealEqSpanCertificate O ℤ timesTableO I13N1
 ![![13, 0, 0, 0], ![5, -1, 0, 1]] 
 ![![13, 0, 0, 0], ![12, 1, 0, 0], ![12, 0, 1, 0], ![4, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![13, 0, 0, 0], ![0, 13, 0, 0], ![0, 0, 13, 0], ![0, 0, 0, 13]], ![![5, -1, 0, 1], ![6, -3, -9, 18], ![-36, -3, -3, 9], ![-16, -4, -6, 13]]]
  hmulB := by decide
  f := ![![![92061, -53455, -175695, 346270], ![66170, -253825, 130, 0]], ![![120287, -69843, -229557, 452425], ![86447, -331639, 170, 0]], ![![77919, -45243, -148703, 293073], ![56001, -214830, 110, 0]], ![![28323, -16447, -54060, 106544], ![20369, -78100, 40, 0]]]
  g := ![![![1, 0, 0, 0], ![-12, 13, 0, 0], ![-12, 0, 13, 0], ![-4, 0, 0, 13]], ![![1, -1, 0, 1], ![6, -3, -9, 18], ![0, -3, -3, 9], ![4, -4, -6, 13]]]
  hle1 := by decide
  hle2 := by decide

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def I13N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0], ![-4, -1, 0, 1]] i)))

def SI13N2: IdealEqSpanCertificate O ℤ timesTableO I13N2
 ![![13, 0, 0, 0], ![-4, -1, 0, 1]] 
 ![![13, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![9, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![13, 0, 0, 0], ![0, 13, 0, 0], ![0, 0, 13, 0], ![0, 0, 0, 13]], ![![-4, -1, 0, 1], ![6, -12, -9, 18], ![-36, -3, -12, 9], ![-16, -4, -6, 4]]]
  hmulB := by decide
  f := ![![![434453, -847241, -636948, 1271909], ![29341, -920348, 234, 0]], ![![83416, -162667, -122292, 244202], ![5641, -176704, 45, 0]], ![![-16682, 32536, 24460, -48844], ![-1121, 35343, -9, 0]], ![![300777, -586551, -440964, 880552], ![20319, -637164, 162, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 13, 0, 0], ![0, 0, 13, 0], ![-9, 0, 0, 13]], ![![-1, -1, 0, 1], ![-12, -12, -9, 18], ![-9, -3, -12, 9], ![-4, -4, -6, 4]]]
  hle1 := by decide
  hle2 := by decide

lemma NI13N2 : Nat.card (O ⧸ I13N2) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI13N2)

lemma isPrimeI13N2 : Ideal.IsPrime I13N2 := prime_ideal_of_norm_prime hp13.out _ NI13N2
def I13N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0], ![-1, -1, 0, 1]] i)))

def SI13N3: IdealEqSpanCertificate O ℤ timesTableO I13N3
 ![![13, 0, 0, 0], ![-1, -1, 0, 1]] 
 ![![13, 0, 0, 0], ![4, 1, 0, 0], ![10, 0, 1, 0], ![3, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![13, 0, 0, 0], ![0, 13, 0, 0], ![0, 0, 13, 0], ![0, 0, 0, 13]], ![![-1, -1, 0, 1], ![6, -9, -9, 18], ![-36, -3, -9, 9], ![-16, -4, -6, 7]]]
  hmulB := by decide
  f := ![![![12517, -17604, -17784, 35418], ![3120, -25818, 130, 0]], ![![9129, -12837, -12969, 25828], ![2285, -18828, 95, 0]], ![![9149, -12866, -12998, 25886], ![2287, -18870, 95, 0]], ![![2889, -4062, -4104, 8173], ![726, -5958, 30, 0]]]
  g := ![![![1, 0, 0, 0], ![-4, 13, 0, 0], ![-10, 0, 13, 0], ![-3, 0, 0, 13]], ![![0, -1, 0, 1], ![6, -9, -9, 18], ![3, -3, -9, 9], ![3, -4, -6, 7]]]
  hle1 := by decide
  hle2 := by decide

lemma NI13N3 : Nat.card (O ⧸ I13N3) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI13N3)

lemma isPrimeI13N3 : Ideal.IsPrime I13N3 := prime_ideal_of_norm_prime hp13.out _ NI13N3
def MulI13N0 : IdealMulEqCertificate O ℤ timesTableO (I13N0) I13N1
  ![![13, 0, 0, 0], ![8, -1, 0, 1]] ![![13, 0, 0, 0], ![5, -1, 0, 1]]
  ![![-3, -1, -1, 2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![169, 0, 0, 0], ![65, -13, 0, 13]], ![![104, -13, 0, 13], ![18, -9, 3, 3]]]
 hmul := by decide
 f :=  ![![![![-3833073060744, 2234302331906, 7339762455041, -14467212179917], ![-2758990755027, 10601998602190, -358499410, 0]], ![![741702, 0, 0, 0], ![28065, 85, 0, 0]]]]
 g :=  ![![![![-65, 13, 13, -26]], ![![-23, 7, 0, -4]]], ![![![-38, 10, 3, -10]], ![![-6, 3, -3, 3]]]]
 hle1 := by decide
 hle2 := by decide

def MulI13N1 : IdealMulEqCertificate O ℤ timesTableO (I13N0*I13N1) I13N2
  ![![-3, -1, -1, 2]] ![![13, 0, 0, 0], ![-4, -1, 0, 1]]
  ![![13, 0, 0, 0], ![-9, 4, 1, -1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI13N0
 hI2 := rfl
 M :=  ![![![-39, -13, -13, 26], ![10, 10, 9, -22]]]
 hmul := by decide
 f :=  ![![![![25318583, -49509379, -37241843, 74335296], ![1736185, -53776628, -12859, 0]]], ![![![-17755883, 34720857, 26117651, -52131237], ![-1217575, 37713472, 9018, 0]]]]
 g :=  ![![![![6, -5, -2, 3], ![13, 0, 0, 0]], ![![7, -2, 0, -1], ![9, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI13N2 : IdealMulEqCertificate O ℤ timesTableO (I13N0*I13N1*I13N2) I13N3
  ![![13, 0, 0, 0], ![-9, 4, 1, -1]] ![![13, 0, 0, 0], ![-1, -1, 0, 1]]
  ![![13, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI13N1
 hI2 := rfl
 M :=  ![![![169, 0, 0, 0], ![-13, -13, 0, 13]], ![![-117, 52, 13, -13], ![13, -26, -39, 65]]]
 hmul := by decide
 f :=  ![![![![-644961, 907058, 916308, -1824938], ![-160528, 1330302, -6740, 0]], ![![54, 0, 0, 0], ![0, 0, 0, 0]]]]
 g :=  ![![![![13, 0, 0, 0]], ![![-1, -1, 0, 1]]], ![![![-9, 4, 1, -1]], ![![1, -2, -3, 5]]]]
 hle1 := by decide
 hle2 := by decide

def PBC13 : PrimesBelowPCertificate 13 ![I13N0, I13N1, I13N2, I13N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
    exact isPrimeI13N2
    exact isPrimeI13N3
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI13N2, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}
def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0], ![-3, -5, -6, 12]] i)))

def SI17N0: IdealEqSpanCertificate O ℤ timesTableO I17N0
 ![![17, 0, 0, 0], ![-3, -5, -6, 12]] 
 ![![17, 0, 0, 0], ![0, 17, 0, 0], ![7, 16, 1, 0], ![16, 9, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![17, 0, 0, 0], ![0, 17, 0, 0], ![0, 0, 17, 0], ![0, 0, 0, 17]], ![![-3, -5, -6, 12], ![-24, -9, -5, 6], ![-44, 3, 23, -67], ![-30, 4, 16, -45]]]
  hmulB := by decide
  f := ![![![1774, 537, 192, -72], ![-561, 1326, 0, 0]], ![![-135, -38, -12, 0], ![51, -102, 0, 0]], ![![602, 183, 65, -24], ![-191, 450, 0, 0]], ![![1595, 480, 168, -55], ![-519, 1194, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-7, -16, 17, 0], ![-16, -9, 0, 17]], ![![-9, -1, -6, 12], ![-5, 1, -5, 6], ![51, 14, 23, -67], ![34, 9, 16, -45]]]
  hle1 := by decide
  hle2 := by decide

lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI17N0)

def MemCI17N0 : IdealMemCertificate O ℤ B I17N0
  ![![17, 0, 0, 0], ![0, 17, 0, 0], ![7, 16, 1, 0], ![16, 9, 0, 1]] ![-4126, -856, -168, -620] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI17N0
 g := ![410, 436, -168, -620]
 hmem := by decide

def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [5, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 16], [0, 1]]
 g := ![![[16, 1], [15], [8], [1]],![[4, 16], [15], [8], [1]]]
 h' := ![![[5, 16], [14, 1], [2, 7], [12, 5], [0, 1]],![[0, 1], [2, 16], [3, 10], [3, 12], [5, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [1, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : PrimeIdeal O 17 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I17N0
  hcard := NI17N0
  P := [5, 12, 1]
  f := ofList [5, 12, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P17P0
  hneq := by decide
  hlen := by decide
  c := ![-4126, -856, -168, -620]
  a := ![-23, 20, 18, -50]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI17N0
  hpmem := by 
    show  _ ∈ I17N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI17N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := PrimeIdeal_isPrime PI17N0
def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0], ![-13, 5, 4, -8]] i)))

def SI17N1: IdealEqSpanCertificate O ℤ timesTableO I17N1
 ![![17, 0, 0, 0], ![-13, 5, 4, -8]] 
 ![![17, 0, 0, 0], ![0, 17, 0, 0], ![16, 16, 1, 0], ![16, 1, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![17, 0, 0, 0], ![0, 17, 0, 0], ![0, 0, 17, 0], ![0, 0, 0, 17]], ![![-13, 5, 4, -8], ![16, -9, 5, -4], ![56, -27, -57, 103], ![30, -16, -24, 45]]]
  hmulB := by decide
  f := ![![![1114, -707, 630, -672], ![-595, -1666, 0, 0]], ![![-73, 49, -47, 52], ![51, 119, 0, 0]], ![![979, -619, 549, -584], ![-513, -1456, 0, 0]], ![![1048, -664, 589, -627], ![-552, -1561, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-16, -16, 17, 0], ![-16, -1, 0, 17]], ![![3, -3, 4, -8], ![0, -5, 5, -4], ![-40, 46, -57, 103], ![-18, 19, -24, 45]]]
  hle1 := by decide
  hle2 := by decide

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 289 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI17N1)

def MemCI17N1 : IdealMemCertificate O ℤ B I17N1
  ![![17, 0, 0, 0], ![0, 17, 0, 0], ![16, 16, 1, 0], ![16, 1, 0, 1]] ![9275, 3444, 8830, -24820] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI17N1
 g := ![15595, -6648, 8830, -24820]
 hmem := by decide

def P17P1 : CertificateIrreducibleZModOfList' 17 2 2 4 [15, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 16], [0, 1]]
 g := ![![[14, 8], [4], [2], [1]],![[0, 9], [4], [2], [1]]]
 h' := ![![[11, 16], [4, 12], [8, 15], [2, 11], [0, 1]],![[0, 1], [0, 5], [3, 2], [4, 6], [11, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [13, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N1 : PrimeIdeal O 17 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I17N1
  hcard := NI17N1
  P := [15, 6, 1]
  f := ofList [15, 6, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P17P1
  hneq := by decide
  hlen := by decide
  c := ![9275, 3444, 8830, -24820]
  a := ![-126, 117, 129, -275]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI17N1
  hpmem := by 
    show  _ ∈ I17N1.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI17N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := PrimeIdeal_isPrime PI17N1
def MulI17N0 : IdealMulEqCertificate O ℤ timesTableO (I17N0) I17N1
  ![![17, 0, 0, 0], ![-3, -5, -6, 12]] ![![17, 0, 0, 0], ![-13, 5, 4, -8]]
  ![![17, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![289, 0, 0, 0], ![-221, 85, 68, -136]], ![![-51, -85, -102, 204], ![-17, 0, 17, -34]]]
 hmul := by decide
 f :=  ![![![![1530910111, -968504112, 867482530, -927794312], ![-814827482, -2286983706, 0, 0]], ![![8828992, 120, 0, 0], ![0, 0, 0, 0]]]]
 g :=  ![![![![17, 0, 0, 0]], ![![-13, 5, 4, -8]]], ![![![-3, -5, -6, 12]], ![![-1, 0, 1, -2]]]]
 hle1 := by decide
 hle2 := by decide

def PBC17 : PrimesBelowPCertificate 17 ![I17N0, I17N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI17N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}
def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0, 0], ![-4, -5, -6, 12]] i)))

def SI19N0: IdealEqSpanCertificate O ℤ timesTableO I19N0
 ![![19, 0, 0, 0], ![-4, -5, -6, 12]] 
 ![![19, 0, 0, 0], ![0, 19, 0, 0], ![11, 18, 1, 0], ![2, 7, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![19, 0, 0, 0], ![0, 19, 0, 0], ![0, 0, 19, 0], ![0, 0, 0, 19]], ![![-4, -5, -6, 12], ![-24, -10, -5, 6], ![-44, 3, 22, -67], ![-30, 4, 16, -46]]]
  hmulB := by decide
  f := ![![![2409, 850, 264, -96], ![-874, 2052, 0, 0]], ![![-400, -139, -42, 12], ![152, -342, 0, 0]], ![![1017, 362, 115, -48], ![-356, 864, 0, 0]], ![![106, 38, 12, -5], ![-37, 90, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-11, -18, 19, 0], ![-2, -7, 0, 19]], ![![2, 1, -6, 12], ![1, 2, -5, 6], ![-8, 4, 22, -67], ![-6, 2, 16, -46]]]
  hle1 := by decide
  hle2 := by decide

lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI19N0)

def MemCI19N0 : IdealMemCertificate O ℤ B I19N0
  ![![19, 0, 0, 0], ![0, 19, 0, 0], ![11, 18, 1, 0], ![2, 7, 0, 1]] ![-886, -114, -104, 53] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI19N0
 g := ![8, 73, -104, 53]
 hmem := by decide

def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [16, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 18], [0, 1]]
 g := ![![[6, 6], [11, 11], [1], [1]],![[0, 13], [0, 8], [1], [1]]]
 h' := ![![[18, 18], [14, 14], [12, 12], [3, 18], [0, 1]],![[0, 1], [0, 5], [0, 7], [4, 1], [18, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [16, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : PrimeIdeal O 19 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I19N0
  hcard := NI19N0
  P := [16, 1, 1]
  f := ofList [16, 1, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P19P0
  hneq := by decide
  hlen := by decide
  c := ![-886, -114, -104, 53]
  a := ![-5, 6, 2, -11]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI19N0
  hpmem := by 
    show  _ ∈ I19N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI19N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := PrimeIdeal_isPrime PI19N0
def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0, 0], ![-14, 5, 4, -8]] i)))

def SI19N1: IdealEqSpanCertificate O ℤ timesTableO I19N1
 ![![19, 0, 0, 0], ![-14, 5, 4, -8]] 
 ![![19, 0, 0, 0], ![0, 19, 0, 0], ![14, 18, 1, 0], ![4, 6, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![19, 0, 0, 0], ![0, 19, 0, 0], ![0, 0, 19, 0], ![0, 0, 0, 19]], ![![-14, 5, 4, -8], ![16, -10, 5, -4], ![56, -27, -58, 103], ![30, -16, -24, 44]]]
  hmulB := by decide
  f := ![![![101, -70, 48, -48], ![-38, -152, 0, 0]], ![![-86, 66, -52, 56], ![57, 152, 0, 0]], ![![-10, 12, -13, 16], ![22, 32, 0, 0]], ![![0, 4, -8, 11], ![18, 16, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-14, -18, 19, 0], ![-4, -6, 0, 19]], ![![-2, -1, 4, -8], ![-2, -4, 5, -4], ![24, 21, -58, 103], ![10, 8, -24, 44]]]
  hle1 := by decide
  hle2 := by decide

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 361 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI19N1)

def MemCI19N1 : IdealMemCertificate O ℤ B I19N1
  ![![19, 0, 0, 0], ![0, 19, 0, 0], ![14, 18, 1, 0], ![4, 6, 0, 1]] ![-2416, -432, 0, -509] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI19N1
 g := ![-20, 138, 0, -509]
 hmem := by decide

def P19P1 : CertificateIrreducibleZModOfList' 19 2 2 4 [18, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 18], [0, 1]]
 g := ![![[16, 11], [6, 6], [9], [1]],![[2, 8], [7, 13], [9], [1]]]
 h' := ![![[16, 18], [6, 12], [10, 5], [1, 16], [0, 1]],![[0, 1], [8, 7], [14, 14], [10, 3], [16, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [10, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N1 : PrimeIdeal O 19 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I19N1
  hcard := NI19N1
  P := [18, 3, 1]
  f := ofList [18, 3, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P19P1
  hneq := by decide
  hlen := by decide
  c := ![-2416, -432, 0, -509]
  a := ![-17, 16, 13, -37]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI19N1
  hpmem := by 
    show  _ ∈ I19N1.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI19N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := PrimeIdeal_isPrime PI19N1
def MulI19N0 : IdealMulEqCertificate O ℤ timesTableO (I19N0) I19N1
  ![![19, 0, 0, 0], ![-4, -5, -6, 12]] ![![19, 0, 0, 0], ![-14, 5, 4, -8]]
  ![![19, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![361, 0, 0, 0], ![-266, 95, 76, -152]], ![![-76, -95, -114, 228], ![0, 0, 19, -38]]]
 hmul := by decide
 f :=  ![![![![-41209917, 34592750, -22055981, 20707910], ![26106096, 74115464, 0, 0]], ![![9319720, 3949, 0, 0], ![0, 0, 0, 0]]]]
 g :=  ![![![![19, 0, 0, 0]], ![![-14, 5, 4, -8]]], ![![![-4, -5, -6, 12]], ![![0, 0, 1, -2]]]]
 hle1 := by decide
 hle2 := by decide

def PBC19 : PrimesBelowPCertificate 19 ![I19N0, I19N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI19N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0], ![10, -1, 0, 1]] i)))

def SI23N0: IdealEqSpanCertificate O ℤ timesTableO I23N0
 ![![23, 0, 0, 0], ![10, -1, 0, 1]] 
 ![![23, 0, 0, 0], ![18, 1, 0, 0], ![21, 0, 1, 0], ![5, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![23, 0, 0, 0], ![0, 23, 0, 0], ![0, 0, 23, 0], ![0, 0, 0, 23]], ![![10, -1, 0, 1], ![6, 2, -9, 18], ![-36, -3, 2, 9], ![-16, -4, -6, 18]]]
  hmulB := by decide
  f := ![![![1211117, 535122, -2270744, 4510558], ![699430, -5802808, 920, 0]], ![![989926, 437390, -1856027, 3686773], ![571687, -4743013, 752, 0]], ![![1103173, 487427, -2068355, 4108537], ![637087, -5285610, 838, 0]], ![![263285, 116331, -493640, 980556], ![152053, -1261480, 200, 0]]]
  g := ![![![1, 0, 0, 0], ![-18, 23, 0, 0], ![-21, 0, 23, 0], ![-5, 0, 0, 23]], ![![1, -1, 0, 1], ![3, 2, -9, 18], ![-3, -3, 2, 9], ![4, -4, -6, 18]]]
  hle1 := by decide
  hle2 := by decide

lemma NI23N0 : Nat.card (O ⧸ I23N0) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI23N0)

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := prime_ideal_of_norm_prime hp23.out _ NI23N0
def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0], ![-6, -1, 0, 1]] i)))

def SI23N1: IdealEqSpanCertificate O ℤ timesTableO I23N1
 ![![23, 0, 0, 0], ![-6, -1, 0, 1]] 
 ![![23, 0, 0, 0], ![4, 1, 0, 0], ![7, 0, 1, 0], ![21, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![23, 0, 0, 0], ![0, 23, 0, 0], ![0, 0, 23, 0], ![0, 0, 0, 23]], ![![-6, -1, 0, 1], ![6, -14, -9, 18], ![-36, -3, -14, 9], ![-16, -4, -6, 2]]]
  hmulB := by decide
  f := ![![![490381, -1137266, -728364, 1461026], ![-14950, -1868244, 4416, 0]], ![![110600, -256492, -164271, 329511], ![-3363, -421353, 996, 0]], ![![147917, -343034, -219697, 440690], ![-4498, -563520, 1332, 0]], ![![447741, -1038373, -665028, 1333980], ![-13643, -1705788, 4032, 0]]]
  g := ![![![1, 0, 0, 0], ![-4, 23, 0, 0], ![-7, 0, 23, 0], ![-21, 0, 0, 23]], ![![-1, -1, 0, 1], ![-11, -14, -9, 18], ![-5, -3, -14, 9], ![0, -4, -6, 2]]]
  hle1 := by decide
  hle2 := by decide

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulEqCertificate O ℤ timesTableO (I23N0) I23N0
  ![![23, 0, 0, 0], ![10, -1, 0, 1]] ![![23, 0, 0, 0], ![10, -1, 0, 1]]
  ![![5, -3, -3, 6]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![529, 0, 0, 0], ![230, -23, 0, 23]], ![![230, -23, 0, 23], ![78, -16, 3, 10]]]
 hmul := by decide
 f :=  ![![![![220879415452571, 97593246266288, -414129056451271, 822617366095501], ![127557316276311, -1058292550311095, 167760710332, 0]], ![![0, 0, 0, 0], ![-1479627565, -2739820, 42, 0]]]]
 g :=  ![![![![23, -69, -69, 138]], ![![4, -22, -15, 28]]], ![![![4, -22, -15, 28]], ![![0, -5, 0, -1]]]]
 hle1 := by decide
 hle2 := by decide

def MulI23N1 : IdealMulEqCertificate O ℤ timesTableO (I23N0*I23N0) I23N1
  ![![5, -3, -3, 6]] ![![23, 0, 0, 0], ![-6, -1, 0, 1]]
  ![![23, 0, 0, 0], ![5, -12, -18, 37]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI23N0
 hI2 := rfl
 M :=  ![![![115, -69, -69, 138], ![-36, 22, 33, -64]]]
 hmul := by decide
 f :=  ![![![![2483401193, -5838935738, -3751744725, 7506377231], ![-67612771, -9587694336, -62832, 0]]], ![![![250429139, -588805241, -378330411, 756952029], ![-6818146, -966834528, -6336, 0]]]]
 g :=  ![![![![0, 9, 15, -31], ![23, 0, 0, 0]], ![![-2, 2, 3, -6], ![2, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI23N2 : IdealMulEqCertificate O ℤ timesTableO (I23N0*I23N0*I23N1) I23N1
  ![![23, 0, 0, 0], ![5, -12, -18, 37]] ![![23, 0, 0, 0], ![-6, -1, 0, 1]]
  ![![23, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI23N1
 hI2 := rfl
 M :=  ![![![529, 0, 0, 0], ![-138, -23, 0, 23]], ![![115, -276, -414, 851], ![-46, 69, 138, -299]]]
 hmul := by decide
 f :=  ![![![![6251424087, -14498021788, -9285275724, 18625353180], ![-190659524, -23816626596, 56304528, 0]], ![![0, 0, 0, 0], ![-5720, 0, 0, 0]]]]
 g :=  ![![![![23, 0, 0, 0]], ![![-6, -1, 0, 1]]], ![![![5, -12, -18, 37]], ![![-2, 3, 6, -13]]]]
 hle1 := by decide
 hle2 := by decide

def PBC23 : PrimesBelowPCertificate 23 ![I23N0, I23N0, I23N1, I23N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N0
    exact isPrimeI23N1
    exact isPrimeI23N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI23N2, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}
def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0, 0], ![11, 0, -1, 2]] i)))

def SI29N0: IdealEqSpanCertificate O ℤ timesTableO I29N0
 ![![29, 0, 0, 0], ![11, 0, -1, 2]] 
 ![![29, 0, 0, 0], ![0, 29, 0, 0], ![10, 20, 1, 0], ![25, 10, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![29, 0, 0, 0], ![0, 29, 0, 0], ![0, 0, 29, 0], ![0, 0, 0, 29]], ![![11, 0, -1, 2], ![-4, 10, 0, 1], ![6, -12, 2, 18], ![0, -6, -4, 19]]]
  hmulB := by decide
  f := ![![![-10, 0, 1, -2], ![29, 0, 0, 0]], ![![1, -29, 1, -5], ![29, 87, 0, 0]], ![![-2, -20, 1, -4], ![28, 60, 0, 0]], ![![-6, -10, 1, -3], ![29, 30, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-10, -20, 29, 0], ![-25, -10, 0, 29]], ![![-1, 0, -1, 2], ![-1, 0, 0, 1], ![-16, -8, 2, 18], ![-15, -4, -4, 19]]]
  hle1 := by decide
  hle2 := by decide

lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI29N0)

def MemCI29N0 : IdealMemCertificate O ℤ B I29N0
  ![![29, 0, 0, 0], ![0, 29, 0, 0], ![10, 20, 1, 0], ![25, 10, 0, 1]] ![3537, -1314, -4464, 8814] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI29N0
 g := ![-5937, -6, -4464, 8814]
 hmem := by decide

def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [21, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [20, 28], [0, 1]]
 g := ![![[17, 7], [28], [24, 4], [20, 1]],![[12, 22], [28], [17, 25], [11, 28]]]
 h' := ![![[20, 28], [26, 6], [18, 12], [15, 2], [0, 1]],![[0, 1], [1, 23], [26, 17], [26, 27], [20, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [3, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : PrimeIdeal O 29 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I29N0
  hcard := NI29N0
  P := [21, 9, 1]
  f := ofList [21, 9, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P29P0
  hneq := by decide
  hlen := by decide
  c := ![3537, -1314, -4464, 8814]
  a := ![-31, 30, 41, -68]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI29N0
  hpmem := by 
    show  _ ∈ I29N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI29N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := PrimeIdeal_isPrime PI29N0
def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0, 0], ![-10, 0, -1, 2]] i)))

def SI29N1: IdealEqSpanCertificate O ℤ timesTableO I29N1
 ![![29, 0, 0, 0], ![-10, 0, -1, 2]] 
 ![![29, 0, 0, 0], ![0, 29, 0, 0], ![2, 7, 1, 0], ![25, 18, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![29, 0, 0, 0], ![0, 29, 0, 0], ![0, 0, 29, 0], ![0, 0, 0, 29]], ![![-10, 0, -1, 2], ![-4, -11, 0, 1], ![6, -12, -19, 18], ![0, -6, -4, -2]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0], ![0, 0, 0, 0]], ![![-22, -87, 1, 6], ![29, -232, 0, 0]], ![![2, -21, 1, 0], ![28, -56, 0, 0]], ![![-9, -54, 1, 3], ![29, -144, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-2, -7, 29, 0], ![-25, -18, 0, 29]], ![![-2, -1, -1, 2], ![-1, -1, 0, 1], ![-14, -7, -19, 18], ![2, 2, -4, -2]]]
  hle1 := by decide
  hle2 := by decide

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 841 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI29N1)

def MemCI29N1 : IdealMemCertificate O ℤ B I29N1
  ![![29, 0, 0, 0], ![0, 29, 0, 0], ![2, 7, 1, 0], ![25, 18, 0, 1]] ![377, 216, 260, -595] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI29N1
 g := ![508, 314, 260, -595]
 hmem := by decide

def P29P1 : CertificateIrreducibleZModOfList' 29 2 2 4 [25, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [20, 28], [0, 1]]
 g := ![![[5, 7], [6], [21, 4], [20, 1]],![[0, 22], [6], [14, 25], [11, 28]]]
 h' := ![![[20, 28], [4, 23], [26, 21], [22, 27], [0, 1]],![[0, 1], [0, 6], [11, 8], [11, 2], [20, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [2, 23]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N1 : PrimeIdeal O 29 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I29N1
  hcard := NI29N1
  P := [25, 9, 1]
  f := ofList [25, 9, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P29P1
  hneq := by decide
  hlen := by decide
  c := ![377, 216, 260, -595]
  a := ![-16, 16, 17, -35]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI29N1
  hpmem := by 
    show  _ ∈ I29N1.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI29N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := PrimeIdeal_isPrime PI29N1
def MulI29N0 : IdealMulEqCertificate O ℤ timesTableO (I29N0) I29N1
  ![![29, 0, 0, 0], ![11, 0, -1, 2]] ![![29, 0, 0, 0], ![-10, 0, -1, 2]]
  ![![29, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![841, 0, 0, 0], ![-290, 0, -29, 58]], ![![319, 0, -29, 58], ![-116, 0, 0, 0]]]
 hmul := by decide
 f :=  ![![![![864, 0, -95, 190], ![-250, 0, 0, 0]], ![![-2505, 0, 0, 0], ![0, 0, 0, 0]]]]
 g :=  ![![![![29, 0, 0, 0]], ![![-10, 0, -1, 2]]], ![![![11, 0, -1, 2]], ![![-4, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def PBC29 : PrimesBelowPCertificate 29 ![I29N0, I29N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI29N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
