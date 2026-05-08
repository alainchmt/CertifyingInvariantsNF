
import IdealArithmetic.Examples.NF3_1_24843_1.RI3_1_24843_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic

set_option linter.all false

open Classical Polynomial

noncomputable section 
instance hp2 : Fact (Nat.Prime 2) := {out := by norm_num}
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 0, 1]] i)))

def SI2N0: IdealEqSpanCertificate timesTableO I2N0
 ![![2, 0, 0], ![0, 0, 1]] 
 ![![2, 0, 0], ![0, 2, 0], ![0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![0, 0, 1], ![30, 0, 1], ![20, 10, 1]]]
  hmulB := by decide
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 2]], ![![0, 0, 1], ![15, 0, 1], ![10, 5, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 4 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI2N0)

def MemCI2N0 : IdealMemCertificate B I2N0
  ![![2, 0, 0], ![0, 2, 0], ![0, 0, 1]] ![-1138, 640, 19] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI2N0
 g := ![-569, 320, 19]
 hmem := by decide

def P2P0 : CertificateIrreducibleZModOfList' 2 2 2 1 [1, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 1], [0, 1]]
 g := ![![[1]],![[1]]]
 h' := ![![[1, 1], [0, 1]],![[0, 1], [1, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], []]
 b := ![[], [1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI2N0 : CertifiedPrimeIdeal O 2 where 
  r := 3
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I2N0
  hcard := NI2N0
  P := [1, 1, 1]
  f := ofList [1, 1, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P2P0
  hneq := by decide
  hlen := by decide
  c := ![-1138, 640, 19]
  a := ![-3, -5, 8]
  z := ![1, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI2N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI2N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := CertifiedPrimeIdeal.isPrime PI2N0
def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![1, 1, 0]] i)))

def SI2N1: IdealEqSpanCertificate timesTableO I2N1
 ![![2, 0, 0], ![1, 1, 0]] 
 ![![2, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![1, 1, 0], ![-1, 0, 3], ![30, 0, 2]]]
  hmulB := by decide
  f := ![![![0, -1, 0], ![2, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 2], ![0, -1, 0]]]
  g := ![![![1, 0, 0], ![-1, 2, 0], ![-1, 0, 2]], ![![0, 1, 0], ![-2, 0, 3], ![14, 0, 2]]]
  hle1 := by decide
  hle2 := by decide

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulEqCertificate timesTableO (I2N0) I2N1
  ![![2, 0, 0], ![0, 0, 1]] ![![2, 0, 0], ![1, 1, 0]]
  ![![2, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![4, 0, 0], ![2, 2, 0]], ![![0, 0, 2], ![30, 0, 2]]]
 hmul := by decide
 f :=  ![![![![0, 0, 2], ![0, -1, 0]], ![![-1, 0, 0], ![0, 0, 0]]]]
 g :=  ![![![![2, 0, 0]], ![![1, 1, 0]]], ![![![0, 0, 1]], ![![15, 0, 1]]]]
 hle1 := by decide
 hle2 := by decide

def PBC2 : IsPrimesAboveP 2 ![I2N0, I2N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI2N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![0, 0, 1]] i)))

def SI3N0: IdealEqSpanCertificate timesTableO I3N0
 ![![3, 0, 0], ![0, 0, 1]] 
 ![![3, 0, 0], ![2, 1, 0], ![0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![0, 0, 1], ![30, 0, 1], ![20, 10, 1]]]
  hmulB := by decide
  f := ![![![-9, 10, 0], ![0, 3, -3]], ![![-6, 7, 0], ![0, 2, -2]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![-2, 3, 0], ![0, 0, 3]], ![![0, 0, 1], ![10, 0, 1], ![0, 10, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0
def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-1, 0, 1]] i)))

def SI3N1: IdealEqSpanCertificate timesTableO I3N1
 ![![3, 0, 0], ![-1, 0, 1]] 
 ![![3, 0, 0], ![2, 1, 0], ![2, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![-1, 0, 1], ![30, -1, 1], ![20, 10, 0]]]
  hmulB := by decide
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![10, 0, 1], ![-2, -1, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![-2, 3, 0], ![-2, 0, 3]], ![![-1, 0, 1], ![10, -1, 1], ![0, 10, 0]]]
  hle1 := by decide
  hle2 := by decide

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulEqCertificate timesTableO (I3N0) I3N0
  ![![3, 0, 0], ![0, 0, 1]] ![![3, 0, 0], ![0, 0, 1]]
  ![![3, 0, 0], ![-1, 1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![9, 0, 0], ![0, 0, 3]], ![![0, 0, 3], ![20, 10, 1]]]
 hmul := by decide
 f :=  ![![![![377, 39190, 7084], ![-17262, 7817, -11221]], ![![0, 0, 0], ![-1603, 0, -5]]], ![![![-159, -15671, -2834], ![6906, -3125, 4487]], ![![0, 0, 0], ![641, 0, 2]]]]
 g :=  ![![![![3, 0, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0]]], ![![![0, 0, 1], ![0, 0, 0]], ![![7, 3, 0], ![1, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI3N1 : IdealMulEqCertificate timesTableO (I3N0*I3N0) I3N1
  ![![3, 0, 0], ![-1, 1, 1]] ![![3, 0, 0], ![-1, 0, 1]]
  ![![3, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI3N0
 hI2 := rfl
 M :=  ![![![9, 0, 0], ![-3, 0, 3]], ![![-3, 3, 3], ![51, 9, 0]]]
 hmul := by decide
 f :=  ![![![![18, 0, 3], ![-5, -2, 0]], ![![-2, 0, 0], ![0, 0, 0]]]]
 g :=  ![![![![3, 0, 0]], ![![-1, 0, 1]]], ![![![-1, 1, 1]], ![![17, 3, 0]]]]
 hle1 := by decide
 hle2 := by decide

def PBC3 : IsPrimesAboveP 3 ![I3N0, I3N0, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI3N1, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp5 : Fact (Nat.Prime 5) := {out := by norm_num}
def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![0, 0, 1]] i)))

def SI5N0: IdealEqSpanCertificate timesTableO I5N0
 ![![5, 0, 0], ![0, 0, 1]] 
 ![![5, 0, 0], ![0, 5, 0], ![0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![0, 0, 1], ![30, 0, 1], ![20, 10, 1]]]
  hmulB := by decide
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 5]], ![![0, 0, 1], ![6, 0, 1], ![4, 2, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 25 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI5N0)

def MemCI5N0 : IdealMemCertificate B I5N0
  ![![5, 0, 0], ![0, 5, 0], ![0, 0, 1]] ![81740, 44890, 4099] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI5N0
 g := ![16348, 8978, 4099]
 hmem := by decide

def P5P0 : CertificateIrreducibleZModOfList' 5 2 2 2 [3, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 4], [0, 1]]
 g := ![![[], [1]],![[], [1]]]
 h' := ![![[0, 4], [2], [0, 1]],![[0, 1], [2], [0, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [0, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal O 5 where 
  r := 3
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I5N0
  hcard := NI5N0
  P := [3, 0, 1]
  f := ofList [3, 0, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P5P0
  hneq := by decide
  hlen := by decide
  c := ![81740, 44890, 4099]
  a := ![1, 2, -67]
  z := ![1, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI5N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI5N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := CertifiedPrimeIdeal.isPrime PI5N0
def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-1, 1, 0]] i)))

def SI5N1: IdealEqSpanCertificate timesTableO I5N1
 ![![5, 0, 0], ![-1, 1, 0]] 
 ![![5, 0, 0], ![4, 1, 0], ![4, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![-1, 1, 0], ![-1, -2, 3], ![30, 0, 0]]]
  hmulB := by decide
  f := ![![![-11, -24, 36], ![0, -60, 0]], ![![-8, -18, 27], ![1, -45, 0]], ![![-9, -19, 29], ![-1, -48, 0]]]
  g := ![![![1, 0, 0], ![-4, 5, 0], ![-4, 0, 5]], ![![-1, 1, 0], ![-1, -2, 3], ![6, 0, 0]]]
  hle1 := by decide
  hle2 := by decide

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1
def MulI5N0 : IdealMulEqCertificate timesTableO (I5N0) I5N1
  ![![5, 0, 0], ![0, 0, 1]] ![![5, 0, 0], ![-1, 1, 0]]
  ![![5, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![25, 0, 0], ![-5, 5, 0]], ![![0, 0, 5], ![30, 0, 0]]]
 hmul := by decide
 f :=  ![![![![-18, -37, 56], ![1, -92, 0]], ![![-4, 0, 0], ![0, 0, 0]]]]
 g :=  ![![![![5, 0, 0]], ![![-1, 1, 0]]], ![![![0, 0, 1]], ![![6, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def PBC5 : IsPrimesAboveP 5 ![I5N0, I5N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI5N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![0, 1, 0]] i)))

def SI7N0: IdealEqSpanCertificate timesTableO I7N0
 ![![7, 0, 0], ![0, 1, 0]] 
 ![![7, 0, 0], ![0, 1, 0], ![2, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![0, 1, 0], ![-1, -1, 3], ![30, 0, 1]]]
  hmulB := by decide
  f := ![![![0, -1, 3], ![0, -7, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 1], ![-2, -2, 0]]]
  g := ![![![1, 0, 0], ![0, 7, 0], ![-2, 0, 7]], ![![0, 1, 0], ![-1, -1, 3], ![4, 0, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI7N0)

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := prime_ideal_of_norm_prime hp7.out _ NI7N0
def MulI7N0 : IdealMulEqCertificate timesTableO (I7N0) I7N0
  ![![7, 0, 0], ![0, 1, 0]] ![![7, 0, 0], ![0, 1, 0]]
  ![![7, 0, 0], ![2, 2, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![49, 0, 0], ![0, 7, 0]], ![![0, 7, 0], ![-1, -1, 3]]]
 hmul := by decide
 f :=  ![![![![0, -168, 513], ![-21, 0, 0]], ![![0, 0, 0], ![-8379, -92, 0]]], ![![![0, -48, 145], ![-2, 0, 0]], ![![0, 0, 0], ![-2368, -26, 0]]]]
 g :=  ![![![![5, -2, -1], ![7, 0, 0]], ![![0, 1, 0], ![0, 0, 0]]], ![![![0, 1, 0], ![0, 0, 0]], ![![-1, -1, 0], ![3, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI7N1 : IdealMulEqCertificate timesTableO (I7N0*I7N0) I7N0
  ![![7, 0, 0], ![2, 2, 1]] ![![7, 0, 0], ![0, 1, 0]]
  ![![7, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI7N0
 hI2 := rfl
 M :=  ![![![49, 0, 0], ![0, 7, 0]], ![![14, 14, 7], ![28, 0, 7]]]
 hmul := by decide
 f :=  ![![![![0, -108, 357], ![-13, -769, 0]], ![![0, 0, 0], ![-192, 0, 0]]]]
 g :=  ![![![![7, 0, 0]], ![![0, 1, 0]]], ![![![2, 2, 1]], ![![4, 0, 1]]]]
 hle1 := by decide
 hle2 := by decide

def PBC7 : IsPrimesAboveP 7 ![I7N0, I7N0, I7N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N0
    exact isPrimeI7N0
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI7N1, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}
def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![1, -1, 1]] i)))

def SI11N0: IdealEqSpanCertificate timesTableO I11N0
 ![![11, 0, 0], ![1, -1, 1]] 
 ![![11, 0, 0], ![0, 11, 0], ![1, 10, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![1, -1, 1], ![31, 2, -2], ![-10, 10, 1]]]
  hmulB := by decide
  f := ![![![0, 1, -1], ![11, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-1, -10, 11]], ![![0, -1, 1], ![3, 2, -2], ![-1, 0, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI11N0)

def MemCI11N0 : IdealMemCertificate B I11N0
  ![![11, 0, 0], ![0, 11, 0], ![1, 10, 1]] ![-614, 680, -64] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI11N0
 g := ![-50, 120, -64]
 hmem := by decide

def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [9, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 10], [0, 1]]
 g := ![![[7, 5], [6, 9], [1]],![[0, 6], [0, 2], [1]]]
 h' := ![![[3, 10], [1, 7], [2, 3], [0, 1]],![[0, 1], [0, 4], [0, 8], [3, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [6, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal O 11 where 
  r := 3
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I11N0
  hcard := NI11N0
  P := [9, 8, 1]
  f := ofList [9, 8, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P11P0
  hneq := by decide
  hlen := by decide
  c := ![-614, 680, -64]
  a := ![3, 4, -8]
  z := ![1, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI11N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI11N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal.isPrime PI11N0
def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![2, 1, 0]] i)))

def SI11N1: IdealEqSpanCertificate timesTableO I11N1
 ![![11, 0, 0], ![2, 1, 0]] 
 ![![11, 0, 0], ![2, 1, 0], ![10, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![2, 1, 0], ![-1, 1, 3], ![30, 0, 3]]]
  hmulB := by decide
  f := ![![![-47, 48, 144], ![0, -528, 0]], ![![-8, 8, 24], ![1, -88, 0]], ![![-44, 43, 131], ![7, -480, 0]]]
  g := ![![![1, 0, 0], ![-2, 11, 0], ![-10, 0, 11]], ![![0, 1, 0], ![-3, 1, 3], ![0, 0, 3]]]
  hle1 := by decide
  hle2 := by decide

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulEqCertificate timesTableO (I11N0) I11N1
  ![![11, 0, 0], ![1, -1, 1]] ![![11, 0, 0], ![2, 1, 0]]
  ![![11, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![121, 0, 0], ![22, 11, 0]], ![![11, -11, 11], ![33, 0, 0]]]
 hmul := by decide
 f :=  ![![![![87031, -89138, -265736], ![7726, 973972, 0]], ![![1180, 0, 0], ![0, 0, 0]]]]
 g :=  ![![![![11, 0, 0]], ![![2, 1, 0]]], ![![![1, -1, 1]], ![![3, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def PBC11 : IsPrimesAboveP 11 ![I11N0, I11N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
    exact isPrimeI11N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI11N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![0, 1, 0]] i)))

def SI13N0: IdealEqSpanCertificate timesTableO I13N0
 ![![13, 0, 0], ![0, 1, 0]] 
 ![![13, 0, 0], ![0, 1, 0], ![4, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![0, 1, 0], ![-1, -1, 3], ![30, 0, 1]]]
  hmulB := by decide
  f := ![![![0, -1, 3], ![0, -13, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 1], ![-4, -4, 0]]]
  g := ![![![1, 0, 0], ![0, 13, 0], ![-4, 0, 13]], ![![0, 1, 0], ![-1, -1, 3], ![2, 0, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI13N0 : Nat.card (O ⧸ I13N0) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI13N0)

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := prime_ideal_of_norm_prime hp13.out _ NI13N0
def MulI13N0 : IdealMulEqCertificate timesTableO (I13N0) I13N0
  ![![13, 0, 0], ![0, 1, 0]] ![![13, 0, 0], ![0, 1, 0]]
  ![![13, 0, 0], ![4, 4, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![169, 0, 0], ![0, 13, 0]], ![![0, 13, 0], ![-1, -1, 3]]]
 hmul := by decide
 f :=  ![![![![0, -445, 1341], ![-26, 0, 0]], ![![0, 0, 0], ![-75543, -830, 0]]], ![![![0, -137, 412], ![-4, 0, 0]], ![![0, 0, 0], ![-23209, -255, 0]]]]
 g :=  ![![![![9, -4, -1], ![13, 0, 0]], ![![0, 1, 0], ![0, 0, 0]]], ![![![0, 1, 0], ![0, 0, 0]], ![![-1, -1, 0], ![3, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI13N1 : IdealMulEqCertificate timesTableO (I13N0*I13N0) I13N0
  ![![13, 0, 0], ![4, 4, 1]] ![![13, 0, 0], ![0, 1, 0]]
  ![![13, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI13N0
 hI2 := rfl
 M :=  ![![![169, 0, 0], ![0, 13, 0]], ![![52, 52, 13], ![26, 0, 13]]]
 hmul := by decide
 f :=  ![![![![0, -4, 11], ![11, -41, 0]], ![![0, 0, 0], ![-20, 0, 0]]]]
 g :=  ![![![![13, 0, 0]], ![![0, 1, 0]]], ![![![4, 4, 1]], ![![2, 0, 1]]]]
 hle1 := by decide
 hle2 := by decide

def PBC13 : IsPrimesAboveP 13 ![I13N0, I13N0, I13N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N0
    exact isPrimeI13N0
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI13N1, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}
def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![8, 7, 1]] i)))

def SI17N0: IdealEqSpanCertificate timesTableO I17N0
 ![![17, 0, 0], ![8, 7, 1]] 
 ![![17, 0, 0], ![0, 17, 0], ![8, 7, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![8, 7, 1], ![23, 1, 22], ![230, 10, 16]]]
  hmulB := by decide
  f := ![![![-7, -7, -1], ![17, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-8, -7, 17]], ![![0, 0, 1], ![-9, -9, 22], ![6, -6, 16]]]
  hle1 := by decide
  hle2 := by decide

lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI17N0)

def MemCI17N0 : IdealMemCertificate B I17N0
  ![![17, 0, 0], ![0, 17, 0], ![8, 7, 1]] ![200, 90, -9] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI17N0
 g := ![16, 9, -9]
 hmem := by decide

def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [15, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 16], [0, 1]]
 g := ![![[15, 8], [8], [16], [1]],![[0, 9], [8], [16], [1]]]
 h' := ![![[13, 16], [3, 5], [2, 5], [2, 13], [0, 1]],![[0, 1], [0, 12], [16, 12], [1, 4], [13, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [14, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal O 17 where 
  r := 3
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I17N0
  hcard := NI17N0
  P := [15, 4, 1]
  f := ofList [15, 4, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P17P0
  hneq := by decide
  hlen := by decide
  c := ![200, 90, -9]
  a := ![1, 0, -3]
  z := ![1, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI17N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI17N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal.isPrime PI17N0
def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![-5, 1, 0]] i)))

def SI17N1: IdealEqSpanCertificate timesTableO I17N1
 ![![17, 0, 0], ![-5, 1, 0]] 
 ![![17, 0, 0], ![12, 1, 0], ![1, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![-5, 1, 0], ![-1, -6, 3], ![30, 0, -4]]]
  hmulB := by decide
  f := ![![![-129, -780, 390], ![0, -2210, 0]], ![![-90, -546, 273], ![1, -1547, 0]], ![![-7, -46, 23], ![2, -130, 0]]]
  g := ![![![1, 0, 0], ![-12, 17, 0], ![-1, 0, 17]], ![![-1, 1, 0], ![4, -6, 3], ![2, 0, -4]]]
  hle1 := by decide
  hle2 := by decide

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulEqCertificate timesTableO (I17N0) I17N1
  ![![17, 0, 0], ![8, 7, 1]] ![![17, 0, 0], ![-5, 1, 0]]
  ![![17, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![289, 0, 0], ![-85, 17, 0]], ![![136, 119, 17], ![-17, -34, 17]]]
 hmul := by decide
 f :=  ![![![![-2654, -15683, 7846], ![-135, -44460, 0]], ![![-2, 0, 0], ![0, 0, 0]]]]
 g :=  ![![![![17, 0, 0]], ![![-5, 1, 0]]], ![![![8, 7, 1]], ![![-1, -2, 1]]]]
 hle1 := by decide
 hle2 := by decide

def PBC17 : IsPrimesAboveP 17 ![I17N0, I17N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI17N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}
def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0]] i)))

def SI19N0: IdealEqSpanCertificate timesTableO I19N0
 ![![19, 0, 0]] 
 ![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]]]
  hmulB := by decide
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI19N0 : Nat.card (O ⧸ I19N0) = 6859 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI19N0)

def MemCI19N0 : IdealMemCertificate B I19N0
  ![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]] ![749873, 123082, 49552] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI19N0
 g := ![39467, 6478, 2608]
 hmem := by decide

def P19P0 : CertificateIrreducibleZModOfList' 19 3 2 4 [16, 12, 18, 1] where
 m := 1
 P := ![3]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 3, 18], [3, 15, 1], [0, 1]]
 g := ![![[12, 3, 1], [3, 15, 7], [1, 1], []],![[7, 17, 1, 13], [17, 0, 2, 3], [7, 16], [14, 1]],![[18, 0, 6, 16], [8, 17, 2, 16], [7, 9], [12, 1]]]
 h' := ![![[17, 3, 18], [9, 18, 18], [3, 10, 8], [0, 0, 1], [0, 1]],![[3, 15, 1], [3, 3, 5], [9, 1, 15], [8, 13, 15], [17, 3, 18]],![[0, 1], [18, 17, 15], [13, 8, 15], [7, 6, 3], [3, 15, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 15], []]
 b := ![[], [9, 15, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal O 19 where 
  r := 3
  n := 3
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I19N0
  hcard := NI19N0
  P := [16, 12, 18, 1]
  f := ofList [16, 12, 18, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P19P0
  hneq := by decide
  hlen := by decide
  c := ![749873, 123082, 49552]
  a := ![-1, 18, 4]
  z := ![1, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI19N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI19N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal.isPrime PI19N0
def PBC19 : IsPrimesAboveP 19 ![I19N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    unfold I19N0
    rw [Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}
def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![0, 7, 1]] i)))

def SI23N0: IdealEqSpanCertificate timesTableO I23N0
 ![![23, 0, 0], ![0, 7, 1]] 
 ![![23, 0, 0], ![0, 23, 0], ![0, 7, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![0, 7, 1], ![23, -7, 22], ![230, 10, 8]]]
  hmulB := by decide
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, -6, -1], ![23, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, -7, 23]], ![![0, 0, 1], ![1, -7, 22], ![10, -2, 8]]]
  hle1 := by decide
  hle2 := by decide

lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI23N0)

def MemCI23N0 : IdealMemCertificate B I23N0
  ![![23, 0, 0], ![0, 23, 0], ![0, 7, 1]] ![-621, 200, -24] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI23N0
 g := ![-27, 16, -24]
 hmem := by decide

def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [22, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 22], [0, 1]]
 g := ![![[11, 4], [14, 12], [19, 6], [1]],![[9, 19], [8, 11], [16, 17], [1]]]
 h' := ![![[11, 22], [14, 21], [19, 9], [1, 11], [0, 1]],![[0, 1], [15, 2], [3, 14], [7, 12], [11, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [8, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal O 23 where 
  r := 3
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I23N0
  hcard := NI23N0
  P := [22, 12, 1]
  f := ofList [22, 12, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P23P0
  hneq := by decide
  hlen := by decide
  c := ![-621, 200, -24]
  a := ![1, 4, -4]
  z := ![1, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI23N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI23N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal.isPrime PI23N0
def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![1, 1, 0]] i)))

def SI23N1: IdealEqSpanCertificate timesTableO I23N1
 ![![23, 0, 0], ![1, 1, 0]] 
 ![![23, 0, 0], ![1, 1, 0], ![15, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![1, 1, 0], ![-1, 0, 3], ![30, 0, 2]]]
  hmulB := by decide
  f := ![![![0, -1, 0], ![23, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 2], ![0, -15, 0]]]
  g := ![![![1, 0, 0], ![-1, 23, 0], ![-15, 0, 23]], ![![0, 1, 0], ![-2, 0, 3], ![0, 0, 2]]]
  hle1 := by decide
  hle2 := by decide

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulEqCertificate timesTableO (I23N0) I23N1
  ![![23, 0, 0], ![0, 7, 1]] ![![23, 0, 0], ![1, 1, 0]]
  ![![23, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![529, 0, 0], ![23, 23, 0]], ![![0, 161, 23], ![23, 0, 23]]]
 hmul := by decide
 f :=  ![![![![-3160, -3160, 9061], ![-260, -72941, 0]], ![![10420, 0, 0], ![0, 0, 0]]]]
 g :=  ![![![![23, 0, 0]], ![![1, 1, 0]]], ![![![0, 7, 1]], ![![1, 0, 1]]]]
 hle1 := by decide
 hle2 := by decide

def PBC23 : IsPrimesAboveP 23 ![I23N0, I23N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI23N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}
def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![-12, -7, 1]] i)))

def SI29N0: IdealEqSpanCertificate timesTableO I29N0
 ![![29, 0, 0], ![-12, -7, 1]] 
 ![![29, 0, 0], ![0, 29, 0], ![17, 22, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![-12, -7, 1], ![37, -5, -20], ![-190, 10, -18]]]
  hmulB := by decide
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-17, -22, 29]], ![![-1, -1, 1], ![13, 15, -20], ![4, 14, -18]]]
  hle1 := by decide
  hle2 := by decide

lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI29N0)

def MemCI29N0 : IdealMemCertificate B I29N0
  ![![29, 0, 0], ![0, 29, 0], ![17, 22, 1]] ![325, 337, 159] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI29N0
 g := ![-82, -109, 159]
 hmem := by decide

def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [14, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 28], [0, 1]]
 g := ![![[6, 1], [1], [2, 25], [3, 1]],![[9, 28], [1], [19, 4], [6, 28]]]
 h' := ![![[3, 28], [16, 1], [1, 28], [16, 24], [0, 1]],![[0, 1], [19, 28], [27, 1], [1, 5], [3, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [24, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal O 29 where 
  r := 3
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I29N0
  hcard := NI29N0
  P := [14, 26, 1]
  f := ofList [14, 26, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P29P0
  hneq := by decide
  hlen := by decide
  c := ![325, 337, 159]
  a := ![-2, -1, 6]
  z := ![1, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI29N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI29N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal.isPrime PI29N0
def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![-9, 1, 0]] i)))

def SI29N1: IdealEqSpanCertificate timesTableO I29N1
 ![![29, 0, 0], ![-9, 1, 0]] 
 ![![29, 0, 0], ![20, 1, 0], ![18, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![-9, 1, 0], ![-1, -10, 3], ![30, 0, -8]]]
  hmulB := by decide
  f := ![![![-79, -800, 240], ![0, -2320, 0]], ![![-54, -550, 165], ![1, -1595, 0]], ![![-45, -497, 149], ![13, -1440, 0]]]
  g := ![![![1, 0, 0], ![-20, 29, 0], ![-18, 0, 29]], ![![-1, 1, 0], ![5, -10, 3], ![6, 0, -8]]]
  hle1 := by decide
  hle2 := by decide

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulEqCertificate timesTableO (I29N0) I29N1
  ![![29, 0, 0], ![-12, -7, 1]] ![![29, 0, 0], ![-9, 1, 0]]
  ![![29, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![841, 0, 0], ![-261, 29, 0]], ![![-348, -203, 29], ![145, 58, -29]]]
 hmul := by decide
 f :=  ![![![![-560102, -5608261, 1683348], ![-19545, -16278230, 0]], ![![17598, 0, 0], ![0, 0, 0]]]]
 g :=  ![![![![29, 0, 0]], ![![-9, 1, 0]]], ![![![-12, -7, 1]], ![![5, 2, -1]]]]
 hle1 := by decide
 hle2 := by decide

def PBC29 : IsPrimesAboveP 29 ![I29N0, I29N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI29N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}
def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![4, 1, 0]] i)))

def SI31N0: IdealEqSpanCertificate timesTableO I31N0
 ![![31, 0, 0], ![4, 1, 0]] 
 ![![31, 0, 0], ![4, 1, 0], ![6, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![4, 1, 0], ![-1, 3, 3], ![30, 0, 5]]]
  hmulB := by decide
  f := ![![![-135, 408, 408], ![0, -4216, 0]], ![![-17, 51, 51], ![1, -527, 0]], ![![-30, 78, 79], ![30, -816, 0]]]
  g := ![![![1, 0, 0], ![-4, 31, 0], ![-6, 0, 31]], ![![0, 1, 0], ![-1, 3, 3], ![0, 0, 5]]]
  hle1 := by decide
  hle2 := by decide

lemma NI31N0 : Nat.card (O ⧸ I31N0) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI31N0)

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := prime_ideal_of_norm_prime hp31.out _ NI31N0
def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![7, 1, 0]] i)))

def SI31N1: IdealEqSpanCertificate timesTableO I31N1
 ![![31, 0, 0], ![7, 1, 0]] 
 ![![31, 0, 0], ![7, 1, 0], ![27, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![7, 1, 0], ![-1, 6, 3], ![30, 0, 8]]]
  hmulB := by decide
  f := ![![![-260, 1566, 783], ![0, -8091, 0]], ![![-58, 348, 174], ![1, -1798, 0]], ![![-226, 1364, 682], ![-2, -7047, 0]]]
  g := ![![![1, 0, 0], ![-7, 31, 0], ![-27, 0, 31]], ![![0, 1, 0], ![-4, 6, 3], ![-6, 0, 8]]]
  hle1 := by decide
  hle2 := by decide

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def I31N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![-11, 1, 0]] i)))

def SI31N2: IdealEqSpanCertificate timesTableO I31N2
 ![![31, 0, 0], ![-11, 1, 0]] 
 ![![31, 0, 0], ![20, 1, 0], ![28, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![-11, 1, 0], ![-1, -12, 3], ![30, 0, -10]]]
  hmulB := by decide
  f := ![![![-223, -2688, 672], ![0, -6944, 0]], ![![-143, -1728, 432], ![1, -4464, 0]], ![![-200, -2428, 607], ![4, -6272, 0]]]
  g := ![![![1, 0, 0], ![-20, 31, 0], ![-28, 0, 31]], ![![-1, 1, 0], ![5, -12, 3], ![10, 0, -10]]]
  hle1 := by decide
  hle2 := by decide

lemma NI31N2 : Nat.card (O ⧸ I31N2) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI31N2)

lemma isPrimeI31N2 : Ideal.IsPrime I31N2 := prime_ideal_of_norm_prime hp31.out _ NI31N2
def MulI31N0 : IdealMulEqCertificate timesTableO (I31N0) I31N1
  ![![31, 0, 0], ![4, 1, 0]] ![![31, 0, 0], ![7, 1, 0]]
  ![![31, 0, 0], ![9, -7, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![961, 0, 0], ![217, 31, 0]], ![![124, 31, 0], ![27, 10, 3]]]
 hmul := by decide
 f :=  ![![![![193115521, -1167102703, -583452354], ![5958284, 6029007635, 0]], ![![179469, 0, 0], ![713, 0, 0]]], ![![![56120723, -339168231, -169555346], ![1731527, 1752071902, 0]], ![![52155, 0, 0], ![207, 0, 0]]]]
 g :=  ![![![![22, 7, -1], ![31, 0, 0]], ![![-2, 8, -1], ![31, 0, 0]]], ![![![-5, 8, -1], ![31, 0, 0]], ![![0, 1, 0], ![3, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI31N1 : IdealMulEqCertificate timesTableO (I31N0*I31N1) I31N2
  ![![31, 0, 0], ![9, -7, 1]] ![![31, 0, 0], ![-11, 1, 0]]
  ![![31, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI31N0
 hI2 := rfl
 M :=  ![![![961, 0, 0], ![-341, 31, 0]], ![![279, -217, 31], ![-62, 93, -31]]]
 hmul := by decide
 f :=  ![![![![-39356711, -467527210, 116890572], ![-1116218, -1207866044, 0]], ![![-9600, 0, 0], ![0, 0, 0]]]]
 g :=  ![![![![31, 0, 0]], ![![-11, 1, 0]]], ![![![9, -7, 1]], ![![-2, 3, -1]]]]
 hle1 := by decide
 hle2 := by decide

def PBC31 : IsPrimesAboveP 31 ![I31N0, I31N1, I31N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
    exact isPrimeI31N2
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI31N1, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
