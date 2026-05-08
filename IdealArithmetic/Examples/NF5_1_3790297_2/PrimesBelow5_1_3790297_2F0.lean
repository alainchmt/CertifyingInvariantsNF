
import IdealArithmetic.Examples.NF5_1_3790297_2.RI5_1_3790297_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] i)))

def SI2N0: IdealEqSpanCertificate timesTableO I2N0
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![-4, -5, -6, -2, 16], ![-1, -2, -1, 0, 3]]]
  hmulB := by decide
  f := ![![![0, -2, 0, 0, 3], ![0, -2, 0, 0, -2]], ![![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]], ![![0, -1, 0, 0, 2], ![0, -1, 0, 0, -1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![-1, 0, 0, 0, 2]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![-10, -5, -6, -2, 16], ![-2, -2, -1, 0, 3]]]
  hle1 := by decide
  hle2 := by decide

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0
def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![2, 0, -1, 0, 1]] i)))

def SI2N1: IdealEqSpanCertificate timesTableO I2N1
 ![![2, 0, 0, 0, 0], ![2, 0, -1, 0, 1]] 
 ![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![1, 1, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 1, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![2, 0, -1, 0, 1], ![-1, 0, -1, -1, 3], ![1, -2, 3, 1, -7], ![3, 10, -1, 1, -5], ![1, 1, 1, 0, -2]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 1, -1], ![0, 2, 0, 0, 2]], ![![0, 0, 0, 0, 1], ![0, 0, 0, 0, 1]], ![![-1, 0, 0, 0, 1], ![1, -1, 0, 0, 0]], ![![-1, 0, 0, 0, 1], ![1, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-1, -1, 2, 0, 0], ![-1, 0, 0, 2, 0], ![-1, -1, 0, 0, 2]], ![![1, 0, -1, 0, 1], ![-1, -1, -1, -1, 3], ![2, 1, 3, 1, -7], ![4, 8, -1, 1, -5], ![1, 1, 1, 0, -2]]]
  hle1 := by decide
  hle2 := by decide

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 4 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI2N1)

def MemCI2N1 : IdealMemCertificate B I2N1
  ![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![1, 1, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 1, 0, 0, 1]] ![475, 329, 259, -72, -2076] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI2N1
 g := ![1182, 1073, 259, -72, -2076]
 hmem := by decide

def P2P1 : CertificateIrreducibleZModOfList' 2 2 2 1 [1, 1, 1] where
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

def PI2N1 : CertifiedPrimeIdeal O 2 where 
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I2N1
  hcard := NI2N1
  P := [1, 1, 1]
  f := ofList [1, 1, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P2P1
  hneq := by decide
  hlen := by decide
  c := ![475, 329, 259, -72, -2076]
  a := ![9, 11, 12, 3, -36]
  z := ![1, 0, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI2N1
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI2N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := CertifiedPrimeIdeal.isPrime PI2N1
def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] i)))

def SI2N2: IdealEqSpanCertificate timesTableO I2N2
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 2]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![1, 1, 0, 0, 0], ![0, 1, 1, 0, 0], ![0, 0, 1, 1, 0], ![-4, -5, -6, -1, 16], ![-1, -2, -1, 0, 4]]]
  hmulB := by decide
  f := ![![![0, -1, 1, 1, 0], ![2, 0, -2, 0, 0]], ![![0, 0, 1, 1, 0], ![1, 0, -2, 0, 0]], ![![0, 0, 1, 0, 0], ![1, -1, 0, 0, 0]], ![![0, 0, 1, 1, 0], ![1, -1, -1, 0, 0]], ![![0, 0, 0, 0, 1], ![0, 0, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-1, 2, 0, 0, 0], ![-1, 0, 2, 0, 0], ![-1, 0, 0, 2, 0], ![0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0], ![-1, 1, 1, 0, 0], ![-1, 0, 1, 1, 0], ![4, -5, -6, -1, 8], ![1, -2, -1, 0, 2]]]
  hle1 := by decide
  hle2 := by decide

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 4 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI2N2)

def MemCI2N2 : IdealMemCertificate B I2N2
  ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 2]] ![-16989, -100752, -71184, -27285, -1022] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI2N2
 g := ![91116, -100752, -71184, -27285, -511]
 hmem := by decide

def P2P2 : CertificateIrreducibleZModOfList' 2 2 2 1 [1, 1, 1] where
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

def PI2N2 : CertifiedPrimeIdeal O 2 where 
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I2N2
  hcard := NI2N2
  P := [1, 1, 1]
  f := ofList [1, 1, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P2P2
  hneq := by decide
  hlen := by decide
  c := ![-16989, -100752, -71184, -27285, -1022]
  a := ![51, 47, 47, -6, -201]
  z := ![1, 0, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI2N2
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI2N2]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := CertifiedPrimeIdeal.isPrime PI2N2
def MulI2N0 : IdealMulEqCertificate timesTableO (I2N0) I2N1
  ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] ![![2, 0, 0, 0, 0], ![2, 0, -1, 0, 1]]
  ![![2, 0, 0, 0, 0], ![-2, 1, 1, 1, -4]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![4, 0, 0, 0, 0], ![4, 0, -2, 0, 2]], ![![0, 2, 0, 0, 0], ![-1, 0, -1, -1, 3]]]
 hmul := by decide
 f :=  ![![![![0, 0, 2, -1, 2], ![0, -1, 0, 0, -1]], ![![1, -5, 0, 0, 0], ![-2, 0, 0, 0, 0]]], ![![![0, 0, -3, 1, -3], ![0, 1, 0, 0, 1]], ![![2, 8, 0, 0, 0], ![0, 0, 0, 0, -1]]]]
 g :=  ![![![![0, -2, 0, 0, 2], ![0, 0, 0, 0, -4]], ![![0, -2, -1, 0, 3], ![0, 0, 0, 0, -4]]], ![![![0, 0, 1, 1, -4], ![0, 2, 0, 0, 0]], ![![0, 0, 0, 0, -1], ![0, 1, 0, 0, 1]]]]
 hle1 := by decide
 hle2 := by decide

def MulI2N1 : IdealMulEqCertificate timesTableO (I2N0*I2N1) I2N2
  ![![2, 0, 0, 0, 0], ![-2, 1, 1, 1, -4]] ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0]]
  ![![2, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI2N0
 hI2 := rfl
 M :=  ![![![4, 0, 0, 0, 0], ![2, 2, 0, 0, 0]], ![![-4, 2, 2, 2, -8], ![-2, 2, 0, 0, 0]]]
 hmul := by decide
 f :=  ![![![![0, 0, -1, 0, -2], ![-1, 2, 1, 0, 0]], ![![-1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]]
 g :=  ![![![![2, 0, 0, 0, 0]], ![![1, 1, 0, 0, 0]]], ![![![-2, 1, 1, 1, -4]], ![![-1, 1, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def PBC2 : IsPrimesAboveP 2 ![I2N0, I2N1, I2N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
    exact isPrimeI2N2
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI2N1, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp3 : Fact (Nat.Prime 3) := {out := by norm_num}
def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0]] i)))

def SI3N0: IdealEqSpanCertificate timesTableO I3N0
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

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 243 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI3N0)

def MemCI3N0 : IdealMemCertificate B I3N0
  ![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]] ![-76785180, -168502560, -105535317, -17080107, 235757295] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI3N0
 g := ![-25595060, -56167520, -35178439, -5693369, 78585765]
 hmem := by decide

def P3P0 : CertificateIrreducibleZModOfList' 3 5 2 1 [1, 1, 2, 1, 1, 1] where
 m := 1
 P := ![5]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 0, 0, 1], [1, 2, 0, 1, 2], [1, 0, 2, 1, 2], [0, 0, 1, 0, 2], [0, 1]]
 g := ![![[]],![[2, 2, 0, 2, 1]],![[0, 0, 1, 0, 2, 0, 1, 2]],![[1, 2, 1, 0, 2, 0, 1, 2]],![[0, 2, 1, 1, 1, 0, 1, 2]]]
 h' := ![![[0, 0, 0, 1], [0, 1]],![[1, 2, 0, 1, 2], [0, 0, 0, 1]],![[1, 0, 2, 1, 2], [1, 2, 0, 1, 2]],![[0, 0, 1, 0, 2], [1, 0, 2, 1, 2]],![[0, 1], [0, 0, 1, 0, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1], [], [], []]
 b := ![[], [1, 2, 2], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal O 3 where 
  r := 5
  n := 5
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I3N0
  hcard := NI3N0
  P := [1, 1, 2, 1, 1, 1]
  f := ofList [1, 1, 2, 1, 1, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P3P0
  hneq := by decide
  hlen := by decide
  c := ![-76785180, -168502560, -105535317, -17080107, 235757295]
  a := ![4, 4, 5, 0, -15]
  z := ![1, 0, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI3N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI3N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal.isPrime PI3N0
def PBC3 : IsPrimesAboveP 3 ![I3N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    unfold I3N0
    rw [Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp5 : Fact (Nat.Prime 5) := {out := by norm_num}
def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0, 0, 0], ![1, 2, -1, 0, 1]] i)))

def SI5N0: IdealEqSpanCertificate timesTableO I5N0
 ![![5, 0, 0, 0, 0], ![1, 2, -1, 0, 1]] 
 ![![5, 0, 0, 0, 0], ![0, 5, 0, 0, 0], ![3, 3, 1, 0, 0], ![1, 4, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![5, 0, 0, 0, 0], ![0, 5, 0, 0, 0], ![0, 0, 5, 0, 0], ![0, 0, 0, 5, 0], ![0, 0, 0, 0, 5]], ![![1, 2, -1, 0, 1], ![-1, -1, 1, -1, 3], ![1, -2, 2, 3, -7], ![-5, 0, -13, -4, 27], ![-1, -3, -1, 0, 3]]]
  hmulB := by decide
  f := ![![![29, 58, -64, 10, -60], ![30, 230, 60, 0, 0]], ![![0, 0, 0, 1, -4], ![5, 5, 0, 0, 0]], ![![16, 32, -35, 6, -35], ![19, 129, 33, 0, 0]], ![![6, 12, -13, 3, -15], ![9, 50, 12, 0, 0]], ![![23, 46, -51, 8, -48], ![25, 184, 48, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-3, -3, 5, 0, 0], ![-1, -4, 0, 5, 0], ![-4, 0, 0, 0, 5]], ![![0, 1, -1, 0, 1], ![-3, 0, 1, -1, 3], ![4, -4, 2, 3, -7], ![-14, 11, -13, -4, 27], ![-2, 0, -1, 0, 3]]]
  hle1 := by decide
  hle2 := by decide

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 25 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI5N0)

def MemCI5N0 : IdealMemCertificate B I5N0
  ![![5, 0, 0, 0, 0], ![0, 5, 0, 0, 0], ![3, 3, 1, 0, 0], ![1, 4, 0, 1, 0], ![4, 0, 0, 0, 1]] ![3408, -7014, -4708, -3665, -22867] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI5N0
 g := ![22533, 4354, -4708, -3665, -22867]
 hmem := by decide

def P5P0 : CertificateIrreducibleZModOfList' 5 2 2 2 [2, 0, 1] where
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
 h' := ![![[0, 4], [3], [0, 1]],![[0, 1], [3], [0, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [0, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal O 5 where 
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I5N0
  hcard := NI5N0
  P := [2, 0, 1]
  f := ofList [2, 0, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P5P0
  hneq := by decide
  hlen := by decide
  c := ![3408, -7014, -4708, -3665, -22867]
  a := ![-34, -38, -40, -8, 137]
  z := ![1, 0, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI5N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI5N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := CertifiedPrimeIdeal.isPrime PI5N0
def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0, 0, 0], ![-1, 2, -1, 0, 1]] i)))

def SI5N1: IdealEqSpanCertificate timesTableO I5N1
 ![![5, 0, 0, 0, 0], ![-1, 2, -1, 0, 1]] 
 ![![5, 0, 0, 0, 0], ![0, 5, 0, 0, 0], ![0, 0, 5, 0, 0], ![3, 4, 1, 1, 0], ![4, 2, 4, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![5, 0, 0, 0, 0], ![0, 5, 0, 0, 0], ![0, 0, 5, 0, 0], ![0, 0, 0, 5, 0], ![0, 0, 0, 0, 5]], ![![-1, 2, -1, 0, 1], ![-1, -3, 1, -1, 3], ![1, -2, 0, 3, -7], ![-5, 0, -13, -6, 27], ![-1, -3, -1, 0, 1]]]
  hmulB := by decide
  f := ![![![-2, -9, 3, -3, 9], ![0, -15, 0, 0, 0]], ![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![4, 7, -1, 3, -10], ![5, 15, 0, 0, 0]], ![![0, 1, 0, 0, 1], ![-2, -1, 0, 0, 0]], ![![1, 0, 1, 0, 0], ![1, 0, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-3, -4, -1, 5, 0], ![-4, -2, -4, 0, 5]], ![![-1, 0, -1, 0, 1], ![-2, -1, -2, -1, 3], ![4, 0, 5, 3, -7], ![-19, -6, -23, -6, 27], ![-1, -1, -1, 0, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 125 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI5N1)

def MemCI5N1 : IdealMemCertificate B I5N1
  ![![5, 0, 0, 0, 0], ![0, 5, 0, 0, 0], ![0, 0, 5, 0, 0], ![3, 4, 1, 1, 0], ![4, 2, 4, 0, 1]] ![642021, 1052283, 726999, 96221, -2288713] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI5N1
 g := ![1901642, 1048965, 1957126, 96221, -2288713]
 hmem := by decide

def P5P1 : CertificateIrreducibleZModOfList' 5 3 2 2 [2, 2, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 2, 3], [1, 2, 2], [0, 1]]
 g := ![![[2, 2, 1], []],![[0, 1, 4, 2], [0, 4]],![[3, 1, 1, 3], [1, 4]]]
 h' := ![![[1, 2, 3], [0, 0, 1], [0, 1]],![[1, 2, 2], [1, 1, 2], [1, 2, 3]],![[0, 1], [4, 4, 2], [1, 2, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 4], []]
 b := ![[], [0, 1, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N1 : CertifiedPrimeIdeal O 5 where 
  r := 5
  n := 3
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I5N1
  hcard := NI5N1
  P := [2, 2, 3, 1]
  f := ofList [2, 2, 3, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P5P1
  hneq := by decide
  hlen := by decide
  c := ![642021, 1052283, 726999, 96221, -2288713]
  a := ![23, 29, 35, 13, -93]
  z := ![1, 0, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI5N1
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI5N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := CertifiedPrimeIdeal.isPrime PI5N1
def MulI5N0 : IdealMulEqCertificate timesTableO (I5N0) I5N1
  ![![5, 0, 0, 0, 0], ![1, 2, -1, 0, 1]] ![![5, 0, 0, 0, 0], ![-1, 2, -1, 0, 1]]
  ![![5, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![25, 0, 0, 0, 0], ![-5, 10, -5, 0, 5]], ![![5, 10, -5, 0, 5], ![-5, -5, 0, -5, 15]]]
 hmul := by decide
 f :=  ![![![![25, 63, -20, 23, -72], ![12, 115, 0, 0, 0]], ![![3, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]]
 g :=  ![![![![5, 0, 0, 0, 0]], ![![-1, 2, -1, 0, 1]]], ![![![1, 2, -1, 0, 1]], ![![-1, -1, 0, -1, 3]]]]
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
def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0, 0], ![3, 2, -1, 0, 1]] i)))

def SI7N0: IdealEqSpanCertificate timesTableO I7N0
 ![![7, 0, 0, 0, 0], ![3, 2, -1, 0, 1]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![3, 2, 1, 0, 0], ![1, 6, 0, 1, 0], ![6, 4, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]], ![![3, 2, -1, 0, 1], ![-1, 1, 1, -1, 3], ![1, -2, 4, 3, -7], ![-5, 0, -13, -2, 27], ![-1, -3, -1, 0, 5]]]
  hmulB := by decide
  f := ![![![217, -196, -343, 169, -558], ![7, 1708, 175, 0, 0]], ![![269, -243, -421, 212, -697], ![7, 2114, 210, 0, 0]], ![![163, -148, -257, 128, -422], ![6, 1286, 130, 0, 0]], ![![259, -238, -409, 206, -678], ![13, 2056, 205, 0, 0]], ![![338, -308, -534, 266, -877], ![14, 2672, 270, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-3, -2, 7, 0, 0], ![-1, -6, 0, 7, 0], ![-6, -4, 0, 0, 7]], ![![0, 0, -1, 0, 1], ![-3, -1, 1, -1, 3], ![4, 0, 4, 3, -7], ![-18, -10, -13, -2, 27], ![-4, -3, -1, 0, 5]]]
  hle1 := by decide
  hle2 := by decide

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 49 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI7N0)

def MemCI7N0 : IdealMemCertificate B I7N0
  ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![3, 2, 1, 0, 0], ![1, 6, 0, 1, 0], ![6, 4, 0, 0, 1]] ![-316, -1008, -1776, 344, 960] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI7N0
 g := ![-156, -480, -1776, 344, 960]
 hmem := by decide

def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [4, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 6], [0, 1]]
 g := ![![[5, 2], [1, 1]],![[0, 5], [2, 6]]]
 h' := ![![[1, 6], [3, 4], [0, 1]],![[0, 1], [0, 3], [1, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [6, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal O 7 where 
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I7N0
  hcard := NI7N0
  P := [4, 6, 1]
  f := ofList [4, 6, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P7P0
  hneq := by decide
  hlen := by decide
  c := ![-316, -1008, -1776, 344, 960]
  a := ![-8, -10, -10, -14, 32]
  z := ![1, 0, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI7N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI7N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal.isPrime PI7N0
def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]] i)))

def SI7N1: IdealEqSpanCertificate timesTableO I7N1
 ![![7, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]] 
 ![![7, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]], ![![-1, 1, 0, 0, 0], ![0, -1, 1, 0, 0], ![0, 0, -1, 1, 0], ![-4, -5, -6, -3, 16], ![-1, -2, -1, 0, 2]]]
  hmulB := by decide
  f := ![![![162, -265, 288, 32, -192], ![791, -1484, 28, 84, 0]], ![![162, -264, 287, 32, -192], ![792, -1477, 28, 84, 0]], ![![162, -264, 287, 32, -192], ![792, -1476, 28, 84, 0]], ![![135, -221, 241, 26, -160], ![659, -1238, 29, 70, 0]], ![![117, -190, 206, 22, -137], ![574, -1056, 26, 60, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-6, 7, 0, 0, 0], ![-6, 0, 7, 0, 0], ![-6, 0, 0, 7, 0], ![-5, 0, 0, 0, 7]], ![![-1, 1, 0, 0, 0], ![0, -1, 1, 0, 0], ![0, 0, -1, 1, 0], ![0, -5, -6, -3, 16], ![1, -2, -1, 0, 2]]]
  hle1 := by decide
  hle2 := by decide

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulEqCertificate timesTableO (I7N0) I7N1
  ![![7, 0, 0, 0, 0], ![3, 2, -1, 0, 1]] ![![7, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]]
  ![![-3, 1, 2, 1, -4]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![49, 0, 0, 0, 0], ![-7, 7, 0, 0, 0]], ![![21, 14, -7, 0, 7], ![-4, -1, 2, -1, 2]]]
 hmul := by decide
 f :=  ![![![![-894549, 1459009, -1594121, -179096, 1068107], ![-4360925, 8211180, -150045, -467906, 0]], ![![9729, 0, 0, 0, 0], ![-214, -55, 0, 0, 0]]]]
 g :=  ![![![![-7, 0, 7, 7, -28]], ![![1, 2, -3, -2, 8]]], ![![![-3, 8, -4, 1, -1]], ![![0, -2, 1, -1, 2]]]]
 hle1 := by decide
 hle2 := by decide

def MulI7N1 : IdealMulEqCertificate timesTableO (I7N0*I7N1) I7N1
  ![![-3, 1, 2, 1, -4]] ![![7, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]]
  ![![7, 0, 0, 0, 0], ![-16, 3, 9, 3, -17]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI7N0
 hI2 := rfl
 M :=  ![![![-21, 7, 14, 7, -28], ![3, -1, -3, -1, 8]]]
 hmul := by decide
 f :=  ![![![![151, 442, 0, -14, -290], ![45, 1113, 99, 0, 1013]]], ![![![-338, -995, 0, 32, 651], ![-93, -2502, -225, 0, -2277]]]]
 g :=  ![![![![13, -2, -7, -2, 13], ![7, 0, 0, 0, 0]], ![![5, -1, -3, -1, 6], ![2, 0, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI7N2 : IdealMulEqCertificate timesTableO (I7N0*I7N1*I7N1) I7N1
  ![![7, 0, 0, 0, 0], ![-16, 3, 9, 3, -17]] ![![7, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]]
  ![![7, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI7N1
 hI2 := rfl
 M :=  ![![![49, 0, 0, 0, 0], ![-7, 7, 0, 0, 0]], ![![-112, 21, 63, 21, -119], ![21, 0, -7, 0, 14]]]
 hmul := by decide
 f :=  ![![![![-255, 422, -457, -51, 300], ![-1240, 2374, -39, -132, 0]], ![![0, 0, 0, 0, 0], ![6, 0, 0, 0, 0]]]]
 g :=  ![![![![7, 0, 0, 0, 0]], ![![-1, 1, 0, 0, 0]]], ![![![-16, 3, 9, 3, -17]], ![![3, 0, -1, 0, 2]]]]
 hle1 := by decide
 hle2 := by decide

def PBC7 : IsPrimesAboveP 7 ![I7N0, I7N1, I7N1, I7N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N1
    exact isPrimeI7N1
    exact isPrimeI7N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI7N2, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}
def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0], ![3, 1, -1, 0, 1]] i)))

def SI11N0: IdealEqSpanCertificate timesTableO I11N0
 ![![11, 0, 0, 0, 0], ![3, 1, -1, 0, 1]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![8, 4, 1, 0, 0], ![1, 3, 0, 1, 0], ![0, 5, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]], ![![3, 1, -1, 0, 1], ![-1, 1, 0, -1, 3], ![1, -2, 4, 2, -7], ![-1, 5, -7, 0, 11], ![0, -1, 0, 0, 2]]]
  hmulB := by decide
  f := ![![![4283, -4098, -346, 4124, -12266], ![-286, 47124, 880, 0, 0]], ![![4327, -4142, -346, 4169, -12401], ![-286, 47619, 880, 0, 0]], ![![4638, -4440, -373, 4468, -13290], ![-304, 51048, 950, 0, 0]], ![![1567, -1503, -125, 1512, -4498], ![-95, 17271, 320, 0, 0]], ![![1966, -1883, -157, 1895, -5637], ![-127, 21645, 400, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-8, -4, 11, 0, 0], ![-1, -3, 0, 11, 0], ![0, -5, 0, 0, 11]], ![![1, 0, -1, 0, 1], ![0, -1, 0, -1, 3], ![-3, 1, 4, 2, -7], ![5, -2, -7, 0, 11], ![0, -1, 0, 0, 2]]]
  hle1 := by decide
  hle2 := by decide

lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI11N0)

def MemCI11N0 : IdealMemCertificate B I11N0
  ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![8, 4, 1, 0, 0], ![1, 3, 0, 1, 0], ![0, 5, 0, 0, 1]] ![486, -8382, -6201, -3113, -9205] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI11N0
 g := ![4837, 6526, -6201, -3113, -9205]
 hmem := by decide

def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [10, 8, 1] where
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
 g := ![![[3, 1], [0, 9], [1]],![[6, 10], [5, 2], [1]]]
 h' := ![![[3, 10], [0, 10], [1, 3], [0, 1]],![[0, 1], [8, 1], [10, 8], [3, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [7, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal O 11 where 
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I11N0
  hcard := NI11N0
  P := [10, 8, 1]
  f := ofList [10, 8, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P11P0
  hneq := by decide
  hlen := by decide
  c := ![486, -8382, -6201, -3113, -9205]
  a := ![-22, -31, -26, -4, 101]
  z := ![1, 0, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI11N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI11N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal.isPrime PI11N0
def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0], ![-3, -5, -1, 0, 1]] i)))

def SI11N1: IdealEqSpanCertificate timesTableO I11N1
 ![![11, 0, 0, 0, 0], ![-3, -5, -1, 0, 1]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 1, 0, 1, 0], ![9, 6, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]], ![![-3, -5, -1, 0, 1], ![-1, -5, -6, -1, 3], ![1, -2, -2, -4, -7], ![23, 35, 29, 6, -85], ![6, 11, 6, 0, -22]]]
  hmulB := by decide
  f := ![![![-239, -3559, -5345, -1026, 2348], ![2387, -10098, -297, 0, 0]], ![![-387, -5749, -8632, -1662, 3781], ![3850, -16302, -495, 0, 0]], ![![-13, -216, -328, -63, 144], ![153, -621, -18, 0, 0]], ![![-33, -519, -784, -151, 343], ![358, -1482, -45, 0, 0]], ![![-405, -6045, -9081, -1746, 3983], ![4059, -17154, -513, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-1, 0, 11, 0, 0], ![0, -1, 0, 11, 0], ![-9, -6, 0, 0, 11]], ![![-1, -1, -1, 0, 1], ![-2, -2, -6, -1, 3], ![6, 4, -2, -4, -7], ![69, 49, 29, 6, -85], ![18, 13, 6, 0, -22]]]
  hle1 := by decide
  hle2 := by decide

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 121 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI11N1)

def MemCI11N1 : IdealMemCertificate B I11N1
  ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 1, 0, 1, 0], ![9, 6, 0, 0, 1]] ![-137, -616, -474, -155, 178] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI11N1
 g := ![-115, -139, -474, -155, 178]
 hmem := by decide

def P11P1 : CertificateIrreducibleZModOfList' 11 2 2 3 [3, 3, 1] where
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
 g := ![![[1, 4], [2, 9], [1]],![[0, 7], [8, 2], [1]]]
 h' := ![![[8, 10], [5, 9], [8, 8], [0, 1]],![[0, 1], [0, 2], [6, 3], [8, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [1, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N1 : CertifiedPrimeIdeal O 11 where 
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I11N1
  hcard := NI11N1
  P := [3, 3, 1]
  f := ofList [3, 3, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P11P1
  hneq := by decide
  hlen := by decide
  c := ![-137, -616, -474, -155, 178]
  a := ![2, 2, 2, -2, -9]
  z := ![1, 0, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI11N1
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI11N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := CertifiedPrimeIdeal.isPrime PI11N1
def I11N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0], ![-5, 1, 0, 0, 0]] i)))

def SI11N2: IdealEqSpanCertificate timesTableO I11N2
 ![![11, 0, 0, 0, 0], ![-5, 1, 0, 0, 0]] 
 ![![11, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]], ![![-5, 1, 0, 0, 0], ![0, -5, 1, 0, 0], ![0, 0, -5, 1, 0], ![-4, -5, -6, -7, 16], ![-1, -2, -1, 0, -2]]]
  hmulB := by decide
  f := ![![![27199, -8732, 1454, 448, -1152], ![59202, -8162, 616, 792, 0]], ![![16986, -5446, 907, 280, -720], ![36972, -5082, 385, 495, 0]], ![![20404, -6542, 1089, 336, -864], ![44412, -6104, 462, 594, 0]], ![![16997, -5456, 909, 280, -720], ![36996, -5099, 386, 495, 0]], ![![17303, -5552, 925, 285, -733], ![37662, -5186, 393, 504, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-6, 11, 0, 0, 0], ![-8, 0, 11, 0, 0], ![-7, 0, 0, 11, 0], ![-7, 0, 0, 0, 11]], ![![-1, 1, 0, 0, 0], ![2, -5, 1, 0, 0], ![3, 0, -5, 1, 0], ![1, -5, -6, -7, 16], ![3, -2, -1, 0, -2]]]
  hle1 := by decide
  hle2 := by decide

lemma NI11N2 : Nat.card (O ⧸ I11N2) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI11N2)

lemma isPrimeI11N2 : Ideal.IsPrime I11N2 := prime_ideal_of_norm_prime hp11.out _ NI11N2
def MulI11N0 : IdealMulEqCertificate timesTableO (I11N0) I11N1
  ![![11, 0, 0, 0, 0], ![3, 1, -1, 0, 1]] ![![11, 0, 0, 0, 0], ![-3, -5, -1, 0, 1]]
  ![![11, 0, 0, 0, 0], ![16, -4, -10, -3, 20]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![121, 0, 0, 0, 0], ![-33, -55, -11, 0, 11]], ![![33, 11, -11, 0, 11], ![-5, -7, -1, 3, -9]]]
 hmul := by decide
 f :=  ![![![![192103517, 2850214592, 4278351160, 823464003, -1874648998], ![-1907307601, 8079996789, 244526436, 0, 0]], ![![136764, 1473, 0, 0, 0], ![-99, 0, 0, 0, 0]]], ![![![283999541, 4213663809, 6324974091, 1217382185, -2771419619], ![-2819701029, 11945202354, 361499866, 0, 0]], ![![202188, 2178, 0, 0, 0], ![-144, 0, 0, 0, 0]]]]
 g :=  ![![![![-5, 4, 10, 3, -20], ![11, 0, 0, 0, 0]], ![![-19, -1, 9, 3, -19], ![11, 0, 0, 0, 0]]], ![![![-13, 5, 9, 3, -19], ![11, 0, 0, 0, 0]], ![![9, -2, -5, -1, 9], ![-6, 1, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI11N1 : IdealMulEqCertificate timesTableO (I11N0*I11N1) I11N2
  ![![11, 0, 0, 0, 0], ![16, -4, -10, -3, 20]] ![![11, 0, 0, 0, 0], ![-5, 1, 0, 0, 0]]
  ![![11, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI11N0
 hI2 := rfl
 M :=  ![![![121, 0, 0, 0, 0], ![-55, 11, 0, 0, 0]], ![![176, -44, -110, -33, 220], ![-88, 11, 44, 11, -88]]]
 hmul := by decide
 f :=  ![![![![142563822, -47214511, 5676017, -144141, -461056], ![313386693, -41511576, 3804567, 317016, 0]], ![![-32, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]]
 g :=  ![![![![11, 0, 0, 0, 0]], ![![-5, 1, 0, 0, 0]]], ![![![16, -4, -10, -3, 20]], ![![-8, 1, 4, 1, -8]]]]
 hle1 := by decide
 hle2 := by decide

def PBC11 : IsPrimesAboveP 11 ![I11N0, I11N1, I11N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
    exact isPrimeI11N1
    exact isPrimeI11N2
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI11N1, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}
def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0]] i)))

def SI13N0: IdealEqSpanCertificate timesTableO I13N0
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

lemma NI13N0 : Nat.card (O ⧸ I13N0) = 371293 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI13N0)

def MemCI13N0 : IdealMemCertificate B I13N0
  ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]] ![303626219, 520005421, 300898026, 76421046, -1051457953] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI13N0
 g := ![23355863, 40000417, 23146002, 5878542, -80881381]
 hmem := by decide

def P13P0 : CertificateIrreducibleZModOfList' 13 5 2 3 [8, 2, 4, 6, 6, 1] where
 m := 1
 P := ![5]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 10, 7, 6, 5], [4, 10, 4, 1, 12], [1, 8, 4, 8, 8], [10, 10, 11, 11, 1], [0, 1]]
 g := ![![[1, 7, 1, 4, 3], [7, 1], []],![[3, 2, 5, 2, 9, 12, 4, 5], [8, 5, 5, 3], [7, 7, 12, 6, 1, 9, 12, 8]],![[6, 3, 7, 12, 6, 2, 9, 12], [10, 11, 0, 1], [7, 0, 2, 10, 9, 0, 9, 12]],![[4, 3, 11, 7, 4, 10, 10, 8], [12, 4, 0, 9], [0, 10, 6, 6, 0, 11, 11, 5]],![[6, 0, 11, 11, 5, 1, 6, 10], [10, 7, 7, 12], [10, 5, 5, 3, 7, 7, 1, 1]]]
 h' := ![![[5, 10, 7, 6, 5], [9, 4, 9, 6, 4], [0, 0, 0, 1], [0, 1]],![[4, 10, 4, 1, 12], [4, 2, 2, 8, 1], [4, 4, 2, 2, 9], [5, 10, 7, 6, 5]],![[1, 8, 4, 8, 8], [10, 3, 8, 12, 1], [8, 11, 9, 10, 12], [4, 10, 4, 1, 12]],![[10, 10, 11, 11, 1], [9, 1, 11, 8, 1], [1, 9, 6, 4, 10], [1, 8, 4, 8, 8]],![[0, 1], [7, 3, 9, 5, 6], [10, 2, 9, 9, 8], [10, 10, 11, 11, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 8, 0, 10], [], [], []]
 b := ![[], [0, 6, 8, 6, 11], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal O 13 where 
  r := 5
  n := 5
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I13N0
  hcard := NI13N0
  P := [8, 2, 4, 6, 6, 1]
  f := ofList [8, 2, 4, 6, 6, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P13P0
  hneq := by decide
  hlen := by decide
  c := ![303626219, 520005421, 300898026, 76421046, -1051457953]
  a := ![-9, -12, -5, -7, 39]
  z := ![1, 0, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI13N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI13N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal.isPrime PI13N0
def PBC13 : IsPrimesAboveP 13 ![I13N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    unfold I13N0
    rw [Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}
def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0, 0], ![-18, -1, 13, 3, -21]] i)))

def SI17N0: IdealEqSpanCertificate timesTableO I17N0
 ![![17, 0, 0, 0, 0], ![-18, -1, 13, 3, -21]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![13, 13, 1, 12, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]], ![![-18, -1, 13, 3, -21], ![9, 9, 2, 7, -15], ![-13, 4, -18, -12, 67], ![-19, -87, 9, 6, 9], ![-11, -11, -10, -1, 24]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![5, 1, -3, 0, 5], ![4, 0, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![-13, -13, -1, -12, 17]], ![![15, 16, 2, 15, -21], ![12, 12, 1, 11, -15], ![-52, -51, -5, -48, 67], ![-8, -12, 0, -6, 9], ![-19, -19, -2, -17, 24]]]
  hle1 := by decide
  hle2 := by decide

lemma NI17N0 : Nat.card (O ⧸ I17N0) = 83521 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI17N0)

def MemCI17N0 : IdealMemCertificate B I17N0
  ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![13, 13, 1, 12, 1]] ![18055545, 6879490, 1760750, -6891148, -83168105] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI17N0
 g := ![64661230, 64003815, 4995815, 58301536, -83168105]
 hmem := by decide

def P17P0 : CertificateIrreducibleZModOfList' 17 4 2 4 [4, 12, 2, 1, 1] where
 m := 1
 P := ![2]
 exp := ![2] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 11, 16, 6], [14, 4, 10, 15], [9, 1, 8, 13], [0, 1]]
 g := ![![[6, 8, 6, 4], [6, 3, 1], [1], []],![[5, 1, 3, 8, 13, 11], [4, 6, 9], [3, 12, 15], [7, 3, 2]],![[16, 11, 15, 13, 6, 2], [12, 12, 8], [3, 7, 8], [1, 7, 4]],![[13, 14, 13, 7, 5, 9], [5, 2, 13], [14, 9, 8], [2, 5, 16]]]
 h' := ![![[10, 11, 16, 6], [9, 12, 6, 15], [13, 5, 15, 16], [0, 0, 1], [0, 1]],![[14, 4, 10, 15], [0, 1, 15, 4], [4, 7, 6, 14], [4, 5, 9, 10], [10, 11, 16, 6]],![[9, 1, 8, 13], [2, 0, 1, 4], [13, 10, 15, 12], [5, 4, 7, 12], [14, 4, 10, 15]],![[0, 1], [6, 4, 12, 11], [3, 12, 15, 9], [5, 8, 0, 12], [9, 1, 8, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [14, 4, 1], []]
 b := ![[], [], [7, 6, 5, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal O 17 where 
  r := 5
  n := 4
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I17N0
  hcard := NI17N0
  P := [4, 12, 2, 1, 1]
  f := ofList [4, 12, 2, 1, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P17P0
  hneq := by decide
  hlen := by decide
  c := ![18055545, 6879490, 1760750, -6891148, -83168105]
  a := ![-16, -20, -24, -8, 65]
  z := ![1, 0, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI17N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI17N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal.isPrime PI17N0
def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0, 0], ![-8, 1, 0, 0, 0]] i)))

def SI17N1: IdealEqSpanCertificate timesTableO I17N1
 ![![17, 0, 0, 0, 0], ![-8, 1, 0, 0, 0]] 
 ![![17, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![15, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]], ![![-8, 1, 0, 0, 0], ![0, -8, 1, 0, 0], ![0, 0, -8, 1, 0], ![-4, -5, -6, -10, 16], ![-1, -2, -1, 0, -5]]]
  hmulB := by decide
  f := ![![![47617, -9672, 1146, 435, -768], ![100776, -8466, 765, 816, 0]], ![![29745, -6009, 711, 272, -480], ![62952, -5219, 476, 510, 0]], ![![11900, -2405, 291, 108, -192], ![25185, -2090, 204, 204, 0]], ![![41679, -8463, 1000, 381, -672], ![88209, -7404, 664, 714, 0]], ![![16806, -3408, 408, 153, -271], ![35568, -2976, 279, 288, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-9, 17, 0, 0, 0], ![-4, 0, 17, 0, 0], ![-15, 0, 0, 17, 0], ![-6, 0, 0, 0, 17]], ![![-1, 1, 0, 0, 0], ![4, -8, 1, 0, 0], ![1, 0, -8, 1, 0], ![7, -5, -6, -10, 16], ![3, -2, -1, 0, -5]]]
  hle1 := by decide
  hle2 := by decide

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulEqCertificate timesTableO (I17N0) I17N1
  ![![17, 0, 0, 0, 0], ![-18, -1, 13, 3, -21]] ![![17, 0, 0, 0, 0], ![-8, 1, 0, 0, 0]]
  ![![17, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![289, 0, 0, 0, 0], ![-136, 17, 0, 0, 0]], ![![-306, -17, 221, 51, -357], ![153, 17, -102, -17, 153]]]
 hmul := by decide
 f :=  ![![![![-771462441, 159867275, -14596202, 392382, 650415], ![-1639009652, 135274483, -13589871, -692196, 0]], ![![-861, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]]
 g :=  ![![![![17, 0, 0, 0, 0]], ![![-8, 1, 0, 0, 0]]], ![![![-18, -1, 13, 3, -21]], ![![9, 1, -6, -1, 9]]]]
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
def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0, 0, 0]] i)))

def SI19N0: IdealEqSpanCertificate timesTableO I19N0
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

lemma NI19N0 : Nat.card (O ⧸ I19N0) = 2476099 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI19N0)

def MemCI19N0 : IdealMemCertificate B I19N0
  ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]] ![12089083906, 30686693527, 19735475788, 4176126907, -33629162708] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI19N0
 g := ![636267574, 1615089133, 1038709252, 219796153, -1769955932]
 hmem := by decide

def P19P0 : CertificateIrreducibleZModOfList' 19 5 2 4 [10, 7, 1, 17, 6, 1] where
 m := 1
 P := ![5]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 13, 6, 7, 8], [11, 8, 0, 5, 18], [17, 10, 13, 14, 5], [6, 6, 0, 12, 7], [0, 1]]
 g := ![![[4, 4, 1], [1, 6, 0, 13, 1], [], []],![[9, 16, 10, 5, 6, 12, 5, 3], [2, 5, 12, 12, 8, 13, 16, 10], [10, 11, 11, 17], [15, 5, 13, 7]],![[0, 3, 18, 14, 18, 4, 7, 18], [16, 18, 2, 9, 12, 8, 16, 12], [15, 9], [11, 9, 3, 1]],![[1, 1, 9, 18, 3, 13, 12, 11], [18, 4, 15, 1, 10, 7, 6, 4], [15, 9, 18, 7], [7, 18, 9, 6]],![[14, 18, 4, 9, 11, 17, 13, 16], [17, 17, 8, 18, 5, 7, 7, 6], [11, 1, 16, 4], [8, 10, 7, 11]]]
 h' := ![![[17, 13, 6, 7, 8], [9, 9, 14, 18], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]],![[11, 8, 0, 5, 18], [15, 5, 9, 1, 13], [12, 15, 14, 1, 14], [6, 2, 3, 11, 6], [17, 13, 6, 7, 8]],![[17, 10, 13, 14, 5], [9, 0, 3, 2, 1], [9, 3, 16, 14, 11], [11, 9, 17, 16], [11, 8, 0, 5, 18]],![[6, 6, 0, 12, 7], [7, 16, 7, 10, 14], [7, 11, 13, 2, 15], [10, 16, 15, 1, 11], [17, 10, 13, 14, 5]],![[0, 1], [6, 8, 5, 7, 10], [2, 9, 14, 2, 16], [13, 11, 2, 10, 2], [6, 6, 0, 12, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 5, 4, 2], [], [], []]
 b := ![[], [13, 7, 3, 0, 14], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal O 19 where 
  r := 5
  n := 5
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I19N0
  hcard := NI19N0
  P := [10, 7, 1, 17, 6, 1]
  f := ofList [10, 7, 1, 17, 6, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P19P0
  hneq := by decide
  hlen := by decide
  c := ![12089083906, 30686693527, 19735475788, 4176126907, -33629162708]
  a := ![-12, -16, -17, -3, 52]
  z := ![1, 0, 0, 0, 0]
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
def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0, 0]] i)))

def SI23N0: IdealEqSpanCertificate timesTableO I23N0
 ![![23, 0, 0, 0, 0]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI23N0 : Nat.card (O ⧸ I23N0) = 6436343 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI23N0)

def MemCI23N0 : IdealMemCertificate B I23N0
  ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]] ![-248146249257, -479868164727, -292469238803, -33975175673, 816086947163] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI23N0
 g := ![-10788967359, -20863833249, -12716053861, -1477181551, 35482041181]
 hmem := by decide

def P23P0 : CertificateIrreducibleZModOfList' 23 5 2 4 [22, 15, 2, 7, 21, 1] where
 m := 1
 P := ![5]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 22, 4, 11, 3], [22, 14, 21, 22, 7], [5, 6, 9, 16, 22], [4, 3, 12, 20, 14], [0, 1]]
 g := ![![[17, 8, 2, 19, 2], [19, 0, 19, 3, 4], [1], []],![[11, 4, 5, 13, 2, 14, 2, 13], [21, 2, 20, 21, 22, 5, 1, 8], [22, 22, 1, 3, 5, 20, 17, 2], [22, 20, 15, 9]],![[9, 14, 14, 0, 17, 12, 11, 22], [4, 4, 4, 4, 21, 0, 10, 15], [0, 3, 10, 16, 12, 1, 9, 20], [7, 5, 15, 3]],![[5, 15, 4, 22, 22, 0, 3, 10], [0, 18, 13, 17, 17, 3, 19, 21], [2, 5, 6, 10, 8, 0, 17, 7], [21, 10, 16, 1]],![[22, 19, 20, 2, 10, 12, 15, 11], [3, 20, 2, 2, 17, 15, 13, 7], [6, 18, 15, 22, 13, 22, 19, 17], [0, 3, 9, 12]]]
 h' := ![![[17, 22, 4, 11, 3], [19, 15, 20, 13, 5], [1, 8, 21, 16, 2], [0, 0, 1], [0, 1]],![[22, 14, 21, 22, 7], [18, 11, 11, 15, 9], [9, 2, 14, 20, 8], [12, 1, 15, 2, 19], [17, 22, 4, 11, 3]],![[5, 6, 9, 16, 22], [2, 11, 20, 14, 6], [5, 3, 7, 16, 9], [8, 10, 11, 10, 4], [22, 14, 21, 22, 7]],![[4, 3, 12, 20, 14], [20, 2, 22, 13, 6], [2, 21, 17, 6, 18], [0, 8, 19, 0, 4], [5, 6, 9, 16, 22]],![[0, 1], [11, 7, 19, 14, 20], [18, 12, 10, 11, 9], [16, 4, 0, 11, 19], [4, 3, 12, 20, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 11, 2, 19], [], [], []]
 b := ![[], [18, 11, 3, 2, 9], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal O 23 where 
  r := 5
  n := 5
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I23N0
  hcard := NI23N0
  P := [22, 15, 2, 7, 21, 1]
  f := ofList [22, 15, 2, 7, 21, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P23P0
  hneq := by decide
  hlen := by decide
  c := ![-248146249257, -479868164727, -292469238803, -33975175673, 816086947163]
  a := ![-27, -35, -61, -9, 115]
  z := ![1, 0, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI23N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI23N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal.isPrime PI23N0
def PBC23 : IsPrimesAboveP 23 ![I23N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    unfold I23N0
    rw [Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
