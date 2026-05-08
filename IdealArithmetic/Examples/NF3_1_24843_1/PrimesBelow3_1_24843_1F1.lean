
import IdealArithmetic.Examples.NF3_1_24843_1.RI3_1_24843_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic

set_option linter.all false

open Classical Polynomial

noncomputable section 
instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}
def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0]] i)))

def SI37N0: IdealEqSpanCertificate timesTableO I37N0
 ![![37, 0, 0]] 
 ![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]]]
  hmulB := by decide
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 50653 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI37N0)

def MemCI37N0 : IdealMemCertificate B I37N0
  ![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]] ![-8066, 0, -888] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI37N0
 g := ![-218, 0, -24]
 hmem := by decide

def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [10, 23, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 9, 36], [3, 27, 1], [0, 1]]
 g := ![![[4, 4, 7], [26, 9], [32, 16, 11], [0, 1], []],![[0, 23, 22, 10], [36, 3], [0, 17, 30, 9], [30, 26], [19, 1]],![[30, 21, 25, 1], [29, 28], [35, 32, 35, 25], [27, 7], [17, 1]]]
 h' := ![![[34, 9, 36], [20, 29, 9], [13, 29, 3], [0, 27, 14], [0, 0, 1], [0, 1]],![[3, 27, 1], [6, 7, 29], [12, 16, 15], [12, 0, 18], [4, 17, 27], [34, 9, 36]],![[0, 1], [27, 1, 36], [24, 29, 19], [10, 10, 5], [24, 20, 9], [3, 27, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28, 35], []]
 b := ![[], [19, 12, 35], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal O 37 where 
  r := 3
  n := 3
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I37N0
  hcard := NI37N0
  P := [10, 23, 0, 1]
  f := ofList [10, 23, 0, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P37P0
  hneq := by decide
  hlen := by decide
  c := ![-8066, 0, -888]
  a := ![1, 0, -3]
  z := ![1, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI37N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI37N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal.isPrime PI37N0
def PBC37 : IsPrimesAboveP 37 ![I37N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    unfold I37N0
    rw [Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}
def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![13, -17, 1]] i)))

def SI41N0: IdealEqSpanCertificate timesTableO I41N0
 ![![41, 0, 0], ![13, -17, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![13, 24, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![13, -17, 1], ![47, 30, -50], ![-490, 10, -3]]]
  hmulB := by decide
  f := ![![![-12, 17, -1], ![41, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-13, -24, 41]], ![![0, -1, 1], ![17, 30, -50], ![-11, 2, -3]]]
  hle1 := by decide
  hle2 := by decide

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI41N0)

def MemCI41N0 : IdealMemCertificate B I41N0
  ![![41, 0, 0], ![0, 41, 0], ![13, 24, 1]] ![-1161, 550, 163] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI41N0
 g := ![-80, -82, 163]
 hmem := by decide

def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [32, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 40], [0, 1]]
 g := ![![[7, 9], [20], [39], [15, 33], [1]],![[0, 32], [20], [39], [3, 8], [1]]]
 h' := ![![[22, 40], [25, 38], [3, 15], [12, 11], [9, 22], [0, 1]],![[0, 1], [0, 3], [5, 26], [8, 30], [1, 19], [22, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [33, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal O 41 where 
  r := 3
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I41N0
  hcard := NI41N0
  P := [32, 19, 1]
  f := ofList [32, 19, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P41P0
  hneq := by decide
  hlen := by decide
  c := ![-1161, 550, 163]
  a := ![-3, -5, 8]
  z := ![1, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI41N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI41N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal.isPrime PI41N0
def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![9, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate timesTableO I41N1
 ![![41, 0, 0], ![9, 1, 0]] 
 ![![41, 0, 0], ![9, 1, 0], ![3, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![9, 1, 0], ![-1, 8, 3], ![30, 0, 10]]]
  hmulB := by decide
  f := ![![![-1279, 10240, 3840], ![0, -52480, 0]], ![![-280, 2240, 840], ![1, -11480, 0]], ![![-96, 749, 281], ![11, -3840, 0]]]
  g := ![![![1, 0, 0], ![-9, 41, 0], ![-3, 0, 41]], ![![0, 1, 0], ![-2, 8, 3], ![0, 0, 10]]]
  hle1 := by decide
  hle2 := by decide

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulEqCertificate timesTableO (I41N0) I41N1
  ![![41, 0, 0], ![13, -17, 1]] ![![41, 0, 0], ![9, 1, 0]]
  ![![41, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![1681, 0, 0], ![369, 41, 0]], ![![533, -697, 41], ![164, -123, -41]]]
 hmul := by decide
 f :=  ![![![![414669145, -3334659176, -1250412772], ![9691820, 17088966720, 0]], ![![23492, 0, 0], ![0, 0, 0]]]]
 g :=  ![![![![41, 0, 0]], ![![9, 1, 0]]], ![![![13, -17, 1]], ![![4, -3, -1]]]]
 hle1 := by decide
 hle2 := by decide

def PBC41 : IsPrimesAboveP 41 ![I41N0, I41N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI41N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}
def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0]] i)))

def SI43N0: IdealEqSpanCertificate timesTableO I43N0
 ![![43, 0, 0]] 
 ![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]]]
  hmulB := by decide
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 79507 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI43N0)

def MemCI43N0 : IdealMemCertificate B I43N0
  ![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]] ![-93767133, -1684998, -8392869] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI43N0
 g := ![-2180631, -39186, -195183]
 hmem := by decide

def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [24, 29, 21, 1] where
 m := 1
 P := ![3]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 3, 1], [21, 39, 42], [0, 1]]
 g := ![![[34, 17, 40], [29, 9, 9], [5, 31], [25, 22, 1], []],![[35, 26, 33, 17], [5, 5, 0, 11], [12, 15], [36, 20, 31, 16], [28, 1]],![[15, 3, 29, 8], [8, 4, 39, 26], [35, 24], [1, 25, 32, 34], [30, 1]]]
 h' := ![![[1, 3, 1], [35, 15, 30], [13, 33, 3], [2, 37, 17], [0, 0, 1], [0, 1]],![[21, 39, 42], [1, 42, 24], [11, 17, 21], [27, 19, 12], [17, 30, 39], [1, 3, 1]],![[0, 1], [21, 29, 32], [41, 36, 19], [35, 30, 14], [22, 13, 3], [21, 39, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24, 1], []]
 b := ![[], [27, 0, 42], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal O 43 where 
  r := 3
  n := 3
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I43N0
  hcard := NI43N0
  P := [24, 29, 21, 1]
  f := ofList [24, 29, 21, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P43P0
  hneq := by decide
  hlen := by decide
  c := ![-93767133, -1684998, -8392869]
  a := ![1, 2, -67]
  z := ![1, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI43N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI43N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal.isPrime PI43N0
def PBC43 : IsPrimesAboveP 43 ![I43N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    unfold I43N0
    rw [Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl

