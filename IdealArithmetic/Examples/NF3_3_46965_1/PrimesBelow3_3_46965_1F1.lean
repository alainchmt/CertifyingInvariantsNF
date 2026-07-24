
import IdealArithmetic.Examples.NF3_3_46965_1.RI3_3_46965_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![340, 650, 271]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![340, 650, 271]] 
 ![![37, 0, 0], ![18, 1, 0], ![3, 0, 1]] where
  M :=![![![340, 650, 271], ![2439, 4676, 1950], ![5850, 11213, 4676]]]
  hmulB := by decide  
  f := ![![![-374, -677, 304]], ![![-108, -208, 93]], ![![-195, -323, 146]]]
  g := ![![![-329, 650, 271], ![-2367, 4676, 1950], ![-5676, 11213, 4676]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-230, -4, 15]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-230, -4, 15]] 
 ![![37, 0, 0], ![20, 1, 0], ![27, 0, 1]] where
  M :=![![![-230, -4, 15], ![135, 10, -12], ![-36, -19, 10]]]
  hmulB := by decide  
  f := ![![![-128, -245, -102]], ![![-94, -180, -75]], ![![-153, -293, -122]]]
  g := ![![![-15, -4, 15], ![7, 10, -12], ![2, -19, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-62, -1, 4]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![-62, -1, 4]] 
 ![![37, 0, 0], ![36, 1, 0], ![12, 0, 1]] where
  M :=![![![-62, -1, 4], ![36, 2, -3], ![-9, -4, 2]]]
  hmulB := by decide  
  f := ![![![-8, -14, -5]], ![![-9, -16, -6]], ![![-6, -11, -4]]]
  g := ![![![-2, -1, 4], ![0, 2, -3], ![3, -4, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![340, 650, 271]] ![![-230, -4, 15]]
  ![![-206, -9, 10]] where
 M := ![![![-206, -9, 10]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![-206, -9, 10]] ![![-62, -1, 4]]
  ![![37, 0, 0]] where
 M := ![![![12358, 148, -777]]]
 hmul := by decide  
 g := ![![![![334, 4, -21]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1, I37N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
    exact isPrimeI37N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0 ⊙ MulI37N1)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0]] 
 ![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [33, 17, 32, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 33, 5], [33, 7, 36], [0, 1]]
 g := ![![[38, 31, 1], [39, 8], [1, 31], [23, 9, 1], []], ![[27, 23, 35, 32], [8, 25], [7, 5], [16, 34, 31, 40], [22, 25]], ![[4, 40, 31, 40], [31, 21], [18, 23], [16, 22, 38, 8], [32, 25]]]
 h' := ![![[17, 33, 5], [29, 30, 40], [39, 17, 34], [20, 9, 21], [0, 0, 1], [0, 1]], ![[33, 7, 36], [33, 1, 20], [25, 34, 36], [16, 33, 28], [14, 5, 7], [17, 33, 5]], ![[0, 1], [2, 10, 22], [0, 31, 12], [26, 40, 33], [33, 36, 33], [33, 7, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 14], []]
 b := ![[], [25, 3, 30], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [33, 17, 32, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![123, 164, 164]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3, 4, 4]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 68921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def PBC41 : ContainsPrimesAboveP 41 ![I41N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![41, 0, 0]]) timesTableT_eq_Table B_one_repr 41 (by decide) 𝕀

instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0]] 
 ![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [20, 21, 36, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 40, 10], [21, 2, 33], [0, 1]]
 g := ![![[5, 21, 17], [19, 27, 21], [41, 24], [28, 7, 1], []], ![[24, 30, 14, 41], [26, 12, 5, 23], [14, 4], [22, 34, 25, 40], [38, 14]], ![[2, 5, 16, 8], [18, 36, 33, 5], [31, 15], [6, 4, 32, 39], [15, 14]]]
 h' := ![![[29, 40, 10], [7, 11, 19], [41, 29, 35], [42, 3, 29], [0, 0, 1], [0, 1]], ![[21, 2, 33], [16, 1, 19], [19, 39, 16], [27, 18, 2], [38, 38, 2], [29, 40, 10]], ![[0, 1], [36, 31, 5], [38, 18, 35], [23, 22, 12], [12, 5, 40], [21, 2, 33]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 41], []]
 b := ![[], [15, 3, 26], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [20, 21, 36, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10793, -16641, 13158]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-251, -387, 306]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 79507 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def PBC43 : ContainsPrimesAboveP 43 ![I43N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![43, 0, 0]]) timesTableT_eq_Table B_one_repr 43 (by decide) 𝕀

instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0]] 
 ![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [17, 28, 36, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 16, 2], [31, 30, 45], [0, 1]]
 g := ![![[15, 27, 27], [30, 11, 18], [36, 39, 2], [46, 11, 1], []], ![[39, 37, 6, 27], [18, 29, 30, 17], [44, 24, 44, 7], [4, 10, 7, 14], [14, 4]], ![[38, 24, 13, 15], [1, 41, 27, 39], [41, 23, 6, 10], [0, 19, 33, 5], [18, 4]]]
 h' := ![![[27, 16, 2], [7, 8, 36], [46, 28, 21], [17, 29, 40], [0, 0, 1], [0, 1]], ![[31, 30, 45], [39, 8, 15], [21, 2, 28], [42, 33, 36], [21, 28, 30], [27, 16, 2]], ![[0, 1], [6, 31, 43], [5, 17, 45], [44, 32, 18], [44, 19, 16], [31, 30, 45]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21, 29], []]
 b := ![[], [46, 11, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [17, 28, 36, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-113223, 12925, -11045]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2409, 275, -235]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 103823 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def PBC47 : ContainsPrimesAboveP 47 ![I47N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![47, 0, 0]]) timesTableT_eq_Table B_one_repr 47 (by decide) 𝕀



lemma PB49I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 48 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 48 (by omega)

def PB49I1 : PrimesBelowBoundCertificateInterval O 31 48 49 where
  m := 4
  g := ![3, 1, 1, 1]
  P := ![37, 41, 43, 47]
  hP := PB49I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0]
    · exact ![I43N0]
    · exact ![I47N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![37, 37, 37]
    · exact ![68921]
    · exact ![79507]
    · exact ![103823]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
      exact NI37N2
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
  β := ![I37N0, I37N1, I37N2]
  Il := ![[I37N0, I37N1, I37N2], [], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
