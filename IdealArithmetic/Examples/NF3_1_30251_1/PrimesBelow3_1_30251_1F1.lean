
import IdealArithmetic.Examples.NF3_1_30251_1.RI3_1_30251_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![17, -15, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![17, -15, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![17, 22, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![17, -15, 1], ![34, 44, -72], ![-476, 50, -28]]]
  hmulB := by decide  
  f := ![![![-16, 15, -1], ![37, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-17, -22, 37]], ![![0, -1, 1], ![34, 44, -72], ![0, 18, -28]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [24, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 36], [0, 1]]
 g := ![![[10, 30], [36], [9, 26], [28], [1]], ![[25, 7], [36], [22, 11], [28], [1]]]
 h' := ![![[19, 36], [23, 20], [6, 31], [15, 27], [13, 19], [0, 1]], ![[0, 1], [33, 17], [3, 6], [10, 10], [4, 18], [19, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [34, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [24, 18, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![568, 500, -243]
  a := ![0, 3, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![127, 158, -243]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-2, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-2, 1, 0]] 
 ![![37, 0, 0], ![35, 1, 0], ![28, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-2, 1, 0], ![0, -4, 5], ![34, -3, 1]]]
  hmulB := by decide  
  f := ![![![47, -23, 0], ![851, 0, 0]], ![![45, -22, 0], ![815, 0, 0]], ![![36, -16, -2], ![652, 15, 0]]]
  g := ![![![1, 0, 0], ![-35, 37, 0], ![-28, 0, 37]], ![![-1, 1, 0], ![0, -4, 5], ![3, -3, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![17, -15, 1]] ![![37, 0, 0], ![-2, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-74, 37, 0]], ![![629, -555, 37], ![0, 74, -74]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-2, 1, 0]]], ![![![17, -15, 1]], ![![0, 2, -2]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-13, -15, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-13, -15, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![28, 26, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-13, -15, 1], ![34, 14, -72], ![-476, 50, -58]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-28, -26, 41]], ![![-1, -1, 1], ![50, 46, -72], ![28, 38, -58]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [1, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 40], [0, 1]]
 g := ![![[4, 1], [20], [16], [26, 16], [1]], ![[0, 40], [20], [16], [3, 25], [1]]]
 h' := ![![[37, 40], [37, 40], [4, 15], [15, 4], [40, 37], [0, 1]], ![[0, 1], [0, 1], [26, 26], [40, 37], [15, 4], [37, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [27, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [1, 4, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![304, 581, -118]
  a := ![-1, -4, 9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![88, 89, -118]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-10, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-10, 1, 0]] 
 ![![41, 0, 0], ![31, 1, 0], ![17, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-10, 1, 0], ![0, -12, 5], ![34, -3, -7]]]
  hmulB := by decide  
  f := ![![![391, -39, 0], ![1599, 0, 0]], ![![301, -30, 0], ![1231, 0, 0]], ![![167, -7, -4], ![683, 33, 0]]]
  g := ![![![1, 0, 0], ![-31, 41, 0], ![-17, 0, 41]], ![![-1, 1, 0], ![7, -12, 5], ![6, -3, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-13, -15, 1]] ![![41, 0, 0], ![-10, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-410, 41, 0]], ![![-533, -615, 41], ![164, 164, -82]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-10, 1, 0]]], ![![![-13, -15, 1]], ![![4, 4, -2]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![12, 1, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![12, 1, 0]] 
 ![![43, 0, 0], ![12, 1, 0], ![19, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![12, 1, 0], ![0, 10, 5], ![34, -3, 15]]]
  hmulB := by decide  
  f := ![![![169, 14, 0], ![-602, 0, 0]], ![![36, 3, 0], ![-128, 0, 0]], ![![73, 0, -3], ![-260, 26, 0]]]
  g := ![![![1, 0, 0], ![-12, 43, 0], ![-19, 0, 43]], ![![0, 1, 0], ![-5, 10, 5], ![-5, -3, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-9, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-9, 1, 0]] 
 ![![43, 0, 0], ![34, 1, 0], ![6, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-9, 1, 0], ![0, -11, 5], ![34, -3, -6]]]
  hmulB := by decide  
  f := ![![![235, -26, 0], ![1118, 0, 0]], ![![190, -21, 0], ![904, 0, 0]], ![![42, 2, -3], ![200, 26, 0]]]
  g := ![![![1, 0, 0], ![-34, 43, 0], ![-6, 0, 43]], ![![-1, 1, 0], ![8, -11, 5], ![4, -3, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1

def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-4, 1, 0]] i)))

def SI43N2: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-4, 1, 0]] 
 ![![43, 0, 0], ![39, 1, 0], ![21, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-4, 1, 0], ![0, -6, 5], ![34, -3, -1]]]
  hmulB := by decide  
  f := ![![![77, -19, 0], ![817, 0, 0]], ![![73, -18, 0], ![775, 0, 0]], ![![43, -7, -3], ![457, 26, 0]]]
  g := ![![![1, 0, 0], ![-39, 43, 0], ![-21, 0, 43]], ![![-1, 1, 0], ![3, -6, 5], ![4, -3, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![12, 1, 0]] ![![43, 0, 0], ![-9, 1, 0]]
  ![![43, 0, 0], ![-13, -17, 1]] where
 M := ![![![1849, 0, 0], ![-387, 43, 0]], ![![516, 43, 0], ![-108, 1, 5]]]
 hmul := by decide  
 g := ![![![![43, 0, 0], ![0, 0, 0]], ![![4, 18, -1], ![43, 0, 0]]], ![![![12, 1, 0], ![0, 0, 0]], ![![-1, 2, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-13, -17, 1]] ![![43, 0, 0], ![-4, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-172, 43, 0]], ![![-559, -731, 43], ![86, 86, -86]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-4, 1, 0]]], ![![![-13, -17, 1]], ![![2, 2, -2]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1, I43N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
    exact isPrimeI43N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0 ⊙ MulI43N1)
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


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [22, 17, 44, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 31, 42], [12, 15, 5], [0, 1]]
 g := ![![[41, 10, 27], [22, 8, 14], [21, 30, 9], [39, 3, 1], []], ![[24, 31, 30, 18], [44, 18, 36, 37], [37, 37, 32, 28], [1, 38, 36, 3], [0, 25]], ![[43, 21, 2, 20], [17, 19, 36, 22], [21, 12, 32, 23], [35, 24, 23, 11], [37, 25]]]
 h' := ![![[38, 31, 42], [33, 31, 36], [8, 20, 25], [35, 23, 44], [0, 0, 1], [0, 1]], ![[12, 15, 5], [38, 36, 9], [20, 39, 40], [8, 42, 28], [34, 20, 15], [38, 31, 42]], ![[0, 1], [20, 27, 2], [42, 35, 29], [18, 29, 22], [35, 27, 31], [12, 15, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44, 33], []]
 b := ![[], [3, 38, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [22, 17, 44, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-84788, 2444, -12361]
  a := ![-64, 1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1804, 52, -263]
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



lemma PB50I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 49 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 49 (by omega)

def PB50I1 : PrimesBelowBoundCertificateInterval O 31 49 50 where
  m := 4
  g := ![2, 2, 3, 1]
  P := ![37, 41, 43, 47]
  hP := PB50I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1, I43N2]
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
    · exact ![1369, 37]
    · exact ![1681, 41]
    · exact ![43, 43, 43]
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
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
      exact NI43N2
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
  β := ![I37N1, I41N1, I43N0, I43N1, I43N2]
  Il := ![[I37N1], [I41N1], [I43N0, I43N1, I43N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
