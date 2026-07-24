
import IdealArithmetic.Examples.NF3_1_35075_1.RI3_1_35075_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0]] 
 ![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [7, 23, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 11, 34], [26, 25, 3], [0, 1]]
 g := ![![[21, 7, 27], [5, 34], [18, 27, 9], [27, 1], []], ![[21, 26, 15, 1], [34, 3], [34, 6, 5, 25], [12, 33], [29, 9]], ![[9, 28, 5, 9], [28, 36], [5, 23, 14, 3], [10, 10], [23, 9]]]
 h' := ![![[1, 11, 34], [5, 15, 8], [22, 5, 16], [33, 1, 3], [0, 0, 1], [0, 1]], ![[26, 25, 3], [32, 14, 7], [14, 12, 15], [20, 33, 35], [20, 32, 25], [1, 11, 34]], ![[0, 1], [1, 8, 22], [30, 20, 6], [13, 3, 36], [34, 5, 11], [26, 25, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33, 27], []]
 b := ![[], [29, 20, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [7, 23, 10, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1554, 3108, -4847]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![42, 84, -131]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 50653 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def PBC37 : ContainsPrimesAboveP 37 ![I37N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![37, 0, 0]]) timesTableT_eq_Table B_one_repr 37 (by decide) 𝕀

instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 2, -2]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![-1, 2, -2]] 
 ![![41, 0, 0], ![5, 1, 0], ![26, 0, 1]] where
  M :=![![![-1, 2, -2], ![-68, 23, 4], ![102, -56, 21]]]
  hmulB := by decide  
  f := ![![![707, 70, 54]], ![![131, 13, 10]], ![![484, 48, 37]]]
  g := ![![![1, 2, -2], ![-7, 23, 4], ![-4, -56, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 1, 1]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![13, 1, 1]] 
 ![![41, 0, 0], ![8, 1, 0], ![5, 0, 1]] where
  M :=![![![13, 1, 1], ![34, 3, 2], ![17, 6, 2]]]
  hmulB := by decide  
  f := ![![![-6, 4, -1]], ![![-2, 1, 0]], ![![3, -1, 0]]]
  g := ![![![0, 1, 1], ![0, 3, 2], ![-1, 6, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-40, -4, -3]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![-40, -4, -3]] 
 ![![41, 0, 0], ![27, 1, 0], ![32, 0, 1]] where
  M :=![![![-40, -4, -3], ![-102, -11, -8], ![-85, -7, -7]]]
  hmulB := by decide  
  f := ![![![-21, 7, 1]], ![![-13, 4, 1]], ![![-11, 4, 0]]]
  g := ![![![4, -4, -3], ![11, -11, -8], ![8, -7, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![-1, 2, -2]] ![![13, 1, 1]]
  ![![21, -7, -1]] where
 M := ![![![21, -7, -1]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![21, -7, -1]] ![![-40, -4, -3]]
  ![![41, 0, 0]] where
 M := ![![![-41, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1, I41N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
    exact isPrimeI41N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0 ⊙ MulI41N1)
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


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [30, 20, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 22, 17], [4, 20, 26], [0, 1]]
 g := ![![[6, 23, 4], [9, 6, 23], [32, 13], [39, 39, 1], []], ![[2, 3, 11, 6], [8, 12, 25, 16], [25, 14], [38, 20, 20, 6], [22, 31]], ![[28, 35, 34, 39], [30, 5, 17, 7], [37, 40], [12, 14, 31, 28], [13, 31]]]
 h' := ![![[35, 22, 17], [31, 1, 41], [24, 14, 25], [34, 28, 23], [0, 0, 1], [0, 1]], ![[4, 20, 26], [11, 26, 20], [19, 0, 7], [34, 11, 33], [6, 41, 20], [35, 22, 17]], ![[0, 1], [9, 16, 25], [18, 29, 11], [15, 4, 30], [13, 2, 22], [4, 20, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27, 20], []]
 b := ![[], [42, 27, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [30, 20, 4, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![31089, -17673, 7912]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![723, -411, 184]
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


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [23, 22, 29, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 3, 2], [13, 43, 45], [0, 1]]
 g := ![![[10, 28, 14], [32, 41, 36], [3, 11, 3], [20, 18, 1], []], ![[16, 7, 29, 14], [32, 44, 11, 34], [44, 21, 36, 27], [19, 16, 23, 32], [37, 4]], ![[6, 2, 7, 44], [29, 7, 19, 31], [3, 38, 13, 46], [23, 8, 32, 29], [41, 4]]]
 h' := ![![[5, 3, 2], [16, 12, 22], [25, 16, 6], [10, 39, 35], [0, 0, 1], [0, 1]], ![[13, 43, 45], [46, 34, 30], [37, 9, 8], [12, 7, 32], [20, 17, 43], [5, 3, 2]], ![[0, 1], [17, 1, 42], [7, 22, 33], [29, 1, 27], [25, 30, 3], [13, 43, 45]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 10], []]
 b := ![[], [20, 43, 42], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [23, 22, 29, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-142739, -2397, -6909]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3037, -51, -147]
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

instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0]] 
 ![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [8, 30, 48, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [26, 9, 17], [32, 43, 36], [0, 1]]
 g := ![![[10, 41, 7], [11, 17], [14, 34, 47], [37, 25], [1]], ![[21, 27, 37, 6], [39, 29], [51, 7, 47, 49], [49, 52], [28, 48, 38, 37]], ![[7, 8, 18, 44], [43, 38], [2, 20, 23, 28], [6, 42], [47, 43, 49, 16]]]
 h' := ![![[26, 9, 17], [1, 17, 22], [47, 26, 21], [33, 18, 43], [45, 23, 5], [0, 1]], ![[32, 43, 36], [17, 29, 16], [8, 0, 20], [49, 16, 35], [21, 15, 23], [26, 9, 17]], ![[0, 1], [42, 7, 15], [11, 27, 12], [33, 19, 28], [9, 15, 25], [32, 43, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38, 30], []]
 b := ![[], [23, 1, 45], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [8, 30, 48, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-26977, 37789, -31058]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-509, 713, -586]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 148877 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def PBC53 : ContainsPrimesAboveP 53 ![I53N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![53, 0, 0]]) timesTableT_eq_Table B_one_repr 53 (by decide) 𝕀



lemma PB54I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 53 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 53 (by omega)

def PB54I1 : PrimesBelowBoundCertificateInterval O 31 53 54 where
  m := 5
  g := ![1, 3, 1, 1, 1]
  P := ![37, 41, 43, 47, 53]
  hP := PB54I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0]
    · exact ![I47N0]
    · exact ![I53N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
    · exact PBC53
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![50653]
    · exact ![41, 41, 41]
    · exact ![79507]
    · exact ![103823]
    · exact ![148877]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
      exact NI41N2
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
  β := ![I41N0, I41N1, I41N2]
  Il := ![[], [I41N0, I41N1, I41N2], [], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
