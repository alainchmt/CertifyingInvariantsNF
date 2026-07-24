
import IdealArithmetic.Examples.NF3_1_36579_1.RI3_1_36579_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 2, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![-1, 2, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![36, 2, 1]] where
  M :=![![![-1, 2, 1], ![-40, 6, 3], ![-120, -19, 9]]]
  hmulB := by decide  
  f := ![![![3, -1, 0]], ![![0, 3, -1]], ![![4, -1, 0]]]
  g := ![![![-1, 0, 1], ![-4, 0, 3], ![-12, -1, 9]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [2, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 36], [0, 1]]
 g := ![![[2, 1], [11], [21, 10], [16], [1]], ![[35, 36], [11], [18, 27], [16], [1]]]
 h' := ![![[33, 36], [3, 1], [32, 14], [9, 26], [35, 33], [0, 1]], ![[0, 1], [36, 36], [13, 23], [16, 11], [14, 4], [33, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [18, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [2, 4, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-118, -23, 7]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10, -1, 7]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-3, 1, 0]] 
 ![![37, 0, 0], ![34, 1, 0], ![28, 0, 1]] where
  M :=![![![-3, 1, 0], ![0, -3, 1], ![-40, 7, -2]]]
  hmulB := by decide  
  f := ![![![1, -2, -1]], ![![2, -2, -1]], ![![4, -1, -1]]]
  g := ![![![-1, 1, 0], ![2, -3, 1], ![-6, 7, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![-1, 2, 1]] ![![-3, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![-37, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![20647, -9138, 1929]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![20647, -9138, 1929]] 
 ![![41, 0, 0], ![0, 41, 0], ![12, 23, 1]] where
  M :=![![![20647, -9138, 1929], ![-77160, 34150, -7209], ![288360, -127623, 26941]]]
  hmulB := by decide  
  f := ![![![23, 51, 12]], ![![-480, 107, 63]], ![![-324, 74, 43]]]
  g := ![![![-61, -1305, 1929], ![228, 4877, -7209], ![-852, -18226, 26941]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [5, 40, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 40], [0, 1]]
 g := ![![[8, 33], [16], [39], [32, 1], [1]], ![[0, 8], [16], [39], [33, 40], [1]]]
 h' := ![![[1, 40], [22, 19], [26, 4], [4, 11], [36, 1], [0, 1]], ![[0, 1], [0, 22], [30, 37], [15, 30], [37, 40], [1, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [28, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [5, 40, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![86, -457, 178]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-50, -111, 178]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 51, 12]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![23, 51, 12]] 
 ![![41, 0, 0], ![17, 1, 0], ![39, 0, 1]] where
  M :=![![![23, 51, 12], ![-480, 107, 63], ![-2520, -39, 170]]]
  hmulB := by decide  
  f := ![![![20647, -9138, 1929]], ![![6679, -2956, 624]], ![![26673, -11805, 2492]]]
  g := ![![![-32, 51, 12], ![-116, 107, 63], ![-207, -39, 170]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![20647, -9138, 1929]] ![![23, 51, 12]]
  ![![41, 0, 0]] where
 M := ![![![41, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0]] 
 ![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [2, 28, 34, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 35, 30], [17, 7, 13], [0, 1]]
 g := ![![[4, 33, 17], [8, 34, 40], [22, 21], [10, 9, 1], []], ![[12, 3, 22, 8], [40, 9, 41, 7], [4, 31], [17, 32, 0, 8], [9, 40]], ![[8, 36, 32, 23], [16, 1, 17, 21], [31, 23], [33, 11, 33, 15], [26, 40]]]
 h' := ![![[35, 35, 30], [27, 24, 19], [12, 39, 30], [23, 3, 8], [0, 0, 1], [0, 1]], ![[17, 7, 13], [21, 17, 36], [5, 18, 4], [23, 21, 17], [3, 11, 7], [35, 35, 30]], ![[0, 1], [36, 2, 31], [2, 29, 9], [35, 19, 18], [22, 32, 35], [17, 7, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13], []]
 b := ![[], [30, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [2, 28, 34, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-132870, 16039, -9159]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3090, 373, -213]
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


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [19, 25, 41, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 10, 2], [46, 36, 45], [0, 1]]
 g := ![![[12, 27, 16], [6, 35, 8], [22, 15, 34], [11, 6, 1], []], ![[44, 24, 24, 36], [0, 28, 1, 24], [33, 1, 2, 36], [11, 35, 28, 7], [17, 4]], ![[34, 16, 40, 19], [1, 45, 14, 35], [17, 19, 37, 33], [14, 28, 39, 35], [21, 4]]]
 h' := ![![[7, 10, 2], [27, 9, 4], [5, 29, 33], [26, 34, 38], [0, 0, 1], [0, 1]], ![[46, 36, 45], [28, 9, 21], [2, 33, 24], [4, 17, 26], [8, 15, 36], [7, 10, 2]], ![[0, 1], [24, 29, 22], [2, 32, 37], [2, 43, 30], [25, 32, 10], [46, 36, 45]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45, 27], []]
 b := ![[], [19, 37, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [19, 25, 41, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-40514, -705, 2115]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-862, -15, 45]
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


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [51, 23, 16, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 5, 27], [33, 47, 26], [0, 1]]
 g := ![![[2, 25, 43], [23, 25], [44, 41, 1], [32, 44], [1]], ![[21, 3, 20, 26], [17, 13], [34, 43, 26, 39], [49, 25], [44, 3, 15, 20]], ![[36, 29, 15, 19], [44, 29], [52, 36, 44, 45], [52, 15], [45, 7, 24, 33]]]
 h' := ![![[4, 5, 27], [52, 44, 34], [35, 37, 5], [15, 2, 1], [2, 30, 37], [0, 1]], ![[33, 47, 26], [45, 20, 30], [8, 34, 15], [41, 1, 48], [46, 29, 5], [4, 5, 27]], ![[0, 1], [29, 42, 42], [43, 35, 33], [8, 50, 4], [40, 47, 11], [33, 47, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 44], []]
 b := ![[], [49, 2, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [51, 23, 16, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1749, 212, 212]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-33, 4, 4]
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



lemma PB55I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 54 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 54 (by omega)

def PB55I1 : PrimesBelowBoundCertificateInterval O 31 54 55 where
  m := 5
  g := ![2, 2, 1, 1, 1]
  P := ![37, 41, 43, 47, 53]
  hP := PB55I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
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
    · exact ![1369, 37]
    · exact ![1681, 41]
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
      exact NI37N1
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
  β := ![I37N1, I41N1]
  Il := ![[I37N1], [I41N1], [], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
