
import IdealArithmetic.Examples.NF3_1_120204_1.RI3_1_120204_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0]] 
 ![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [54, 22, 71, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [73, 82, 52], [22, 0, 31], [0, 1]]
 g := ![![[34, 82, 48], [35, 19, 31], [56, 21], [53, 7], [39, 12, 1], []], ![[43, 73, 35, 42], [1, 18, 22, 20], [36, 40], [22, 23], [12, 8], [57, 48]], ![[1, 28, 80, 9], [34, 12, 31, 40], [49, 78], [25, 78], [69, 66, 42, 31], [78, 48]]]
 h' := ![![[73, 82, 52], [19, 67, 31], [28, 23, 23], [8, 30, 41], [52, 71, 67], [0, 0, 1], [0, 1]], ![[22, 0, 31], [74, 17, 81], [28, 42, 34], [35, 57, 66], [12, 57, 40], [10, 75], [73, 82, 52]], ![[0, 1], [50, 82, 54], [31, 18, 26], [42, 79, 59], [8, 38, 59], [7, 8, 82], [22, 0, 31]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2], []]
 b := ![[], [19, 67], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [54, 22, 71, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8964, 664, -415]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![108, 8, -5]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 571787 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def PBC83 : ContainsPrimesAboveP 83 ![I83N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![83, 0, 0]]) timesTableT_eq_Table B_one_repr 83 (by decide) 𝕀

instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-17, -17, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-17, -17, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![72, 72, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-17, -17, 1], ![66, -23, -51], ![-1122, 124, -23]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-72, -72, 89]], ![![-1, -1, 1], ![42, 41, -51], ![6, 20, -23]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [15, 71, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 88], [0, 1]]
 g := ![![[70, 64], [47], [8], [38, 5], [41, 57], [1]], ![[65, 25], [47], [8], [39, 84], [88, 32], [1]]]
 h' := ![![[18, 88], [12, 81], [19, 15], [53, 50], [8, 19], [74, 18], [0, 1]], ![[0, 1], [46, 8], [22, 74], [63, 39], [83, 70], [42, 71], [18, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31]]
 b := ![[], [83, 60]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [15, 71, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-847, 132, 165]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-143, -132, 165]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-38, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-38, 1, 0]] 
 ![![89, 0, 0], ![51, 1, 0], ![23, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-38, 1, 0], ![0, -38, 3], ![66, -6, -38]]]
  hmulB := by decide  
  f := ![![![3345, -88, 0], ![7832, 0, 0]], ![![1939, -51, 0], ![4540, 0, 0]], ![![867, -10, -1], ![2030, 30, 0]]]
  g := ![![![1, 0, 0], ![-51, 89, 0], ![-23, 0, 89]], ![![-1, 1, 0], ![21, -38, 3], ![14, -6, -38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-17, -17, 1]] ![![89, 0, 0], ![-38, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-3382, 89, 0]], ![![-1513, -1513, 89], ![712, 623, -89]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-38, 1, 0]]], ![![![-17, -17, 1]], ![![8, 7, -1]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0)
instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-43, 4, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-43, 4, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![54, 4, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-43, 4, 1], ![66, -49, 12], ![264, -2, -49]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-54, -4, 97]], ![![-1, 0, 1], ![-6, -1, 12], ![30, 2, -49]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [94, 80, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 96], [0, 1]]
 g := ![![[38, 32], [2], [4], [96], [1], [17, 1]], ![[0, 65], [2], [4], [96], [1], [34, 96]]]
 h' := ![![[17, 96], [18, 56], [20, 83], [28, 2], [82, 22], [51, 1], [0, 1]], ![[0, 1], [0, 41], [73, 14], [62, 95], [68, 75], [68, 96], [17, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [89, 58]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [94, 80, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1062, -14, 45]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-36, -2, 45]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-12, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-12, 1, 0]] 
 ![![97, 0, 0], ![85, 1, 0], ![49, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-12, 1, 0], ![0, -12, 3], ![66, -6, -12]]]
  hmulB := by decide  
  f := ![![![1093, -91, 0], ![8827, 0, 0]], ![![961, -80, 0], ![7761, 0, 0]], ![![565, -39, -2], ![4563, 65, 0]]]
  g := ![![![1, 0, 0], ![-85, 97, 0], ![-49, 0, 97]], ![![-1, 1, 0], ![9, -12, 3], ![12, -6, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![-43, 4, 1]] ![![97, 0, 0], ![-12, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![-1164, 97, 0]], ![![-4171, 388, 97], ![582, -97, 0]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![-12, 1, 0]]], ![![![-43, 4, 1]], ![![6, -1, 0]]]]
 hle2 := by decide  


def PBC97 : ContainsPrimesAboveP 97 ![I97N0, I97N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
    exact isPrimeI97N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 97 (by decide) (𝕀 ⊙ MulI97N0)


lemma PB99I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 98 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 98 (by omega)

def PB99I2 : PrimesBelowBoundCertificateInterval O 79 98 99 where
  m := 3
  g := ![1, 2, 2]
  P := ![83, 89, 97]
  hP := PB99I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC83
    · exact PBC89
    · exact PBC97
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![571787]
    · exact ![7921, 89]
    · exact ![9409, 97]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
  β := ![I89N1, I97N1]
  Il := ![[], [I89N1], [I97N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
