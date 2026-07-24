
import IdealArithmetic.Examples.NF3_1_117720_1.RI3_1_117720_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![3, -15, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![3, -15, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![3, 68, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![3, -15, 1], ![38, -24, -15], ![-570, 443, -24]]]
  hmulB := by decide  
  f := ![![![-2, 15, -1], ![83, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-3, -68, 83]], ![![0, -1, 1], ![1, 12, -15], ![-6, 25, -24]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [57, 68, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 82], [0, 1]]
 g := ![![[74, 38], [74, 48], [78], [27], [5, 59], [1]], ![[63, 45], [47, 35], [78], [27], [60, 24], [1]]]
 h' := ![![[15, 82], [15, 72], [72, 52], [6, 59], [47, 44], [26, 15], [0, 1]], ![[0, 1], [16, 11], [22, 31], [61, 24], [43, 39], [2, 68], [15, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [78, 56]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [57, 68, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![133, -84, -94]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5, 76, -94]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![15, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![15, 1, 0]] 
 ![![83, 0, 0], ![15, 1, 0], ![24, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![15, 1, 0], ![0, 15, 1], ![38, -27, 15]]]
  hmulB := by decide  
  f := ![![![751, 50, 0], ![-4150, 0, 0]], ![![135, 9, 0], ![-746, 0, 0]], ![![198, 13, 0], ![-1094, 1, 0]]]
  g := ![![![1, 0, 0], ![-15, 83, 0], ![-24, 0, 83]], ![![0, 1, 0], ![-3, 15, 1], ![1, -27, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![3, -15, 1]] ![![83, 0, 0], ![15, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![1245, 83, 0]], ![![249, -1245, 83], ![83, -249, 0]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![15, 1, 0]]], ![![![3, -15, 1]], ![![1, -3, 0]]]]
 hle2 := by decide  


def PBC83 : ContainsPrimesAboveP 83 ![I83N0, I83N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 83 (by decide) (𝕀 ⊙ MulI83N0)
instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![23, 21, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![23, 21, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![23, 21, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![23, 21, 1], ![38, -4, 21], ![798, -529, -4]]]
  hmulB := by decide  
  f := ![![![-22, -21, -1], ![89, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-23, -21, 89]], ![![0, 0, 1], ![-5, -5, 21], ![10, -5, -4]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [28, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [68, 88], [0, 1]]
 g := ![![[23, 81], [44], [85], [83, 85], [14, 85], [1]], ![[13, 8], [44], [85], [78, 4], [9, 4], [1]]]
 h' := ![![[68, 88], [13, 80], [34, 20], [79, 21], [53, 68], [61, 68], [0, 1]], ![[0, 1], [24, 9], [59, 69], [83, 68], [49, 21], [57, 21], [68, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43]]
 b := ![[], [70, 66]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [28, 21, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-448, 628, -182]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![42, 50, -182]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-21, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-21, 1, 0]] 
 ![![89, 0, 0], ![68, 1, 0], ![4, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-21, 1, 0], ![0, -21, 1], ![38, -27, -21]]]
  hmulB := by decide  
  f := ![![![526, -25, 0], ![2225, 0, 0]], ![![400, -19, 0], ![1692, 0, 0]], ![![26, -1, 0], ![110, 1, 0]]]
  g := ![![![1, 0, 0], ![-68, 89, 0], ![-4, 0, 89]], ![![-1, 1, 0], ![16, -21, 1], ![22, -27, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![23, 21, 1]] ![![89, 0, 0], ![-21, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-1869, 89, 0]], ![![2047, 1869, 89], ![-445, -445, 0]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-21, 1, 0]]], ![![![23, 21, 1]], ![![-5, -5, 0]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-4, 39, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-4, 39, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![93, 39, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-4, 39, 1], ![38, -31, 39], ![1482, -1015, -31]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-93, -39, 97]], ![![-1, 0, 1], ![-37, -16, 39], ![45, 2, -31]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [29, 47, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [50, 96], [0, 1]]
 g := ![![[15, 94], [35], [22], [85], [79], [50, 1]], ![[59, 3], [35], [22], [85], [79], [3, 96]]]
 h' := ![![[50, 96], [61, 26], [94, 61], [21, 33], [62, 45], [5, 46], [0, 1]], ![[0, 1], [3, 71], [40, 36], [22, 64], [81, 52], [74, 51], [50, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [90]]
 b := ![[], [39, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [29, 47, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1041, 11, 55]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-42, -22, 55]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-39, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-39, 1, 0]] 
 ![![97, 0, 0], ![58, 1, 0], ![31, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-39, 1, 0], ![0, -39, 1], ![38, -27, -39]]]
  hmulB := by decide  
  f := ![![![352, -9, 0], ![873, 0, 0]], ![![196, -5, 0], ![486, 0, 0]], ![![172, -4, 0], ![427, 1, 0]]]
  g := ![![![1, 0, 0], ![-58, 97, 0], ![-31, 0, 97]], ![![-1, 1, 0], ![23, -39, 1], ![29, -27, -39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![-4, 39, 1]] ![![97, 0, 0], ![-39, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![-3783, 97, 0]], ![![-388, 3783, 97], ![194, -1552, 0]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![-39, 1, 0]]], ![![![-4, 39, 1]], ![![2, -16, 0]]]]
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


lemma PB98I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 97 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 97 (by omega)

def PB98I2 : PrimesBelowBoundCertificateInterval O 79 97 98 where
  m := 3
  g := ![2, 2, 2]
  P := ![83, 89, 97]
  hP := PB98I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
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
    · exact ![6889, 83]
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
      exact NI83N1
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
  β := ![I83N1, I89N1, I97N1]
  Il := ![[I83N1], [I89N1], [I97N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
