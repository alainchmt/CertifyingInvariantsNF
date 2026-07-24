
import IdealArithmetic.Examples.NF3_1_117288_3.RI3_1_117288_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![46, 23, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![46, 23, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![46, 23, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![46, 23, 1], ![62, 31, 23], ![1426, -283, 31]]]
  hmulB := by decide  
  f := ![![![-45, -23, -1], ![83, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-46, -23, 83]], ![![0, 0, 1], ![-12, -6, 23], ![0, -12, 31]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [25, 82, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 82], [0, 1]]
 g := ![![[73, 10], [81, 31], [44], [70], [34, 1], [1]], ![[0, 73], [29, 52], [44], [70], [35, 82], [1]]]
 h' := ![![[1, 82], [50, 33], [48, 23], [61, 25], [63, 53], [58, 1], [0, 1]], ![[0, 1], [0, 50], [71, 60], [3, 58], [33, 30], [59, 82], [1, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [57, 52]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [25, 82, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![149, -50, -96]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![55, 26, -96]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-23, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-23, 1, 0]] 
 ![![83, 0, 0], ![60, 1, 0], ![52, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-23, 1, 0], ![0, -23, 1], ![62, -15, -23]]]
  hmulB := by decide  
  f := ![![![1680, -73, 0], ![6059, 0, 0]], ![![1220, -53, 0], ![4400, 0, 0]], ![![1042, -45, 0], ![3758, 1, 0]]]
  g := ![![![1, 0, 0], ![-60, 83, 0], ![-52, 0, 83]], ![![-1, 1, 0], ![16, -23, 1], ![26, -15, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![46, 23, 1]] ![![83, 0, 0], ![-23, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![-1909, 83, 0]], ![![3818, 1909, 83], ![-996, -498, 0]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![-23, 1, 0]]], ![![![46, 23, 1]], ![![-12, -6, 0]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-69, 14, 4]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![-69, 14, 4]] 
 ![![89, 0, 0], ![0, 89, 0], ![5, 48, 1]] where
  M :=![![![-69, 14, 4], ![248, -129, 14], ![868, 38, -129]]]
  hmulB := by decide  
  f := ![![![-181, -22, -8]], ![![-496, -61, -22]], ![![-293, -36, -13]]]
  g := ![![![-1, -2, 4], ![2, -9, 14], ![17, 70, -129]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [48, 55, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 88], [0, 1]]
 g := ![![[3, 78], [42], [84], [40, 69], [84, 88], [1]], ![[74, 11], [42], [84], [72, 20], [50, 1], [1]]]
 h' := ![![[34, 88], [80, 73], [82, 65], [38, 23], [62, 46], [41, 34], [0, 1]], ![[0, 1], [70, 16], [67, 24], [19, 66], [24, 43], [40, 55], [34, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [63, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [48, 55, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-750, 632, 28]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10, -8, 28]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-181, -22, -8]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![-181, -22, -8]] 
 ![![89, 0, 0], ![41, 1, 0], ![10, 0, 1]] where
  M :=![![![-181, -22, -8], ![-496, -61, -22], ![-1364, -166, -61]]]
  hmulB := by decide  
  f := ![![![-69, 14, 4]], ![![-29, 5, 2]], ![![2, 2, -1]]]
  g := ![![![9, -22, -8], ![25, -61, -22], ![68, -166, -61]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![-69, 14, 4]] ![![-181, -22, -8]]
  ![![89, 0, 0]] where
 M := ![![![89, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


lemma PB97I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 96 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 96 (by omega)

def PB97I2 : PrimesBelowBoundCertificateInterval O 79 96 97 where
  m := 2
  g := ![2, 2]
  P := ![83, 89]
  hP := PB97I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC83
    · exact PBC89
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![6889, 83]
    · exact ![7921, 89]
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
  β := ![I83N1, I89N1]
  Il := ![[I83N1], [I89N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
