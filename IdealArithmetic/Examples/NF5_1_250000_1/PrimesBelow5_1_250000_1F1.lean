
import IdealArithmetic.Examples.NF5_1_250000_1.RI5_1_250000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0, 0, 0]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0, 0, 0]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![0, 0, 0, 0, 29]] where
  M :=![![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![0, 0, 0, 0, 29]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 5 2 4 [24, 8, 3, 16, 1, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [14, 12, 6, 19, 17], [3, 24, 4, 8, 19], [17, 20, 13, 27, 23], [23, 1, 6, 4, 28], [0, 1]]
 g := ![![[26, 19, 28, 22, 28], [24, 0, 22, 1], [14, 28, 1], []], ![[28, 16, 26, 24, 11, 26, 22, 19], [7, 9, 16, 4], [25, 15, 23, 17, 26, 15], [26, 25, 3, 18, 2, 0, 18, 12]], ![[17, 28, 19, 23, 0, 22, 1, 26], [28, 27, 11, 24], [16, 17, 1, 20, 11, 1, 20, 17], [9, 10, 10, 21, 19, 19, 7, 15]], ![[8, 1, 14, 6, 26, 28, 21, 1], [19, 2, 21, 9], [14, 3, 16, 14, 8, 2, 1, 16], [16, 4, 28, 19, 21, 3, 0, 16]], ![[1, 3, 4, 26, 28, 2, 16, 20], [4, 2, 26, 23], [6, 14, 25, 16, 16, 6, 23, 1], [0, 6, 18, 11, 6, 2, 13, 28]]]
 h' := ![![[14, 12, 6, 19, 17], [3, 16, 10, 10, 17], [12, 28, 0, 3, 28], [0, 0, 0, 1], [0, 1]], ![[3, 24, 4, 8, 19], [19, 7, 19, 7, 5], [19, 2, 16, 5, 2], [3, 13, 4, 21], [14, 12, 6, 19, 17]], ![[17, 20, 13, 27, 23], [25, 25, 25, 21, 26], [1, 28, 4, 2, 16], [14, 17, 15, 17, 23], [3, 24, 4, 8, 19]], ![[23, 1, 6, 4, 28], [12, 11, 5, 20, 13], [2, 2, 14, 5, 3], [5, 6, 5, 25, 23], [17, 20, 13, 27, 23]], ![[0, 1], [24, 28, 28, 0, 26], [2, 27, 24, 14, 9], [16, 22, 5, 23, 12], [23, 1, 6, 4, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23, 2, 26, 24], [], [], []]
 b := ![[], [0, 0, 26, 17, 2], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 5
  hpos := by decide
  P := [24, 8, 3, 16, 1, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1598016, -4057477, -100137, 2454473, -14181]
  a := ![0, -1, -3, -1, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![55104, -139913, -3453, 84637, -489]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 20511149 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def PBC29 : ContainsPrimesAboveP 29 ![I29N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![29, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 29 (by decide) 𝕀

instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, -8, 0, 2, 0]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![3, -8, 0, 2, 0]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![12, 27, 1, 0, 0], ![17, 27, 0, 1, 0], ![18, 18, 0, 0, 1]] where
  M :=![![![3, -8, 0, 2, 0], ![0, 3, -6, 0, 4], ![8, -20, 3, 2, 0], ![0, 8, -18, 3, 4], ![0, 0, 4, -6, 3]]]
  hmulB := by decide  
  f := ![![![-107, 24, 44, -6, -24]], ![![-48, 13, 18, -4, -12]], ![![-84, 21, 33, -6, -20]], ![![-101, 25, 40, -7, -24]], ![![-90, 22, 36, -6, -21]]]
  g := ![![![-1, -2, 0, 2, 0], ![0, 3, -6, 0, 4], ![-2, -5, 3, 2, 0], ![3, 11, -18, 3, 4], ![0, 0, 4, -6, 3]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [12, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 30], [0, 1]]
 g := ![![[27, 8], [22, 7], [16, 4], [17, 1]], ![[8, 23], [17, 24], [22, 27], [3, 30]]]
 h' := ![![[17, 30], [15, 16], [25, 21], [13, 29], [0, 1]], ![[0, 1], [8, 15], [10, 10], [10, 2], [17, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [2, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [12, 14, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-769, 855, 4161, -1085, 409]
  a := ![3, -64, 2, -1, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1278, -2889, 4161, -1085, 409]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, -3, -3, 0, 2]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![11, -3, -3, 0, 2]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![23, 13, 1, 0, 0], ![11, 9, 0, 1, 0], ![9, 18, 0, 0, 1]] where
  M :=![![![11, -3, -3, 0, 2], ![4, 1, -3, 1, 0], ![0, 4, 2, -3, 2], ![4, -10, 1, 6, -6], ![-6, 15, -3, -4, 5]]]
  hmulB := by decide  
  f := ![![![1, 3, 5, 2, 0]], ![![0, 1, 5, 5, 4]], ![![1, 2, 6, 4, 2]], ![![1, 0, 3, 3, 2]], ![![1, 0, 4, 4, 3]]]
  g := ![![![2, 0, -3, 0, 2], ![2, 1, -3, 1, 0], ![-1, -1, 2, -3, 2], ![-1, 1, 1, 6, -6], ![2, 0, -3, -4, 5]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P1 : CertificateIrreducibleZModOfList' 31 2 2 4 [17, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 30], [0, 1]]
 g := ![![[3, 14], [15, 25], [7, 28], [11, 1]], ![[2, 17], [11, 6], [5, 3], [22, 30]]]
 h' := ![![[11, 30], [24, 13], [5, 5], [30, 11], [0, 1]], ![[0, 1], [12, 18], [29, 26], [27, 20], [11, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [16, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N1 : CertifiedPrimeIdeal' SI31N1 31 where
  n := 2
  hpos := by decide
  P := [17, 20, 1]
  hirr := P31P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![102, -202, -39, 42, 8]
  a := ![1, -3, -1, -1, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![15, -7, -39, 42, 8]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N1 B_one_repr
lemma NI31N1 : Nat.card (O ⧸ I31N1) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N1

def I31N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, -5, -5, 2, 4]] i)))

def SI31N2: IdealEqSpanCertificate' Table ![![13, -5, -5, 2, 4]] 
 ![![31, 0, 0, 0, 0], ![22, 1, 0, 0, 0], ![12, 0, 1, 0, 0], ![15, 0, 0, 1, 0], ![15, 0, 0, 0, 1]] where
  M :=![![![13, -5, -5, 2, 4], ![8, -7, -3, 3, 4], ![8, -12, -4, 5, 6], ![12, -22, -7, 8, 10], ![6, -13, -5, 4, 5]]]
  hmulB := by decide  
  f := ![![![-9, 37, -17, -4, 6]], ![![-6, 25, -11, -3, 4]], ![![-4, 16, -8, -1, 2]], ![![-5, 19, -6, -4, 4]], ![![-3, 14, -8, 0, 1]]]
  g := ![![![3, -5, -5, 2, 4], ![3, -7, -3, 3, 4], ![5, -12, -4, 5, 6], ![10, -22, -7, 8, 10], ![7, -13, -5, 4, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N2 : Nat.card (O ⧸ I31N2) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N2)

lemma isPrimeI31N2 : Ideal.IsPrime I31N2 := prime_ideal_of_norm_prime hp31.out _ NI31N2
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![3, -8, 0, 2, 0]] ![![11, -3, -3, 0, 2]]
  ![![9, -37, 17, 4, -6]] where
 M := ![![![9, -37, 17, 4, -6]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI31N1 : IdealMulLeCertificate' Table 
  ![![9, -37, 17, 4, -6]] ![![13, -5, -5, 2, 4]]
  ![![31, 0, 0, 0, 0]] where
 M := ![![![-31, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N1, I31N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
    exact isPrimeI31N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0 ⊙ MulI31N1)


lemma PB32I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 31 (by omega)

def PB32I1 : PrimesBelowBoundCertificateInterval O 23 31 32 where
  m := 2
  g := ![1, 3]
  P := ![29, 31]
  hP := PB32I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0]
    · exact ![I31N0, I31N1, I31N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC29
    · exact PBC31
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![20511149]
    · exact ![961, 961, 31]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
      exact NI31N2
  β := ![I31N2]
  Il := ![[], [I31N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
