
import IdealArithmetic.Examples.NF3_1_25160_1.RI3_1_25160_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 2]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![29, 0, 2]] 
 ![![37, 0, 0], ![3, 1, 0], ![33, 0, 1]] where
  M :=![![![29, 0, 2], ![26, -1, 2], ![-2, -2, -1]]]
  hmulB := by decide  
  f := ![![![5, -4, 2]], ![![1, -1, 0]], ![![3, -2, 1]]]
  g := ![![![-1, 0, 2], ![-1, -1, 2], ![1, -2, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-2, 1, 0]] 
 ![![37, 0, 0], ![35, 1, 0], ![17, 0, 1]] where
  M :=![![![-2, 1, 0], ![1, -2, 2], ![13, -15, -1]]]
  hmulB := by decide  
  f := ![![![-32, -1, -2]], ![![-31, -1, -2]], ![![-15, 0, -1]]]
  g := ![![![-1, 1, 0], ![1, -2, 2], ![15, -15, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![29, 0, 2]] ![![-2, 1, 0]]
  ![![-32, -1, -2]] where
 M := ![![![-32, -1, -2]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![-32, -1, -2]] ![![-2, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![37, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1, I37N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
    exact isPrimeI37N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0 ⊙ MulI37N1)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-31711, 37650, 6990]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![-31711, 37650, 6990]] 
 ![![41, 0, 0], ![0, 41, 0], ![36, 17, 1]] where
  M :=![![![-31711, 37650, 6990], ![128520, -136561, 82290], ![482460, -571740, -98911]]]
  hmulB := by decide  
  f := ![![![-1476972431, 6645450, -98848290]], ![![-1278382320, 5751919, -85557390]], ![![-1822396776, 8199643, -121966261]]]
  g := ![![![-6911, -1980, 6990], ![-69120, -37451, 82290], ![98616, 27067, -98911]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [33, 37, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 40], [0, 1]]
 g := ![![[21, 5], [37], [8], [5, 16], [1]], ![[0, 36], [37], [8], [28, 25], [1]]]
 h' := ![![[4, 40], [11, 28], [24, 18], [40, 7], [8, 4], [0, 1]], ![[0, 1], [0, 13], [14, 23], [27, 34], [24, 37], [4, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [24, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [33, 37, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![46, -99, -124]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![110, 49, -124]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1476972431, 6645450, -98848290]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-1476972431, 6645450, -98848290]] 
 ![![41, 0, 0], ![6, 1, 0], ![3, 0, 1]] where
  M :=![![![-1476972431, 6645450, -98848290], ![-1278382320, 5751919, -85557390], ![185239140, -833460, 12397369]]]
  hmulB := by decide  
  f := ![![![-31711, 37650, 6990]], ![![-1506, 2179, 3030]], ![![9447, -11190, -1901]]]
  g := ![![![-29763421, 6645450, -98848290], ![-25761504, 5751919, -85557390], ![3732873, -833460, 12397369]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![-31711, 37650, 6990]] ![![-1476972431, 6645450, -98848290]]
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


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [36, 17, 17, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 21, 36], [20, 21, 7], [0, 1]]
 g := ![![[7, 36, 6], [28, 12, 35], [42, 10], [14, 26, 1], []], ![[7, 40, 21, 25], [5, 23, 33, 13], [16, 17], [2, 15, 25, 9], [34, 6]], ![[28, 29, 16, 7], [3, 5], [41, 38], [35, 11, 30, 34], [20, 6]]]
 h' := ![![[6, 21, 36], [24, 16, 7], [8, 33, 32], [12, 30, 15], [0, 0, 1], [0, 1]], ![[20, 21, 7], [17, 25, 35], [30, 33, 11], [2, 25, 19], [16, 17, 21], [6, 21, 36]], ![[0, 1], [39, 2, 1], [17, 20], [26, 31, 9], [24, 26, 21], [20, 21, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29], []]
 b := ![[], [34, 41], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [36, 17, 17, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![23005, -23607, 20253]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![535, -549, 471]
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



lemma PB45I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 44 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 44 (by omega)

def PB45I1 : PrimesBelowBoundCertificateInterval O 31 44 45 where
  m := 3
  g := ![3, 2, 1]
  P := ![37, 41, 43]
  hP := PB45I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC37
    · exact PBC41
    · exact PBC43
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![37, 37, 37]
    · exact ![1681, 41]
    · exact ![79507]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
      exact NI37N1
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
  β := ![I37N0, I37N1, I41N1]
  Il := ![[I37N0, I37N1, I37N1], [I41N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
