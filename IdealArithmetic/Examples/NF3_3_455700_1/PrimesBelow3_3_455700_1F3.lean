
import IdealArithmetic.Examples.NF3_3_455700_1.RI3_3_455700_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-8, 32, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-8, 32, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![131, 32, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-8, 32, 1], ![-220, 46, 97], ![-8130, 1662, 78]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-131, -32, 139]], ![![-1, 0, 1], ![-93, -22, 97], ![-132, -6, 78]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [81, 135, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 138], [0, 1]]
 g := ![![[48, 127], [41, 24], [6], [14, 52], [89], [16], [1]], ![[0, 12], [137, 115], [6], [83, 87], [89], [16], [1]]]
 h' := ![![[4, 138], [15, 31], [137, 118], [117, 80], [30, 57], [122, 111], [58, 4], [0, 1]], ![[0, 1], [0, 108], [53, 21], [20, 59], [119, 82], [10, 28], [74, 135], [4, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65]]
 b := ![[], [74, 102]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [81, 135, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2158, -403, 96]
  a := ![-1, -1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-106, -25, 96]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![42, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![42, 1, 0]] 
 ![![139, 0, 0], ![42, 1, 0], ![61, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![42, 1, 0], ![1, 42, 3], ![-252, 54, 43]]]
  hmulB := by decide  
  f := ![![![-9683, -487826, -34848], ![-6394, 1614624, 0]], ![![-2963, -147365, -10527], ![-1806, 487751, 0]], ![![-4253, -214082, -15293], ![-2794, 708576, 0]]]
  g := ![![![1, 0, 0], ![-42, 139, 0], ![-61, 0, 139]], ![![0, 1, 0], ![-14, 42, 3], ![-37, 54, 43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![-8, 32, 1]] ![![139, 0, 0], ![42, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![5838, 139, 0]], ![![-1112, 4448, 139], ![-556, 1390, 139]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![42, 1, 0]]], ![![![-8, 32, 1]], ![![-4, 10, 1]]]]
 hle2 := by decide  


def PBC139 : ContainsPrimesAboveP 139 ![I139N0, I139N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
    exact isPrimeI139N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 139 (by decide) (𝕀 ⊙ MulI139N0)
instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-91, 74, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-91, 74, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![58, 74, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-91, 74, 1], ![-178, -37, 223], ![-18714, 3930, 37]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-58, -74, 149]], ![![-1, 0, 1], ![-88, -111, 223], ![-140, 8, 37]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [100, 98, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [51, 148], [0, 1]]
 g := ![![[147, 76], [132], [147, 68], [36], [118, 133], [68], [1]], ![[0, 73], [132], [39, 81], [36], [47, 16], [68], [1]]]
 h' := ![![[51, 148], [129, 15], [51, 70], [72, 98], [120, 143], [71, 122], [49, 51], [0, 1]], ![[0, 1], [0, 134], [45, 79], [4, 51], [112, 6], [35, 27], [117, 98], [51, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [79]]
 b := ![[], [73, 114]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [100, 98, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4126, -4950, 3344]
  a := ![2, -2, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1274, -1694, 3344]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-74, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-74, 1, 0]] 
 ![![149, 0, 0], ![75, 1, 0], ![112, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-74, 1, 0], ![1, -74, 3], ![-252, 54, -73]]]
  hmulB := by decide  
  f := ![![![-51, 14798, -600], ![298, 29800, 0]], ![![-25, 7399, -300], ![150, 14900, 0]], ![![-88, 11124, -451], ![124, 22400, 0]]]
  g := ![![![1, 0, 0], ![-75, 149, 0], ![-112, 0, 149]], ![![-1, 1, 0], ![35, -74, 3], ![26, 54, -73]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![-91, 74, 1]] ![![149, 0, 0], ![-74, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![-11026, 149, 0]], ![![-13559, 11026, 149], ![6556, -5513, 149]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![-74, 1, 0]]], ![![![-91, 74, 1]], ![![44, -37, 1]]]]
 hle2 := by decide  


def PBC149 : ContainsPrimesAboveP 149 ![I149N0, I149N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
    exact isPrimeI149N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 149 (by decide) (𝕀 ⊙ MulI149N0)


lemma PB151I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 150 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 150 (by omega)

def PB151I3 : PrimesBelowBoundCertificateInterval O 137 150 151 where
  m := 2
  g := ![2, 2]
  P := ![139, 149]
  hP := PB151I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC139
    · exact PBC149
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![19321, 139]
    · exact ![22201, 149]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
      exact NI139N1
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
  β := ![I139N1, I149N1]
  Il := ![[I139N1], [I149N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
