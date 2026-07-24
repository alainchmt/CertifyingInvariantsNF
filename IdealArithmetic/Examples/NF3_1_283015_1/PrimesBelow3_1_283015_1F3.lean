
import IdealArithmetic.Examples.NF3_1_283015_1.RI3_1_283015_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-55, 28, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-55, 28, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![84, 28, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-55, 28, 1], ![-99, -33, 252], ![-2761, -179, -61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-84, -28, 139]], ![![-1, 0, 1], ![-153, -51, 252], ![17, 11, -61]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [131, 53, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [86, 138], [0, 1]]
 g := ![![[115, 52], [117, 129], [13], [70, 44], [67], [29], [1]], ![[0, 87], [91, 10], [13], [101, 95], [67], [29], [1]]]
 h' := ![![[86, 138], [102, 57], [120, 95], [4, 98], [26, 105], [18, 117], [8, 86], [0, 1]], ![[0, 1], [0, 82], [89, 44], [92, 41], [21, 34], [72, 22], [37, 53], [86, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [88, 82]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [131, 53, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3422, -3689, -2599]
  a := ![0, -2, -17]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1546, 497, -2599]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![26, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![26, 1, 0]] 
 ![![139, 0, 0], ![26, 1, 0], ![61, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![26, 1, 0], ![0, 27, 9], ![-99, -6, 26]]]
  hmulB := by decide  
  f := ![![![2263, 87, 0], ![-12093, 0, 0]], ![![390, 15, 0], ![-2084, 0, 0]], ![![989, 32, -2], ![-5285, 31, 0]]]
  g := ![![![1, 0, 0], ![-26, 139, 0], ![-61, 0, 139]], ![![0, 1, 0], ![-9, 27, 9], ![-11, -6, 26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![-55, 28, 1]] ![![139, 0, 0], ![26, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![3614, 139, 0]], ![![-7645, 3892, 139], ![-1529, 695, 278]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![26, 1, 0]]], ![![![-55, 28, 1]], ![![-11, 5, 2]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0]] 
 ![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [33, 138, 134, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [107, 94, 95], [57, 54, 54], [0, 1]]
 g := ![![[69, 100, 37], [47, 22], [68, 66, 53], [99, 104], [87, 19, 119], [15, 1], []], ![[31, 31, 35, 45], [30, 25], [136, 45, 73, 110], [13, 22], [1, 110, 61, 19], [65, 85], [63, 85]], ![[58, 139, 24, 132], [90, 123], [59, 59, 141, 121], [109, 107], [103, 82, 129, 33], [11, 45], [104, 85]]]
 h' := ![![[107, 94, 95], [20, 95, 127], [140, 99, 52], [121, 7, 65], [109, 101, 113], [101, 132, 87], [0, 0, 1], [0, 1]], ![[57, 54, 54], [129, 93, 89], [15, 109, 144], [63, 76, 3], [55, 113, 52], [81, 101, 103], [132, 124, 54], [107, 94, 95]], ![[0, 1], [74, 110, 82], [141, 90, 102], [98, 66, 81], [87, 84, 133], [48, 65, 108], [115, 25, 94], [57, 54, 54]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [85, 124], []]
 b := ![[], [10, 37, 63], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [33, 138, 134, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1465415, -6407, -70477]
  a := ![-1, 1, 11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![9835, -43, -473]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 3307949 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def PBC149 : ContainsPrimesAboveP 149 ![I149N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![149, 0, 0]]) timesTableT_eq_Table B_one_repr 149 (by decide) 𝕀



lemma PB151I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 150 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 150 (by omega)

def PB151I3 : PrimesBelowBoundCertificateInterval O 137 150 151 where
  m := 2
  g := ![2, 1]
  P := ![139, 149]
  hP := PB151I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0]
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
    · exact ![3307949]
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
  β := ![I139N1]
  Il := ![[I139N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
