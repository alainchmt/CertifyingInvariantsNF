
import IdealArithmetic.Examples.NF3_1_280904_4.RI3_1_280904_4
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-48, -31, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-48, -31, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![91, 108, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-48, -31, 1], ![-130, -55, -61], ![3016, 164, -86]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-91, -108, 139]], ![![-1, -1, 1], ![39, 47, -61], ![78, 68, -86]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [101, 69, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [70, 138], [0, 1]]
 g := ![![[75, 47], [68, 107], [1], [44, 5], [57], [35], [1]], ![[29, 92], [52, 32], [1], [116, 134], [57], [35], [1]]]
 h' := ![![[70, 138], [82, 66], [54, 78], [4, 1], [117, 127], [133, 125], [38, 70], [0, 1]], ![[0, 1], [115, 73], [93, 61], [74, 138], [111, 12], [126, 14], [73, 69], [70, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [81]]
 b := ![[], [42, 110]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [101, 69, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-574, -307, -156]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![98, 119, -156]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![61, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![61, 1, 0]] 
 ![![139, 0, 0], ![61, 1, 0], ![86, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![61, 1, 0], ![1, 61, 2], ![-99, -7, 62]]]
  hmulB := by decide  
  f := ![![![-8247, -741208, -24304], ![-8896, 1689128, 0]], ![![-3624, -325224, -10664], ![-3891, 741148, 0]], ![![-5095, -458589, -15037], ![-5521, 1045072, 0]]]
  g := ![![![1, 0, 0], ![-61, 139, 0], ![-86, 0, 139]], ![![0, 1, 0], ![-28, 61, 2], ![-36, -7, 62]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![-48, -31, 1]] ![![139, 0, 0], ![61, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![8479, 139, 0]], ![![-6672, -4309, 139], ![-3058, -1946, 0]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![61, 1, 0]]], ![![![-48, -31, 1]], ![![-22, -14, 0]]]]
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


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [118, 15, 66, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [63, 46, 139], [20, 102, 10], [0, 1]]
 g := ![![[127, 11, 80], [121, 130], [107, 95, 102], [22, 110], [71, 136, 102], [83, 1], []], ![[31, 98, 78, 21], [137, 39], [45, 22, 143, 109], [120, 124], [42, 125, 90, 8], [128, 123], [79, 100]], ![[4, 31, 115, 78], [124, 24], [80, 55, 9, 111], [94, 67], [22, 63, 1, 135], [83, 30], [59, 100]]]
 h' := ![![[63, 46, 139], [57, 10, 123], [39, 115, 32], [50, 64, 129], [115, 132, 40], [40, 127, 20], [0, 0, 1], [0, 1]], ![[20, 102, 10], [103, 81, 79], [37, 83, 28], [137, 108, 2], [80, 122, 78], [66, 36, 25], [11, 112, 102], [63, 46, 139]], ![[0, 1], [115, 58, 96], [61, 100, 89], [109, 126, 18], [131, 44, 31], [76, 135, 104], [143, 37, 46], [20, 102, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77, 22], []]
 b := ![[], [45, 133, 32], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [118, 15, 66, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![649342, 1192, -2980]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4358, 8, -20]
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



lemma PB150I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 149 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 149 (by omega)

def PB150I3 : PrimesBelowBoundCertificateInterval O 137 149 150 where
  m := 2
  g := ![2, 1]
  P := ![139, 149]
  hP := PB150I3_primes
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
