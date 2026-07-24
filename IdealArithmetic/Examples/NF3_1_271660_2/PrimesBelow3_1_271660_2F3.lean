
import IdealArithmetic.Examples.NF3_1_271660_2.RI3_1_271660_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-48, 24, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-48, 24, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![91, 24, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-48, 24, 1], ![238, 20, 24], ![5712, 1870, 20]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-91, -24, 139]], ![![-1, 0, 1], ![-14, -4, 24], ![28, 10, 20]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [72, 92, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [47, 138], [0, 1]]
 g := ![![[9, 117], [53, 16], [4], [47, 35], [116], [124], [1]], ![[87, 22], [110, 123], [4], [24, 104], [116], [124], [1]]]
 h' := ![![[47, 138], [76, 123], [70, 135], [91, 2], [69, 69], [9, 33], [67, 47], [0, 1]], ![[0, 1], [19, 16], [21, 4], [46, 137], [115, 70], [31, 106], [52, 92], [47, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [78]]
 b := ![[], [126, 39]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [72, 92, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![548, 282, -23]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![19, 6, -23]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-24, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-24, 1, 0]] 
 ![![139, 0, 0], ![115, 1, 0], ![119, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-24, 1, 0], ![0, -24, 1], ![238, 68, -24]]]
  hmulB := by decide  
  f := ![![![889, -37, 0], ![5143, 0, 0]], ![![769, -32, 0], ![4449, 0, 0]], ![![797, -33, 0], ![4611, 1, 0]]]
  g := ![![![1, 0, 0], ![-115, 139, 0], ![-119, 0, 139]], ![![-1, 1, 0], ![19, -24, 1], ![-34, 68, -24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![-48, 24, 1]] ![![139, 0, 0], ![-24, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![-3336, 139, 0]], ![![-6672, 3336, 139], ![1390, -556, 0]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![-24, 1, 0]]], ![![![-48, 24, 1]], ![![10, -4, 0]]]]
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


lemma PB148I3_primes (p : ℕ) :
  p ∈ Set.range ![139] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 147 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 147 (by omega)

def PB148I3 : PrimesBelowBoundCertificateInterval O 137 147 148 where
  m := 1
  g := ![2]
  P := ![139]
  hP := PB148I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC139
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![19321, 139]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
      exact NI139N1
  β := ![I139N1]
  Il := ![[I139N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
