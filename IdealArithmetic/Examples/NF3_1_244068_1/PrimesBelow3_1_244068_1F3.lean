
import IdealArithmetic.Examples.NF3_1_244068_1.RI3_1_244068_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0]] 
 ![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [62, 29, 30, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [120, 23, 107], [128, 115, 32], [0, 1]]
 g := ![![[16, 24, 7], [30, 7, 116], [115, 89], [81, 71, 45], [96, 118], [109, 1], []], ![[115, 26, 43, 38], [57, 58, 72, 24], [88, 71], [16, 14, 29, 57], [42, 78], [30, 20], [56, 51]], ![[52, 78, 19, 18], [7, 33, 79, 40], [135, 37], [136, 20, 34, 43], [26, 83], [128, 112], [131, 51]]]
 h' := ![![[120, 23, 107], [86, 111, 110], [5, 76, 33], [121, 57, 111], [54, 71, 103], [53, 113, 37], [0, 0, 1], [0, 1]], ![[128, 115, 32], [70, 32, 63], [9, 116, 112], [105, 80, 99], [57, 90, 121], [115, 11, 83], [86, 39, 115], [120, 23, 107]], ![[0, 1], [15, 135, 105], [70, 86, 133], [10, 2, 68], [135, 117, 54], [94, 15, 19], [61, 100, 23], [128, 115, 32]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62, 114], []]
 b := ![[], [34, 89, 47], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [62, 29, 30, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-113702, -46426, -390312]
  a := ![-3, -2, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-818, -334, -2808]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 2685619 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def PBC139 : ContainsPrimesAboveP 139 ![I139N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![139, 0, 0]]) timesTableT_eq_Table B_one_repr 139 (by decide) 𝕀



lemma PB140I3_primes (p : ℕ) :
  p ∈ Set.range ![139] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 139 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 139 (by omega)

def PB140I3 : PrimesBelowBoundCertificateInterval O 137 139 140 where
  m := 1
  g := ![1]
  P := ![139]
  hP := PB140I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC139
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2685619]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
  β := ![]
  Il := ![[]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
