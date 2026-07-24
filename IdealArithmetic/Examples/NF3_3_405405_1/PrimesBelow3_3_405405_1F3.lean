
import IdealArithmetic.Examples.NF3_3_405405_1.RI3_3_405405_1
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


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [47, 60, 96, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [59, 110, 98], [123, 28, 41], [0, 1]]
 g := ![![[120, 73, 6], [4, 120, 41], [48, 125], [133, 131, 25], [84, 46], [43, 1], []], ![[34, 43, 18, 109], [54, 67, 126, 39], [138, 100], [13, 120, 73, 93], [114, 44], [86, 89], [18, 13]], ![[98, 3, 84, 55], [18, 14, 124, 99], [49, 35], [128, 53, 43, 131], [88, 117], [95, 7], [75, 13]]]
 h' := ![![[59, 110, 98], [90, 75, 59], [123, 5, 72], [4, 122, 79], [9, 11, 134], [64, 14, 121], [0, 0, 1], [0, 1]], ![[123, 28, 41], [130, 12, 106], [125, 69, 4], [56, 83, 129], [132, 87, 104], [25, 27, 34], [133, 30, 28], [59, 110, 98]], ![[0, 1], [63, 52, 113], [2, 65, 63], [9, 73, 70], [54, 41, 40], [24, 98, 123], [67, 109, 110], [123, 28, 41]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34, 13], []]
 b := ![[], [119, 25, 41], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [47, 60, 96, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![417, 2085, 2085]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3, 15, 15]
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



lemma PB142I3_primes (p : ℕ) :
  p ∈ Set.range ![139] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 141 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 141 (by omega)

def PB142I3 : PrimesBelowBoundCertificateInterval O 137 141 142 where
  m := 1
  g := ![1]
  P := ![139]
  hP := PB142I3_primes
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
