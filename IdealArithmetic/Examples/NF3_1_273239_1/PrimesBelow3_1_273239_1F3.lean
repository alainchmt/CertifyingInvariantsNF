
import IdealArithmetic.Examples.NF3_1_273239_1.RI3_1_273239_1
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


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [28, 121, 90, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [48, 126, 105], [1, 12, 34], [0, 1]]
 g := ![![[38, 99, 116], [81, 131, 52], [103, 107], [122, 133, 91], [85, 78], [49, 1], []], ![[13, 138, 20, 33], [56, 103, 97, 98], [94, 42], [71, 2, 37, 40], [27, 64], [86, 5], [121, 44]], ![[28, 63, 117, 4], [35, 86, 43, 52], [62, 113], [119, 22, 104, 79], [30, 80], [12, 30], [53, 44]]]
 h' := ![![[48, 126, 105], [95, 27, 33], [41, 80, 57], [59, 8, 61], [29, 66, 62], [18, 20, 56], [0, 0, 1], [0, 1]], ![[1, 12, 34], [91, 108, 34], [56, 94, 49], [66, 100, 43], [68, 17, 29], [44, 64, 131], [28, 115, 12], [48, 126, 105]], ![[0, 1], [111, 4, 72], [102, 104, 33], [93, 31, 35], [28, 56, 48], [112, 55, 91], [46, 24, 126], [1, 12, 34]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42, 86], []]
 b := ![[], [129, 9, 117], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [28, 121, 90, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6862013, 599368, -212531]
  a := ![0, 9, -20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-49367, 4312, -1529]
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



lemma PB148I3_primes (p : ℕ) :
  p ∈ Set.range ![139] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 147 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 147 (by omega)

def PB148I3 : PrimesBelowBoundCertificateInterval O 137 147 148 where
  m := 1
  g := ![1]
  P := ![139]
  hP := PB148I3_primes
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
