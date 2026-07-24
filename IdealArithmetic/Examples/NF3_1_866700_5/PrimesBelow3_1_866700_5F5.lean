
import IdealArithmetic.Examples.NF3_1_866700_5.RI3_1_866700_5
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp263 : Fact (Nat.Prime 263) := {out := by norm_num}

def I263N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 0, 0]] i)))

def SI263N0: IdealEqSpanCertificate' Table ![![263, 0, 0]] 
 ![![263, 0, 0], ![0, 263, 0], ![0, 0, 263]] where
  M :=![![![263, 0, 0], ![0, 263, 0], ![0, 0, 263]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P263P0 : CertificateIrreducibleZModOfList' 263 3 2 8 [75, 192, 60, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [146, 159, 177], [57, 103, 86], [0, 1]]
 g := ![![[233, 261, 124], [20, 253, 50], [147, 109, 216], [197, 149], [165, 183], [5, 121], [203, 1], []], ![[196, 108, 120, 53], [40, 177, 135, 239], [161, 123, 61, 65], [204, 22], [41, 137], [94, 208], [156, 89], [188, 32]], ![[141, 47, 56, 35], [26, 257, 89, 184], [37, 125, 35, 69], [66, 156], [178, 48], [68, 105], [181, 33], [16, 32]]]
 h' := ![![[146, 159, 177], [78, 244, 178], [21, 139, 24], [227, 19, 74], [167, 257, 181], [203, 220, 112], [29, 136, 252], [0, 0, 1], [0, 1]], ![[57, 103, 86], [153, 247, 243], [194, 228, 249], [202, 80, 202], [118, 73, 223], [230, 234, 243], [210, 122, 58], [115, 42, 103], [146, 159, 177]], ![[0, 1], [251, 35, 105], [49, 159, 253], [133, 164, 250], [127, 196, 122], [8, 72, 171], [233, 5, 216], [208, 221, 159], [57, 103, 86]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [249, 156], []]
 b := ![[], [9, 15, 222], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI263N0 : CertifiedPrimeIdeal' SI263N0 263 where
  n := 3
  hpos := by decide
  P := [75, 192, 60, 1]
  hirr := P263P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5323383, -44184, -82056]
  a := ![6, -7, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-20241, -168, -312]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI263N0 : Ideal.IsPrime I263N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI263N0 B_one_repr
lemma NI263N0 : Nat.card (O ⧸ I263N0) = 18191447 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI263N0

def PBC263 : ContainsPrimesAboveP 263 ![I263N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI263N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![263, 0, 0]]) timesTableT_eq_Table B_one_repr 263 (by decide) 𝕀



lemma PB264I5_primes (p : ℕ) :
  p ∈ Set.range ![263] ↔ Nat.Prime p ∧ 257 < p ∧ p ≤ 263 := by
  rw [← List.mem_ofFn']
  convert primes_range 257 263 (by omega)

def PB264I5 : PrimesBelowBoundCertificateInterval O 257 263 264 where
  m := 1
  g := ![1]
  P := ![263]
  hP := PB264I5_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I263N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC263
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![18191447]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI263N0
  β := ![]
  Il := ![[]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
