
import IdealArithmetic.Examples.NF3_3_787077_1.RI3_3_787077_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0]] 
 ![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 3 2 7 [124, 56, 138, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [59, 98, 99], [0, 98, 98], [0, 1]]
 g := ![![[17, 76, 171], [138, 59], [99, 115, 143], [72, 6], [26, 168], [195, 132], [1]], ![[69, 139, 179, 11], [28, 40], [14, 72, 116, 80], [26, 137], [158, 55], [52, 105], [136, 32, 7, 74]], ![[0, 8, 161, 79], [135, 43], [52, 146, 40, 129], [26, 193], [184, 37], [128, 150], [162, 165, 140, 123]]]
 h' := ![![[59, 98, 99], [128, 99, 34], [135, 86, 181], [105, 45, 52], [103, 76, 177], [61, 193, 103], [73, 141, 59], [0, 1]], ![[0, 98, 98], [23, 195, 131], [46, 178, 51], [86, 195, 95], [54, 189, 48], [52, 143, 45], [183, 38, 41], [59, 98, 99]], ![[0, 1], [56, 100, 32], [53, 130, 162], [76, 154, 50], [99, 129, 169], [121, 58, 49], [6, 18, 97], [0, 98, 98]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [127, 81], []]
 b := ![[], [67, 150, 35], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 3
  hpos := by decide
  P := [124, 56, 138, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1442237, -1205443, -1007064]
  a := ![-3, -5, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-7321, -6119, -5112]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 7645373 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def PBC197 : ContainsPrimesAboveP 197 ![I197N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![197, 0, 0]]) timesTableT_eq_Table B_one_repr 197 (by decide) 𝕀



lemma PB198I4_primes (p : ℕ) :
  p ∈ Set.range ![197] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 197 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 197 (by omega)

def PB198I4 : PrimesBelowBoundCertificateInterval O 193 197 198 where
  m := 1
  g := ![1]
  P := ![197]
  hP := PB198I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC197
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![7645373]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
  β := ![]
  Il := ![[]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
