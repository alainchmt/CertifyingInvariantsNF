
import IdealArithmetic.Examples.NF3_1_903756_2.RI3_1_903756_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp263 : Fact (Nat.Prime 263) := {out := by norm_num}

def I263N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 0, 0], ![-10, -78, 1]] i)))

def SI263N0: IdealEqSpanCertificate' Table ![![263, 0, 0], ![-10, -78, 1]] 
 ![![263, 0, 0], ![0, 263, 0], ![253, 185, 1]] where
  M :=![![![263, 0, 0], ![0, 263, 0], ![0, 0, 263]], ![![-10, -78, 1], ![-129, 151, -855], ![-14189, -372, -238]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-253, -185, 263]], ![![-1, -1, 1], ![822, 602, -855], ![175, 166, -238]]]
  hle1 := by decide   
  hle2 := by decide  


def P263P0 : CertificateIrreducibleZModOfList' 263 2 2 8 [247, 50, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [213, 262], [0, 1]]
 g := ![![[227, 99], [151, 243], [71, 81], [133], [124], [204], [133], [1]], ![[11, 164], [99, 20], [229, 182], [133], [124], [204], [133], [1]]]
 h' := ![![[213, 262], [49, 238], [84, 56], [224, 254], [215, 213], [134, 178], [17, 166], [16, 213], [0, 1]], ![[0, 1], [247, 25], [177, 207], [148, 9], [85, 50], [176, 85], [133, 97], [149, 50], [213, 262]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [200, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI263N0 : CertifiedPrimeIdeal' SI263N0 263 where
  n := 2
  hpos := by decide
  P := [247, 50, 1]
  hirr := P263P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6326, 2108, 209]
  a := ![-4, 1, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-177, -139, 209]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI263N0 : Ideal.IsPrime I263N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI263N0 B_one_repr
lemma NI263N0 : Nat.card (O ⧸ I263N0) = 69169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI263N0

def I263N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 0, 0], ![66, 1, 0]] i)))

def SI263N1: IdealEqSpanCertificate' Table ![![263, 0, 0], ![66, 1, 0]] 
 ![![263, 0, 0], ![66, 1, 0], ![238, 0, 1]] where
  M :=![![![263, 0, 0], ![0, 263, 0], ![0, 0, 263]], ![![66, 1, 0], ![4, 64, 11], ![183, 5, 69]]]
  hmulB := by decide  
  f := ![![![1995, 35069, 6028], ![789, -144124, 0]], ![![482, 8767, 1507], ![264, -36031, 0]], ![![1776, 31735, 5455], ![831, -130424, 0]]]
  g := ![![![1, 0, 0], ![-66, 263, 0], ![-238, 0, 263]], ![![0, 1, 0], ![-26, 64, 11], ![-63, 5, 69]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI263N1 : Nat.card (O ⧸ I263N1) = 263 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI263N1)

lemma isPrimeI263N1 : Ideal.IsPrime I263N1 := prime_ideal_of_norm_prime hp263.out _ NI263N1
def MulI263N0 : IdealMulLeCertificate' Table 
  ![![263, 0, 0], ![-10, -78, 1]] ![![263, 0, 0], ![66, 1, 0]]
  ![![263, 0, 0]] where
 M := ![![![69169, 0, 0], ![17358, 263, 0]], ![![-2630, -20514, 263], ![-789, -4997, -789]]]
 hmul := by decide  
 g := ![![![![263, 0, 0]], ![![66, 1, 0]]], ![![![-10, -78, 1]], ![![-3, -19, -3]]]]
 hle2 := by decide  


def PBC263 : ContainsPrimesAboveP 263 ![I263N0, I263N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI263N0
    exact isPrimeI263N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 263 (by decide) (𝕀 ⊙ MulI263N0)


lemma PB269I5_primes (p : ℕ) :
  p ∈ Set.range ![263] ↔ Nat.Prime p ∧ 257 < p ∧ p ≤ 268 := by
  rw [← List.mem_ofFn']
  convert primes_range 257 268 (by omega)

def PB269I5 : PrimesBelowBoundCertificateInterval O 257 268 269 where
  m := 1
  g := ![2]
  P := ![263]
  hP := PB269I5_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I263N0, I263N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC263
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![69169, 263]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI263N0
      exact NI263N1
  β := ![I263N1]
  Il := ![[I263N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
