
import IdealArithmetic.Examples.NF3_1_888300_3.RI3_1_888300_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp263 : Fact (Nat.Prime 263) := {out := by norm_num}

def I263N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 0, 0], ![3, 68, 1]] i)))

def SI263N0: IdealEqSpanCertificate' Table ![![263, 0, 0], ![3, 68, 1]] 
 ![![263, 0, 0], ![0, 263, 0], ![3, 68, 1]] where
  M :=![![![263, 0, 0], ![0, 263, 0], ![0, 0, 263]], ![![3, 68, 1], ![730, 153, 68], ![49640, 10930, 153]]]
  hmulB := by decide  
  f := ![![![-2, -68, -1], ![263, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-3, -68, 263]], ![![0, 0, 1], ![2, -17, 68], ![187, 2, 153]]]
  hle1 := by decide   
  hle2 := by decide  


def P263P0 : CertificateIrreducibleZModOfList' 263 2 2 8 [71, 79, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [184, 262], [0, 1]]
 g := ![![[253, 243], [102, 203], [56, 192], [173], [129], [25], [192], [1]], ![[255, 20], [108, 60], [142, 71], [173], [129], [25], [192], [1]]]
 h' := ![![[184, 262], [122, 56], [232, 236], [150, 184], [134, 35], [183, 38], [88, 258], [192, 184], [0, 1]], ![[0, 1], [169, 207], [261, 27], [79, 79], [262, 228], [74, 225], [220, 5], [121, 79], [184, 262]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [183]]
 b := ![[], [261, 223]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI263N0 : CertifiedPrimeIdeal' SI263N0 263 where
  n := 2
  hpos := by decide
  P := [71, 79, 1]
  hirr := P263P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1531, 951, 72]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5, -15, 72]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI263N0 : Ideal.IsPrime I263N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI263N0 B_one_repr
lemma NI263N0 : Nat.card (O ⧸ I263N0) = 69169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI263N0

def I263N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 0, 0], ![-68, 1, 0]] i)))

def SI263N1: IdealEqSpanCertificate' Table ![![263, 0, 0], ![-68, 1, 0]] 
 ![![263, 0, 0], ![195, 1, 0], ![110, 0, 1]] where
  M :=![![![263, 0, 0], ![0, 263, 0], ![0, 0, 263]], ![![-68, 1, 0], ![0, -68, 1], ![730, 150, -68]]]
  hmulB := by decide  
  f := ![![![15437, -227, 0], ![59701, 0, 0]], ![![11561, -170, 0], ![44711, 0, 0]], ![![6546, -96, 0], ![25316, 1, 0]]]
  g := ![![![1, 0, 0], ![-195, 263, 0], ![-110, 0, 263]], ![![-1, 1, 0], ![50, -68, 1], ![-80, 150, -68]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI263N1 : Nat.card (O ⧸ I263N1) = 263 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI263N1)

lemma isPrimeI263N1 : Ideal.IsPrime I263N1 := prime_ideal_of_norm_prime hp263.out _ NI263N1
def MulI263N0 : IdealMulLeCertificate' Table 
  ![![263, 0, 0], ![3, 68, 1]] ![![263, 0, 0], ![-68, 1, 0]]
  ![![263, 0, 0]] where
 M := ![![![69169, 0, 0], ![-17884, 263, 0]], ![![789, 17884, 263], ![526, -4471, 0]]]
 hmul := by decide  
 g := ![![![![263, 0, 0]], ![![-68, 1, 0]]], ![![![3, 68, 1]], ![![2, -17, 0]]]]
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


lemma PB267I5_primes (p : ℕ) :
  p ∈ Set.range ![263] ↔ Nat.Prime p ∧ 257 < p ∧ p ≤ 266 := by
  rw [← List.mem_ofFn']
  convert primes_range 257 266 (by omega)

def PB267I5 : PrimesBelowBoundCertificateInterval O 257 266 267 where
  m := 1
  g := ![2]
  P := ![263]
  hP := PB267I5_primes
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
