
import IdealArithmetic.Examples.NF3_1_894348_3.RI3_1_894348_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp263 : Fact (Nat.Prime 263) := {out := by norm_num}

def I263N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 0, 0], ![126, 67, 1]] i)))

def SI263N0: IdealEqSpanCertificate' Table ![![263, 0, 0], ![126, 67, 1]] 
 ![![263, 0, 0], ![0, 263, 0], ![126, 67, 1]] where
  M :=![![![263, 0, 0], ![0, 263, 0], ![0, 0, 263]], ![![126, 67, 1], ![182, 126, 469], ![12194, 26, 126]]]
  hmulB := by decide  
  f := ![![![-125, -67, -1], ![263, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-126, -67, 263]], ![![0, 0, 1], ![-224, -119, 469], ![-14, -32, 126]]]
  hle1 := by decide   
  hle2 := by decide  


def P263P0 : CertificateIrreducibleZModOfList' 263 2 2 8 [7, 194, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [69, 262], [0, 1]]
 g := ![![[178, 184], [176, 186], [26, 206], [153], [103], [92], [27], [1]], ![[250, 79], [123, 77], [38, 57], [153], [103], [92], [27], [1]]]
 h' := ![![[69, 262], [83, 45], [81, 42], [189, 39], [205, 68], [20, 41], [123, 108], [256, 69], [0, 1]], ![[0, 1], [32, 218], [86, 221], [250, 224], [163, 195], [219, 222], [211, 155], [20, 194], [69, 262]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [194, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI263N0 : CertifiedPrimeIdeal' SI263N0 263 where
  n := 2
  hpos := by decide
  P := [7, 194, 1]
  hirr := P263P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![371, -168, -187]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![91, 47, -187]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI263N0 : Ideal.IsPrime I263N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI263N0 B_one_repr
lemma NI263N0 : Nat.card (O ⧸ I263N0) = 69169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI263N0

def I263N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 0, 0], ![57, 1, 0]] i)))

def SI263N1: IdealEqSpanCertificate' Table ![![263, 0, 0], ![57, 1, 0]] 
 ![![263, 0, 0], ![57, 1, 0], ![137, 0, 1]] where
  M :=![![![263, 0, 0], ![0, 263, 0], ![0, 0, 263]], ![![57, 1, 0], ![0, 57, 7], ![182, 0, 57]]]
  hmulB := by decide  
  f := ![![![3079, 54, 0], ![-14202, 0, 0]], ![![627, 11, 0], ![-2892, 0, 0]], ![![1525, -14, -5], ![-7034, 188, 0]]]
  g := ![![![1, 0, 0], ![-57, 263, 0], ![-137, 0, 263]], ![![0, 1, 0], ![-16, 57, 7], ![-29, 0, 57]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI263N1 : Nat.card (O ⧸ I263N1) = 263 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI263N1)

lemma isPrimeI263N1 : Ideal.IsPrime I263N1 := prime_ideal_of_norm_prime hp263.out _ NI263N1
def MulI263N0 : IdealMulLeCertificate' Table 
  ![![263, 0, 0], ![126, 67, 1]] ![![263, 0, 0], ![57, 1, 0]]
  ![![263, 0, 0]] where
 M := ![![![69169, 0, 0], ![14991, 263, 0]], ![![33138, 17621, 263], ![7364, 3945, 526]]]
 hmul := by decide  
 g := ![![![![263, 0, 0]], ![![57, 1, 0]]], ![![![126, 67, 1]], ![![28, 15, 2]]]]
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


lemma PB268I5_primes (p : ℕ) :
  p ∈ Set.range ![263] ↔ Nat.Prime p ∧ 257 < p ∧ p ≤ 267 := by
  rw [← List.mem_ofFn']
  convert primes_range 257 267 (by omega)

def PB268I5 : PrimesBelowBoundCertificateInterval O 257 267 268 where
  m := 1
  g := ![2]
  P := ![263]
  hP := PB268I5_primes
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
