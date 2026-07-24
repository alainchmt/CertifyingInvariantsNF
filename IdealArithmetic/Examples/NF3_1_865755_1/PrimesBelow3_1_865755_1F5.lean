
import IdealArithmetic.Examples.NF3_1_865755_1.RI3_1_865755_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp263 : Fact (Nat.Prime 263) := {out := by norm_num}

def I263N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 0, 0], ![-74, 126, 1]] i)))

def SI263N0: IdealEqSpanCertificate' Table ![![263, 0, 0], ![-74, 126, 1]] 
 ![![263, 0, 0], ![0, 263, 0], ![189, 126, 1]] where
  M :=![![![263, 0, 0], ![0, 263, 0], ![0, 0, 263]], ![![-74, 126, 1], ![531, 91, 629], ![35058, 4962, -161]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-189, -126, 263]], ![![-1, 0, 1], ![-450, -301, 629], ![249, 96, -161]]]
  hle1 := by decide   
  hle2 := by decide  


def P263P0 : CertificateIrreducibleZModOfList' 263 2 2 8 [118, 204, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [59, 262], [0, 1]]
 g := ![![[131, 49], [215, 258], [135, 75], [225], [3], [81], [62], [1]], ![[129, 214], [183, 5], [89, 188], [225], [3], [81], [62], [1]]]
 h' := ![![[59, 262], [141, 7], [113, 235], [130, 115], [88, 248], [210, 240], [33, 254], [145, 59], [0, 1]], ![[0, 1], [28, 256], [39, 28], [77, 148], [255, 15], [168, 23], [28, 9], [207, 204], [59, 262]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [136]]
 b := ![[], [98, 68]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI263N0 : CertifiedPrimeIdeal' SI263N0 263 where
  n := 2
  hpos := by decide
  P := [118, 204, 1]
  hirr := P263P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2902, 1584, -25]
  a := ![-2, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![29, 18, -25]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI263N0 : Ideal.IsPrime I263N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI263N0 B_one_repr
lemma NI263N0 : Nat.card (O ⧸ I263N0) = 69169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI263N0

def I263N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 0, 0], ![-103, 1, 0]] i)))

def SI263N1: IdealEqSpanCertificate' Table ![![263, 0, 0], ![-103, 1, 0]] 
 ![![263, 0, 0], ![160, 1, 0], ![161, 0, 1]] where
  M :=![![![263, 0, 0], ![0, 263, 0], ![0, 0, 263]], ![![-103, 1, 0], ![2, -102, 5], ![279, 39, -104]]]
  hmulB := by decide  
  f := ![![![48670, -3096603, 151800], ![-30771, -7984680, 0]], ![![29626, -1883767, 92345], ![-18672, -4857347, 0]], ![![29784, -1895639, 92927], ![-18863, -4887960, 0]]]
  g := ![![![1, 0, 0], ![-160, 263, 0], ![-161, 0, 263]], ![![-1, 1, 0], ![59, -102, 5], ![41, 39, -104]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI263N1 : Nat.card (O ⧸ I263N1) = 263 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI263N1)

lemma isPrimeI263N1 : Ideal.IsPrime I263N1 := prime_ideal_of_norm_prime hp263.out _ NI263N1
def MulI263N0 : IdealMulLeCertificate' Table 
  ![![263, 0, 0], ![-74, 126, 1]] ![![263, 0, 0], ![-103, 1, 0]]
  ![![263, 0, 0]] where
 M := ![![![69169, 0, 0], ![-27089, 263, 0]], ![![-19462, 33138, 263], ![8153, -12887, 526]]]
 hmul := by decide  
 g := ![![![![263, 0, 0]], ![![-103, 1, 0]]], ![![![-74, 126, 1]], ![![31, -49, 2]]]]
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


lemma PB264I5_primes (p : ℕ) :
  p ∈ Set.range ![263] ↔ Nat.Prime p ∧ 257 < p ∧ p ≤ 263 := by
  rw [← List.mem_ofFn']
  convert primes_range 257 263 (by omega)

def PB264I5 : PrimesBelowBoundCertificateInterval O 257 263 264 where
  m := 1
  g := ![2]
  P := ![263]
  hP := PB264I5_primes
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
