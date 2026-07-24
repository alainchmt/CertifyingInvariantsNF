
import IdealArithmetic.Examples.NF3_1_884199_1.RI3_1_884199_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp263 : Fact (Nat.Prime 263) := {out := by norm_num}

def I263N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 0, 0], ![-147, -24, 1]] i)))

def SI263N0: IdealEqSpanCertificate' Table ![![263, 0, 0], ![-147, -24, 1]] 
 ![![263, 0, 0], ![0, 263, 0], ![116, 239, 1]] where
  M :=![![![263, 0, 0], ![0, 263, 0], ![0, 0, 263]], ![![-147, -24, 1], ![327, -113, -72], ![-7957, -1283, -89]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-116, -239, 263]], ![![-1, -1, 1], ![33, 65, -72], ![9, 76, -89]]]
  hle1 := by decide   
  hle2 := by decide  


def P263P0 : CertificateIrreducibleZModOfList' 263 2 2 8 [236, 119, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [144, 262], [0, 1]]
 g := ![![[93, 122], [64, 206], [191, 25], [35], [26], [172], [222], [1]], ![[40, 141], [9, 57], [109, 238], [35], [26], [172], [222], [1]]]
 h' := ![![[144, 262], [150, 139], [160, 39], [1, 5], [138, 78], [248, 17], [148, 31], [27, 144], [0, 1]], ![[0, 1], [178, 124], [253, 224], [195, 258], [61, 185], [66, 246], [141, 232], [249, 119], [144, 262]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [102]]
 b := ![[], [10, 51]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI263N0 : CertifiedPrimeIdeal' SI263N0 263 where
  n := 2
  hpos := by decide
  P := [236, 119, 1]
  hirr := P263P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4051, 3651, 867]
  a := ![0, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-367, -774, 867]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI263N0 : Ideal.IsPrime I263N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI263N0 B_one_repr
lemma NI263N0 : Nat.card (O ⧸ I263N0) = 69169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI263N0

def I263N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 0, 0], ![72, 1, 0]] i)))

def SI263N1: IdealEqSpanCertificate' Table ![![263, 0, 0], ![72, 1, 0]] 
 ![![263, 0, 0], ![72, 1, 0], ![89, 0, 1]] where
  M :=![![![263, 0, 0], ![0, 263, 0], ![0, 0, 263]], ![![72, 1, 0], ![0, 73, 3], ![327, 58, 72]]]
  hmulB := by decide  
  f := ![![![6553, 91, 0], ![-23933, 0, 0]], ![![1800, 25, 0], ![-6574, 0, 0]], ![![2263, 7, -1], ![-8265, 88, 0]]]
  g := ![![![1, 0, 0], ![-72, 263, 0], ![-89, 0, 263]], ![![0, 1, 0], ![-21, 73, 3], ![-39, 58, 72]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI263N1 : Nat.card (O ⧸ I263N1) = 263 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI263N1)

lemma isPrimeI263N1 : Ideal.IsPrime I263N1 := prime_ideal_of_norm_prime hp263.out _ NI263N1
def MulI263N0 : IdealMulLeCertificate' Table 
  ![![263, 0, 0], ![-147, -24, 1]] ![![263, 0, 0], ![72, 1, 0]]
  ![![263, 0, 0]] where
 M := ![![![69169, 0, 0], ![18936, 263, 0]], ![![-38661, -6312, 263], ![-10257, -1841, 0]]]
 hmul := by decide  
 g := ![![![![263, 0, 0]], ![![72, 1, 0]]], ![![![-147, -24, 1]], ![![-39, -7, 0]]]]
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
