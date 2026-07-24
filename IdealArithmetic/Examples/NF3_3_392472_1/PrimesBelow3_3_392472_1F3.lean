
import IdealArithmetic.Examples.NF3_3_392472_1.RI3_3_392472_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2050, 4, 55]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![-2050, 4, 55]] 
 ![![139, 0, 0], ![0, 139, 0], ![127, 86, 1]] where
  M :=![![![-2050, 4, 55], ![1815, -11, -47], ![-1683, 38, 36]]]
  hmulB := by decide  
  f := ![![![-10, -14, -3]], ![![-99, -135, -25]], ![![-73, -100, -19]]]
  g := ![![![-65, -34, 55], ![56, 29, -47], ![-45, -22, 36]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [59, 63, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [76, 138], [0, 1]]
 g := ![![[133, 5], [60, 54], [30], [87, 28], [28], [77], [1]], ![[96, 134], [133, 85], [30], [130, 111], [28], [77], [1]]]
 h' := ![![[76, 138], [74, 127], [137, 38], [10, 13], [14, 81], [50, 81], [80, 76], [0, 1]], ![[0, 1], [135, 12], [106, 101], [25, 126], [54, 58], [90, 58], [18, 63], [76, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [24, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [59, 63, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![158, 304, 149]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-135, -90, 149]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10, 14, 3]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![10, 14, 3]] 
 ![![139, 0, 0], ![107, 1, 0], ![60, 0, 1]] where
  M :=![![![10, 14, 3], ![99, 135, 25], ![363, 512, 110]]]
  hmulB := by decide  
  f := ![![![2050, -4, -55]], ![![1565, -3, -42]], ![![897, -2, -24]]]
  g := ![![![-12, 14, 3], ![-114, 135, 25], ![-439, 512, 110]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![-2050, 4, 55]] ![![10, 14, 3]]
  ![![139, 0, 0]] where
 M := ![![![-139, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC139 : ContainsPrimesAboveP 139 ![I139N0, I139N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
    exact isPrimeI139N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 139 (by decide) (𝕀 ⊙ MulI139N0)


lemma PB140I3_primes (p : ℕ) :
  p ∈ Set.range ![139] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 139 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 139 (by omega)

def PB140I3 : PrimesBelowBoundCertificateInterval O 137 139 140 where
  m := 1
  g := ![2]
  P := ![139]
  hP := PB140I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC139
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![19321, 139]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
      exact NI139N1
  β := ![I139N1]
  Il := ![[I139N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
