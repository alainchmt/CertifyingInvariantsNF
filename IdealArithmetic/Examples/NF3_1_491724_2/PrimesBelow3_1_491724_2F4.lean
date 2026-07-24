
import IdealArithmetic.Examples.NF3_1_491724_2.RI3_1_491724_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![217, 58, 4]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![217, 58, 4]] 
 ![![197, 0, 0], ![0, 197, 0], ![5, 113, 1]] where
  M :=![![![217, 58, 4], ![3048, 841, 58], ![44196, 12096, 841]]]
  hmulB := by decide  
  f := ![![![29, -2, 0]], ![![0, 29, -2]], ![![-7, 15, -1]]]
  g := ![![![1, -2, 4], ![14, -29, 58], ![203, -421, 841]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 2 2 7 [56, 38, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [159, 196], [0, 1]]
 g := ![![[64, 64], [42], [75, 104], [190], [187], [81], [159, 1]], ![[193, 133], [42], [63, 93], [190], [187], [81], [121, 196]]]
 h' := ![![[159, 196], [41, 189], [134, 150], [133, 164], [23, 92], [137, 160], [158, 9], [0, 1]], ![[0, 1], [148, 8], [147, 47], [8, 33], [73, 105], [164, 37], [13, 188], [159, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31]]
 b := ![[], [196, 114]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 2
  hpos := by decide
  P := [56, 38, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1580, 1036, 119]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5, -63, 119]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-29, 2, 0]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![-29, 2, 0]] 
 ![![197, 0, 0], ![84, 1, 0], ![36, 0, 1]] where
  M :=![![![-29, 2, 0], ![0, -29, 2], ![1524, 312, -29]]]
  hmulB := by decide  
  f := ![![![-217, -58, -4]], ![![-108, -29, -2]], ![![-264, -72, -5]]]
  g := ![![![-1, 2, 0], ![12, -29, 2], ![-120, 312, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![217, 58, 4]] ![![-29, 2, 0]]
  ![![197, 0, 0]] where
 M := ![![![-197, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC197 : ContainsPrimesAboveP 197 ![I197N0, I197N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
    exact isPrimeI197N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 197 (by decide) (𝕀 ⊙ MulI197N0)


lemma PB199I4_primes (p : ℕ) :
  p ∈ Set.range ![197] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 198 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 198 (by omega)

def PB199I4 : PrimesBelowBoundCertificateInterval O 193 198 199 where
  m := 1
  g := ![2]
  P := ![197]
  hP := PB199I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC197
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![38809, 197]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
      exact NI197N1
  β := ![I197N1]
  Il := ![[I197N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
