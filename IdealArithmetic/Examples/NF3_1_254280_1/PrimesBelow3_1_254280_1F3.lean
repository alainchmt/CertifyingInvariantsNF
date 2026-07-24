
import IdealArithmetic.Examples.NF3_1_254280_1.RI3_1_254280_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1565275254812073079, 173019805174040202, -79199635265189110]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![-1565275254812073079, 173019805174040202, -79199635265189110]] 
 ![![139, 0, 0], ![0, 139, 0], ![54, 76, 1]] where
  M :=![![![-1565275254812073079, 173019805174040202, -79199635265189110], ![7127967173867019900, -787899436803843961, 360660144991742386], ![-8443815291796598280, 933348477988703756, -427239291812101575]]]
  hmulB := by decide  
  f := ![![![793095419, 143523590, -25862858]], ![![2327657220, 959926125, 378845054]], ![![1504601694, 575288956, 206722309]]]
  g := ![![![19507230572000999, 44548144498765558, -79199635265189110], ![-88832234933000496, -202863816231483923, 360660144991742386], ![105230981770193430, 240313198961931104, -427239291812101575]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [23, 52, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [87, 138], [0, 1]]
 g := ![![[105, 37], [27, 96], [5], [133, 29], [137], [63], [1]], ![[127, 102], [39, 43], [5], [15, 110], [137], [63], [1]]]
 h' := ![![[87, 138], [74, 71], [25, 42], [138, 127], [75, 86], [53, 89], [116, 87], [0, 1]], ![[0, 1], [135, 68], [65, 97], [67, 12], [51, 53], [12, 50], [40, 52], [87, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [96]]
 b := ![[], [136, 48]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [23, 52, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-697, -461, -381]
  a := ![0, 1, -4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![143, 205, -381]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-793095419, -143523590, 25862858]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![-793095419, -143523590, 25862858]] 
 ![![139, 0, 0], ![48, 1, 0], ![82, 0, 1]] where
  M :=![![![-793095419, -143523590, 25862858], ![-2327657220, -959926125, -378845054], ![10589465880, 739494476, -1338771179]]]
  hmulB := by decide  
  f := ![![![1565275254812073079, -173019805174040202, 79199635265189110]], ![![489246367317356028, -54079505119065365, 24754837034081546]], ![![984146663211414322, -108783974836402880, 49795750960846105]]]
  g := ![![![28599155, -143523590, 25862858], ![538230872, -959926125, -378845054], ![610596890, 739494476, -1338771179]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![-1565275254812073079, 173019805174040202, -79199635265189110]] ![![-793095419, -143523590, 25862858]]
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


lemma PB143I3_primes (p : ℕ) :
  p ∈ Set.range ![139] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 142 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 142 (by omega)

def PB143I3 : PrimesBelowBoundCertificateInterval O 137 142 143 where
  m := 1
  g := ![2]
  P := ![139]
  hP := PB143I3_primes
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
