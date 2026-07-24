
import IdealArithmetic.Examples.NF3_1_89544_1.RI3_1_89544_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181797406025, -25043507134, -13137212908]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![181797406025, -25043507134, -13137212908]] 
 ![![83, 0, 0], ![0, 83, 0], ![49, 40, 1]] where
  M :=![![![181797406025, -25043507134, -13137212908], ![867056051928, -2123574687, -38180720042], ![2519927522772, 332525971340, -40304294729]]]
  hmulB := by decide  
  f := ![![![-153996026487837921941, 64793076813369110282, -11184111830890666504]], ![![738151380838783989264, -310573592120307252997, 53608964982478443778]], ![![222193472853056916941, -93486819642936403782, 16137017981297184135]]]
  g := ![![![9946034199, 6029457942, -13137212908], ![32986883542, 18374761771, -38180720042], ![54154674271, 23430093500, -40304294729]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [75, 51, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 82], [0, 1]]
 g := ![![[4, 31], [74, 38], [77], [12], [80, 28], [1]], ![[0, 52], [45, 45], [77], [12], [63, 55], [1]]]
 h' := ![![[32, 82], [11, 23], [16, 11], [8, 49], [59, 26], [8, 32], [0, 1]], ![[0, 1], [0, 60], [36, 72], [82, 34], [61, 57], [36, 51], [32, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [78, 47]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [75, 51, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-123, -75, -33]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![18, 15, -33]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![153996026487837921941, -64793076813369110282, 11184111830890666504]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![153996026487837921941, -64793076813369110282, 11184111830890666504]] 
 ![![83, 0, 0], ![42, 1, 0], ![62, 0, 1]] where
  M :=![![![153996026487837921941, -64793076813369110282, 11184111830890666504], ![-738151380838783989264, 310573592120307252997, -53608964982478443778], ![3538191688843577289348, -1488676890593482202156, 256964627137828809219]]]
  hmulB := by decide  
  f := ![![![-181797406025, 25043507134, 13137212908]], ![![-102440326566, 12698203305, 7107754966]], ![![-166161044534, 14700861096, 10298933675]]]
  g := ![![![26287835170290593139, -64793076813369110282, 11184111830890666504], ![-126005860493711145794, 310573592120307252997, -53608964982478443778], ![603985713388246308534, -1488676890593482202156, 256964627137828809219]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![181797406025, -25043507134, -13137212908]] ![![153996026487837921941, -64793076813369110282, 11184111830890666504]]
  ![![83, 0, 0]] where
 M := ![![![-83, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC83 : ContainsPrimesAboveP 83 ![I83N0, I83N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 83 (by decide) (𝕀 ⊙ MulI83N0)


lemma PB85I2_primes (p : ℕ) :
  p ∈ Set.range ![83] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 84 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 84 (by omega)

def PB85I2 : PrimesBelowBoundCertificateInterval O 79 84 85 where
  m := 1
  g := ![2]
  P := ![83]
  hP := PB85I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC83
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![6889, 83]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
  β := ![I83N1]
  Il := ![[I83N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
