
import IdealArithmetic.Examples.NF3_1_542700_2.RI3_1_542700_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![589, 121, 45]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![589, 121, 45]] 
 ![![197, 0, 0], ![0, 197, 0], ![70, 99, 1]] where
  M :=![![![589, 121, 45], ![9450, 1939, 726], ![25410, 5205, 1939]]]
  hmulB := by decide  
  f := ![![![-97, -2, 3]], ![![630, -7, -12]], ![![280, -4, -5]]]
  g := ![![![-13, -22, 45], ![-210, -355, 726], ![-560, -948, 1939]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 2 2 7 [185, 154, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [43, 196], [0, 1]]
 g := ![![[20, 171], [132], [151, 173], [16], [175], [61], [43, 1]], ![[84, 26], [132], [104, 24], [16], [175], [61], [86, 196]]]
 h' := ![![[43, 196], [150, 34], [39, 59], [54, 166], [181, 4], [53, 61], [122, 88], [0, 1]], ![[0, 1], [36, 163], [15, 138], [100, 31], [156, 193], [115, 136], [163, 109], [43, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [108]]
 b := ![[], [21, 54]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 2
  hpos := by decide
  P := [185, 154, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![605, -59, -118]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![45, 59, -118]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 2, -3]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![97, 2, -3]] 
 ![![197, 0, 0], ![194, 1, 0], ![97, 0, 1]] where
  M :=![![![97, 2, -3], ![-630, 7, 12], ![420, -45, 7]]]
  hmulB := by decide  
  f := ![![![-589, -121, -45]], ![![-628, -129, -48]], ![![-419, -86, -32]]]
  g := ![![![0, 2, -3], ![-16, 7, 12], ![43, -45, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![589, 121, 45]] ![![97, 2, -3]]
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
instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![199, 0, 0]] 
 ![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 3 2 7 [149, 57, 22, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [92, 59, 78], [85, 139, 121], [0, 1]]
 g := ![![[169, 181, 50], [83, 62, 188], [174, 168, 56], [6, 158], [24, 106], [19, 86], [1]], ![[16, 185, 136, 39], [81, 31, 146, 107], [63, 59, 58, 78], [28, 116], [130, 50], [75, 180], [88, 86, 72, 136]], ![[165, 134, 11, 25], [112, 110, 76, 100], [6, 65, 180, 123], [141, 180], [36, 64], [61, 102], [182, 127, 183, 63]]]
 h' := ![![[92, 59, 78], [170, 112, 99], [143, 172, 136], [59, 118, 97], [117, 157, 77], [67, 104, 107], [50, 142, 177], [0, 1]], ![[85, 139, 121], [32, 116, 10], [143, 96, 82], [97, 173, 1], [182, 101, 64], [100, 36, 100], [23, 136, 58], [92, 59, 78]], ![[0, 1], [47, 170, 90], [113, 130, 180], [82, 107, 101], [14, 140, 58], [123, 59, 191], [156, 120, 163], [85, 139, 121]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [105, 128], []]
 b := ![[], [3, 74, 80], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 3
  hpos := by decide
  P := [149, 57, 22, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-199597, 13333, 25074]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1003, 67, 126]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 7880599 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def PBC199 : ContainsPrimesAboveP 199 ![I199N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI199N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![199, 0, 0]]) timesTableT_eq_Table B_one_repr 199 (by decide) 𝕀



lemma PB209I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 208 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 208 (by omega)

def PB209I4 : PrimesBelowBoundCertificateInterval O 193 208 209 where
  m := 2
  g := ![2, 1]
  P := ![197, 199]
  hP := PB209I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1]
    · exact ![I199N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC197
    · exact PBC199
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![38809, 197]
    · exact ![7880599]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
      exact NI197N1
    · dsimp ; intro j
      fin_cases j
      exact NI199N0
  β := ![I197N1]
  Il := ![[I197N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
