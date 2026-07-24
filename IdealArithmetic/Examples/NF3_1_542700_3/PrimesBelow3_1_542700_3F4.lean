
import IdealArithmetic.Examples.NF3_1_542700_3.RI3_1_542700_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![-76, 57, 1]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0], ![-76, 57, 1]] 
 ![![197, 0, 0], ![0, 197, 0], ![121, 57, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![-76, 57, 1], ![10, -106, 285], ![570, -1708, -106]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-121, -57, 197]], ![![-1, 0, 1], ![-175, -83, 285], ![68, 22, -106]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 2 2 7 [67, 155, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [42, 196], [0, 1]]
 g := ![![[67, 178], [148], [12, 81], [187], [116], [63], [42, 1]], ![[57, 19], [148], [65, 116], [187], [116], [63], [84, 196]]]
 h' := ![![[42, 196], [190, 93], [181, 99], [57, 188], [61, 160], [97, 126], [141, 121], [0, 1]], ![[0, 1], [156, 104], [5, 98], [73, 9], [83, 37], [70, 71], [101, 76], [42, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [69]]
 b := ![[], [162, 133]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 2
  hpos := by decide
  P := [67, 155, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![87, -213, -180]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![111, 51, -180]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![-88, 1, 0]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![197, 0, 0], ![-88, 1, 0]] 
 ![![197, 0, 0], ![109, 1, 0], ![106, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![-88, 1, 0], ![0, -88, 5], ![10, -30, -88]]]
  hmulB := by decide  
  f := ![![![15665, -178, 0], ![35066, 0, 0]], ![![8713, -99, 0], ![19504, 0, 0]], ![![8386, -60, -2], ![18772, 79, 0]]]
  g := ![![![1, 0, 0], ![-109, 197, 0], ![-106, 0, 197]], ![![-1, 1, 0], ![46, -88, 5], ![64, -30, -88]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![197, 0, 0], ![-76, 57, 1]] ![![197, 0, 0], ![-88, 1, 0]]
  ![![197, 0, 0]] where
 M := ![![![38809, 0, 0], ![-17336, 197, 0]], ![![-14972, 11229, 197], ![6698, -5122, 197]]]
 hmul := by decide  
 g := ![![![![197, 0, 0]], ![![-88, 1, 0]]], ![![![-76, 57, 1]], ![![34, -26, 1]]]]
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


def P199P0 : CertificateIrreducibleZModOfList' 199 3 2 7 [192, 89, 183, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [194, 11, 16], [21, 187, 183], [0, 1]]
 g := ![![[113, 146, 8], [12, 117, 47], [46, 38, 25], [91, 169], [95, 145], [54, 57], [1]], ![[38, 144, 153, 31], [123, 176, 70, 177], [41, 66, 25, 124], [185, 132], [45, 187], [106, 178], [94, 94, 155, 116]], ![[31, 178, 73, 96], [53, 110, 119, 181], [180, 103, 58, 59], [75, 8], [14, 57], [141, 64], [56, 195, 72, 83]]]
 h' := ![![[194, 11, 16], [84, 154, 159], [123, 108, 68], [73, 76, 194], [113, 1, 186], [29, 118, 155], [7, 110, 16], [0, 1]], ![[21, 187, 183], [7, 136, 158], [176, 175, 116], [103, 94, 82], [179, 32, 172], [62, 22, 28], [135, 82, 175], [194, 11, 16]], ![[0, 1], [102, 108, 81], [137, 115, 15], [73, 29, 122], [44, 166, 40], [44, 59, 16], [101, 7, 8], [21, 187, 183]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19, 179], []]
 b := ![[], [13, 34, 51], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 3
  hpos := by decide
  P := [192, 89, 183, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4975, 18308, -27462]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-25, 92, -138]
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
