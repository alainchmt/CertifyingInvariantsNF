
import IdealArithmetic.Examples.NF3_1_547128_1.RI3_1_547128_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0]] 
 ![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 3 2 7 [82, 59, 78, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [98, 30, 7], [21, 166, 190], [0, 1]]
 g := ![![[191, 139, 134], [39, 143], [28, 181, 160], [63, 104], [42, 81], [163, 174], [1]], ![[138, 171, 10, 132], [31, 146], [73, 36, 109, 138], [77, 136], [95, 178], [46, 43], [21, 40, 114, 146]], ![[187, 135, 2, 92], [39, 36], [100, 193, 193, 181], [167, 191], [129, 160], [119, 76], [107, 58, 133, 51]]]
 h' := ![![[98, 30, 7], [47, 19, 118], [68, 83, 52], [63, 105, 95], [86, 97, 33], [56, 172, 188], [115, 138, 119], [0, 1]], ![[21, 166, 190], [104, 45, 21], [171, 105, 151], [140, 168, 154], [97, 97, 50], [106, 53, 104], [174, 133, 35], [98, 30, 7]], ![[0, 1], [191, 133, 58], [146, 9, 191], [71, 121, 145], [70, 3, 114], [73, 169, 102], [93, 123, 43], [21, 166, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21, 15], []]
 b := ![[], [93, 88, 26], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 3
  hpos := by decide
  P := [82, 59, 78, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-236006, -2364, -3940]
  a := ![-1, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1198, -12, -20]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 7645373 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def PBC197 : ContainsPrimesAboveP 197 ![I197N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![197, 0, 0]]) timesTableT_eq_Table B_one_repr 197 (by decide) 𝕀

instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4423491462955205, -716444684387407, -407394307328632]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![-4423491462955205, -716444684387407, -407394307328632]] 
 ![![199, 0, 0], ![102, 1, 0], ![113, 0, 1]] where
  M :=![![![-4423491462955205, -716444684387407, -407394307328632], ![-60097669624097822, -9733636044476625, -5534869614559542], ![-56725083516322560, -9187399794268026, -5224261491363265]]]
  hmulB := by decide  
  f := ![![![1607623467, -43516577, -79260594]], ![![766216256, -17490941, -41219618]], ![![926787801, -30802009, -39638707]]]
  g := ![![![576328759159275, -716444684387407, -407394307328632], ![7830017454059026, -9733636044476625, -5534869614559542], ![7390609266447563, -9187399794268026, -5224261491363265]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N0 : Nat.card (O ⧸ I199N0) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N0)

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := prime_ideal_of_norm_prime hp199.out _ NI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![-57, 1, 0]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![199, 0, 0], ![-57, 1, 0]] 
 ![![199, 0, 0], ![142, 1, 0], ![116, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![-57, 1, 0], ![2, -53, 10], ![144, 6, -61]]]
  hmulB := by decide  
  f := ![![![17419, -518938, 97920], ![-7562, -1948608, 0]], ![![12436, -370284, 69870], ![-5372, -1390413, 0]], ![![10181, -302497, 57079], ![-4313, -1135872, 0]]]
  g := ![![![1, 0, 0], ![-142, 199, 0], ![-116, 0, 199]], ![![-1, 1, 0], ![32, -53, 10], ![32, 6, -61]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1

def I199N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![-45, 1, 0]] i)))

def SI199N2: IdealEqSpanCertificate' Table ![![199, 0, 0], ![-45, 1, 0]] 
 ![![199, 0, 0], ![154, 1, 0], ![154, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![-45, 1, 0], ![2, -41, 10], ![144, 6, -49]]]
  hmulB := by decide  
  f := ![![![27958, -616429, 150360], ![-9353, -2992164, 0]], ![![21651, -476999, 116350], ![-7163, -2315365, 0]], ![![21658, -477036, 116359], ![-7140, -2315544, 0]]]
  g := ![![![1, 0, 0], ![-154, 199, 0], ![-154, 0, 199]], ![![-1, 1, 0], ![24, -41, 10], ![34, 6, -49]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N2 : Nat.card (O ⧸ I199N2) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N2)

lemma isPrimeI199N2 : Ideal.IsPrime I199N2 := prime_ideal_of_norm_prime hp199.out _ NI199N2
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![-4423491462955205, -716444684387407, -407394307328632]] ![![199, 0, 0], ![-57, 1, 0]]
  ![![199, 0, 0], ![-24, -15, 1]] where
 M := ![![![-880274801128085795, -142572492193093993, -81071467158397768], ![192041343764348863, 31103710965605574, 17686605903172482]]]
 hmul := by decide  
 g := ![![![![-4354286856721349, -673191805491247, -410277832588376], ![573821526689056, 0, 0]], ![![949934154685129, 146863977898746, 89506488412510], ![-125185290917008, 0, 0]]]]
 hle2 := by decide  

def MulI199N1 : IdealMulLeCertificate' Table 
  ![![199, 0, 0], ![-24, -15, 1]] ![![199, 0, 0], ![-45, 1, 0]]
  ![![199, 0, 0]] where
 M := ![![![39601, 0, 0], ![-8955, 199, 0]], ![![-4776, -2985, 199], ![1194, 597, -199]]]
 hmul := by decide  
 g := ![![![![199, 0, 0]], ![![-45, 1, 0]]], ![![![-24, -15, 1]], ![![6, 3, -1]]]]
 hle2 := by decide  


def PBC199 : ContainsPrimesAboveP 199 ![I199N0, I199N1, I199N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI199N0
    exact isPrimeI199N1
    exact isPrimeI199N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 199 (by decide) (𝕀 ⊙ MulI199N0 ⊙ MulI199N1)


lemma PB210I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 209 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 209 (by omega)

def PB210I4 : PrimesBelowBoundCertificateInterval O 193 209 210 where
  m := 2
  g := ![1, 3]
  P := ![197, 199]
  hP := PB210I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0]
    · exact ![I199N0, I199N1, I199N2]
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
    · exact ![7645373]
    · exact ![199, 199, 199]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
    · dsimp ; intro j
      fin_cases j
      exact NI199N0
      exact NI199N1
      exact NI199N2
  β := ![I199N0, I199N1, I199N2]
  Il := ![[], [I199N0, I199N1, I199N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
