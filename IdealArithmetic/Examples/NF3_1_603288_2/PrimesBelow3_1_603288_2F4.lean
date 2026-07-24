
import IdealArithmetic.Examples.NF3_1_603288_2.RI3_1_603288_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![88, 59, 1]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0], ![88, 59, 1]] 
 ![![197, 0, 0], ![0, 197, 0], ![88, 59, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![88, 59, 1], ![140, 67, 118], ![8260, -1169, 67]]]
  hmulB := by decide  
  f := ![![![-87, -59, -1], ![197, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-88, -59, 197]], ![![0, 0, 1], ![-52, -35, 118], ![12, -26, 67]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 2 2 7 [97, 167, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [30, 196], [0, 1]]
 g := ![![[20, 65], [174], [172, 181], [105], [135], [28], [30, 1]], ![[0, 132], [174], [86, 16], [105], [135], [28], [60, 196]]]
 h' := ![![[30, 196], [42, 38], [61, 119], [156, 141], [57, 41], [97, 23], [45, 15], [0, 1]], ![[0, 1], [0, 159], [85, 78], [52, 56], [105, 156], [196, 174], [101, 182], [30, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [47, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 2
  hpos := by decide
  P := [97, 167, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![377, -139, -186]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![85, 55, -186]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![79, 1, 0]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![197, 0, 0], ![79, 1, 0]] 
 ![![197, 0, 0], ![79, 1, 0], ![130, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![79, 1, 0], ![0, 79, 2], ![140, -21, 79]]]
  hmulB := by decide  
  f := ![![![238, 3, 0], ![-591, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![214, -37, -1], ![-532, 99, 0]]]
  g := ![![![1, 0, 0], ![-79, 197, 0], ![-130, 0, 197]], ![![0, 1, 0], ![-33, 79, 2], ![-43, -21, 79]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![197, 0, 0], ![88, 59, 1]] ![![197, 0, 0], ![79, 1, 0]]
  ![![197, 0, 0]] where
 M := ![![![38809, 0, 0], ![15563, 197, 0]], ![![17336, 11623, 197], ![7092, 4728, 197]]]
 hmul := by decide  
 g := ![![![![197, 0, 0]], ![![79, 1, 0]]], ![![![88, 59, 1]], ![![36, 24, 1]]]]
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


def P199P0 : CertificateIrreducibleZModOfList' 199 3 2 7 [125, 146, 129, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [152, 167, 124], [117, 31, 75], [0, 1]]
 g := ![![[115, 21, 20], [168, 139, 144], [115, 96, 80], [20, 126], [16, 62], [180, 124], [1]], ![[148, 42, 4, 36], [42, 50, 59, 172], [194, 13, 152, 33], [172, 81], [23, 1], [154, 196], [57, 71, 38, 5]], ![[130, 118, 193, 192], [86, 172, 37, 166], [97, 181, 82, 44], [179, 175], [25, 56], [125, 151], [195, 82, 2, 194]]]
 h' := ![![[152, 167, 124], [94, 106, 47], [152, 75, 12], [72, 169, 105], [130, 87, 153], [90, 93, 103], [74, 53, 70], [0, 1]], ![[117, 31, 75], [144, 72, 74], [105, 123, 120], [174, 2, 132], [88, 181, 9], [133, 123, 198], [94, 186, 185], [152, 167, 124]], ![[0, 1], [165, 21, 78], [50, 1, 67], [130, 28, 161], [60, 130, 37], [198, 182, 97], [163, 159, 143], [117, 31, 75]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20, 52], []]
 b := ![[], [32, 34, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 3
  hpos := by decide
  P := [125, 146, 129, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![209547, 13532, -20298]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1053, 68, -102]
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

instance hp211 : Fact (Nat.Prime 211) := {out := by norm_num}

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![211, 0, 0]] 
 ![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 3 2 7 [32, 8, 150, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [36, 179, 68], [25, 31, 143], [0, 1]]
 g := ![![[78, 179, 6], [90, 173, 99], [6, 113], [124, 169], [15, 150, 120], [24, 134], [1]], ![[178, 157, 157, 115], [172, 205, 72, 38], [15, 24], [83, 62], [102, 62, 154, 162], [156, 20], [33, 97, 70, 42]], ![[152, 82, 202, 144], [130, 42, 129, 79], [102, 73], [30, 81], [117, 208, 139, 37], [1, 119], [11, 95, 195, 169]]]
 h' := ![![[36, 179, 68], [74, 119, 165], [16, 22, 164], [29, 49, 18], [153, 59, 198], [45, 41, 139], [179, 203, 61], [0, 1]], ![[25, 31, 143], [55, 97, 125], [159, 153, 39], [165, 124, 92], [194, 55, 22], [15, 149, 134], [24, 82, 81], [36, 179, 68]], ![[0, 1], [25, 206, 132], [100, 36, 8], [153, 38, 101], [67, 97, 202], [199, 21, 149], [81, 137, 69], [25, 31, 143]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [165, 116], []]
 b := ![[], [164, 34, 110], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 3
  hpos := by decide
  P := [32, 8, 150, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![345196, -7807, 7807]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1636, -37, 37]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 9393931 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def PBC211 : ContainsPrimesAboveP 211 ![I211N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI211N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![211, 0, 0]]) timesTableT_eq_Table B_one_repr 211 (by decide) 𝕀



lemma PB220I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 219 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 219 (by omega)

def PB220I4 : PrimesBelowBoundCertificateInterval O 193 219 220 where
  m := 3
  g := ![2, 1, 1]
  P := ![197, 199, 211]
  hP := PB220I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1]
    · exact ![I199N0]
    · exact ![I211N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC197
    · exact PBC199
    · exact PBC211
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![38809, 197]
    · exact ![7880599]
    · exact ![9393931]
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
    · dsimp ; intro j
      fin_cases j
      exact NI211N0
  β := ![I197N1]
  Il := ![[I197N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
