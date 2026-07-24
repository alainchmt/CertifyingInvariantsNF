
import IdealArithmetic.Examples.NF3_1_551980_3.RI3_1_551980_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![64, 92, 1]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0], ![64, 92, 1]] 
 ![![197, 0, 0], ![0, 197, 0], ![64, 92, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![64, 92, 1], ![-155, 85, 93], ![-14415, 1798, 178]]]
  hmulB := by decide  
  f := ![![![-63, -92, -1], ![197, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-64, -92, 197]], ![![0, 0, 1], ![-31, -43, 93], ![-131, -74, 178]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 2 2 7 [45, 167, 1] where
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
 g := ![![[65, 104], [70], [4, 158], [26], [88], [155], [30, 1]], ![[33, 93], [70], [16, 39], [26], [88], [155], [60, 196]]]
 h' := ![![[30, 196], [94, 33], [17, 142], [146, 143], [118, 115], [170, 65], [29, 67], [0, 1]], ![[0, 1], [99, 164], [140, 55], [102, 54], [22, 82], [150, 132], [69, 130], [30, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58]]
 b := ![[], [156, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 2
  hpos := by decide
  P := [45, 167, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-420, -259, -142]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![44, 65, -142]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![-93, 1, 0]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![197, 0, 0], ![-93, 1, 0]] 
 ![![197, 0, 0], ![104, 1, 0], ![19, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![-93, 1, 0], ![0, -93, 1], ![-155, 21, -92]]]
  hmulB := by decide  
  f := ![![![17206, -185, 0], ![36445, 0, 0]], ![![9022, -97, 0], ![19110, 0, 0]], ![![1718, -18, 0], ![3639, 1, 0]]]
  g := ![![![1, 0, 0], ![-104, 197, 0], ![-19, 0, 197]], ![![-1, 1, 0], ![49, -93, 1], ![-3, 21, -92]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![197, 0, 0], ![64, 92, 1]] ![![197, 0, 0], ![-93, 1, 0]]
  ![![197, 0, 0]] where
 M := ![![![38809, 0, 0], ![-18321, 197, 0]], ![![12608, 18124, 197], ![-6107, -8471, 0]]]
 hmul := by decide  
 g := ![![![![197, 0, 0]], ![![-93, 1, 0]]], ![![![64, 92, 1]], ![![-31, -43, 0]]]]
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


def P199P0 : CertificateIrreducibleZModOfList' 199 3 2 7 [77, 178, 75, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [51, 107, 191], [73, 91, 8], [0, 1]]
 g := ![![[188, 174, 128], [167, 192, 160], [51, 74, 124], [8, 63], [42, 104], [39, 53], [1]], ![[80, 54, 95, 137], [126, 118, 173, 179], [174, 86, 167, 170], [174, 26], [197, 132], [154, 187], [64, 63, 40, 85]], ![[14, 2, 20, 116], [166, 12, 111, 28], [34, 175, 135, 126], [102, 158], [0, 9], [35, 62], [109, 122, 166, 114]]]
 h' := ![![[51, 107, 191], [76, 89, 160], [53, 12, 110], [96, 30, 70], [48, 18, 137], [140, 71, 30], [122, 21, 124], [0, 1]], ![[73, 91, 8], [84, 72, 117], [25, 147, 163], [79, 8, 160], [187, 168, 184], [113, 141, 172], [164, 191, 171], [51, 107, 191]], ![[0, 1], [36, 38, 121], [79, 40, 125], [135, 161, 168], [32, 13, 77], [80, 186, 196], [136, 186, 103], [73, 91, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [184, 2], []]
 b := ![[], [89, 157, 50], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 3
  hpos := by decide
  P := [77, 178, 75, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![681973, -282182, 25870]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3427, -1418, 130]
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



lemma PB211I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 210 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 210 (by omega)

def PB211I4 : PrimesBelowBoundCertificateInterval O 193 210 211 where
  m := 2
  g := ![2, 1]
  P := ![197, 199]
  hP := PB211I4_primes
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
