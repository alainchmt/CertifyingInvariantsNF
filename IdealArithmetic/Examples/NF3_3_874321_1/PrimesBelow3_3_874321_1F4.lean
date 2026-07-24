
import IdealArithmetic.Examples.NF3_3_874321_1.RI3_3_874321_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 40, 15]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![61, 40, 15]] 
 ![![197, 0, 0], ![0, 197, 0], ![96, 134, 1]] where
  M :=![![![61, 40, 15], ![2655, 911, 120], ![6195, 3045, 871]]]
  hmulB := by decide  
  f := ![![![-2173, -55, 45]], ![![7965, 202, -165]], ![![4296, 109, -89]]]
  g := ![![![-7, -10, 15], ![-45, -77, 120], ![-393, -577, 871]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 2 2 7 [4, 170, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [27, 196], [0, 1]]
 g := ![![[141, 148], [54], [41, 55], [127], [100], [29], [27, 1]], ![[0, 49], [54], [147, 142], [127], [100], [29], [54, 196]]]
 h' := ![![[27, 196], [85, 99], [33, 60], [54, 45], [103, 18], [122, 10], [89, 134], [0, 1]], ![[0, 1], [0, 98], [77, 137], [87, 152], [195, 179], [195, 187], [161, 63], [27, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [113]]
 b := ![[], [173, 155]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 2
  hpos := by decide
  P := [4, 170, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2069, 2219, 512]
  a := ![0, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-239, -337, 512]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2173, 55, -45]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![2173, 55, -45]] 
 ![![197, 0, 0], ![189, 1, 0], ![47, 0, 1]] where
  M :=![![![2173, 55, -45], ![-7965, -202, 165], ![12390, 315, -257]]]
  hmulB := by decide  
  f := ![![![-61, -40, -15]], ![![-72, -43, -15]], ![![-46, -25, -8]]]
  g := ![![![-31, 55, -45], ![114, -202, 165], ![-178, 315, -257]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![61, 40, 15]] ![![2173, 55, -45]]
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


def P199P0 : CertificateIrreducibleZModOfList' 199 3 2 7 [173, 104, 59, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [20, 13, 52], [120, 185, 147], [0, 1]]
 g := ![![[62, 118, 52], [64, 145, 7], [187, 58, 123], [162, 49], [2, 140], [122, 98], [1]], ![[58, 13, 143, 72], [172, 133, 100, 86], [181, 26, 6, 66], [137, 57], [170, 106], [11, 25], [23, 94, 26, 114]], ![[89, 103, 96, 67], [102, 172, 177, 176], [77, 61, 57, 137], [66, 81], [155, 90], [176, 116], [192, 72, 21, 85]]]
 h' := ![![[20, 13, 52], [72, 132, 98], [86, 86, 112], [135, 110, 83], [163, 147, 7], [67, 173, 109], [26, 95, 140], [0, 1]], ![[120, 185, 147], [99, 47, 119], [99, 35, 118], [59, 185, 180], [173, 15, 183], [176, 17, 107], [41, 130, 194], [20, 13, 52]], ![[0, 1], [183, 20, 181], [191, 78, 168], [113, 103, 135], [63, 37, 9], [49, 9, 182], [100, 173, 64], [120, 185, 147]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48, 115], []]
 b := ![[], [152, 147, 170], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 3
  hpos := by decide
  P := [173, 104, 59, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1641153, 1131713, 448546]
  a := ![-1, 1, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![8247, 5687, 2254]
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



lemma PB208I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 207 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 207 (by omega)

def PB208I4 : PrimesBelowBoundCertificateInterval O 193 207 208 where
  m := 2
  g := ![2, 1]
  P := ![197, 199]
  hP := PB208I4_primes
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
