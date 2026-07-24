
import IdealArithmetic.Examples.NF3_1_592379_1.RI3_1_592379_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![35, 1, 0]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0], ![35, 1, 0]] 
 ![![197, 0, 0], ![35, 1, 0], ![154, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![35, 1, 0], ![0, 35, 1], ![86, -49, 36]]]
  hmulB := by decide  
  f := ![![![3851, 110, 0], ![-21670, 0, 0]], ![![665, 19, 0], ![-3742, 0, 0]], ![![3052, 87, 0], ![-17174, 1, 0]]]
  g := ![![![1, 0, 0], ![-35, 197, 0], ![-154, 0, 197]], ![![0, 1, 0], ![-7, 35, 1], ![-19, -49, 36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N0 : Nat.card (O ⧸ I197N0) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N0)

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := prime_ideal_of_norm_prime hp197.out _ NI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![-18, 1, 0]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![197, 0, 0], ![-18, 1, 0]] 
 ![![197, 0, 0], ![179, 1, 0], ![70, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![-18, 1, 0], ![0, -18, 1], ![86, -49, -17]]]
  hmulB := by decide  
  f := ![![![235, -13, 0], ![2561, 0, 0]], ![![217, -12, 0], ![2365, 0, 0]], ![![110, -6, 0], ![1200, 1, 0]]]
  g := ![![![1, 0, 0], ![-179, 197, 0], ![-70, 0, 197]], ![![-1, 1, 0], ![16, -18, 1], ![51, -49, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![197, 0, 0], ![35, 1, 0]] ![![197, 0, 0], ![-18, 1, 0]]
  ![![197, 0, 0], ![-39, 17, 1]] where
 M := ![![![38809, 0, 0], ![-3546, 197, 0]], ![![6895, 197, 0], ![-630, 17, 1]]]
 hmul := by decide  
 g := ![![![![197, 0, 0], ![0, 0, 0]], ![![21, -16, -1], ![197, 0, 0]]], ![![![35, 1, 0], ![0, 0, 0]], ![![-3, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI197N1 : IdealMulLeCertificate' Table 
  ![![197, 0, 0], ![-39, 17, 1]] ![![197, 0, 0], ![-18, 1, 0]]
  ![![197, 0, 0]] where
 M := ![![![38809, 0, 0], ![-3546, 197, 0]], ![![-7683, 3349, 197], ![788, -394, 0]]]
 hmul := by decide  
 g := ![![![![197, 0, 0]], ![![-18, 1, 0]]], ![![![-39, 17, 1]], ![![4, -2, 0]]]]
 hle2 := by decide  


def PBC197 : ContainsPrimesAboveP 197 ![I197N0, I197N1, I197N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
    exact isPrimeI197N1
    exact isPrimeI197N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 197 (by decide) (𝕀 ⊙ MulI197N0 ⊙ MulI197N1)
instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![48, 92, 1]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![199, 0, 0], ![48, 92, 1]] 
 ![![199, 0, 0], ![0, 199, 0], ![48, 92, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![48, 92, 1], ![86, -1, 93], ![7998, -4471, 92]]]
  hmulB := by decide  
  f := ![![![-47, -92, -1], ![199, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-48, -92, 199]], ![![0, 0, 1], ![-22, -43, 93], ![18, -65, 92]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 2 2 7 [125, 117, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [82, 198], [0, 1]]
 g := ![![[28, 121], [109, 98], [123, 90], [116], [92], [29], [82, 1]], ![[0, 78], [185, 101], [140, 109], [116], [92], [29], [164, 198]]]
 h' := ![![[82, 198], [106, 188], [147, 59], [32, 182], [123, 64], [9, 93], [98, 32], [0, 1]], ![[0, 1], [0, 11], [10, 140], [31, 17], [197, 135], [73, 106], [135, 167], [82, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [94]]
 b := ![[], [63, 47]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 2
  hpos := by decide
  P := [125, 117, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![383, -178, -162]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![41, 74, -162]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![-93, 1, 0]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![199, 0, 0], ![-93, 1, 0]] 
 ![![199, 0, 0], ![106, 1, 0], ![107, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![-93, 1, 0], ![0, -93, 1], ![86, -49, -92]]]
  hmulB := by decide  
  f := ![![![13486, -145, 0], ![28855, 0, 0]], ![![7348, -79, 0], ![15722, 0, 0]], ![![7298, -78, 0], ![15615, 1, 0]]]
  g := ![![![1, 0, 0], ![-106, 199, 0], ![-107, 0, 199]], ![![-1, 1, 0], ![49, -93, 1], ![76, -49, -92]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![199, 0, 0], ![48, 92, 1]] ![![199, 0, 0], ![-93, 1, 0]]
  ![![199, 0, 0]] where
 M := ![![![39601, 0, 0], ![-18507, 199, 0]], ![![9552, 18308, 199], ![-4378, -8557, 0]]]
 hmul := by decide  
 g := ![![![![199, 0, 0]], ![![-93, 1, 0]]], ![![![48, 92, 1]], ![![-22, -43, 0]]]]
 hle2 := by decide  


def PBC199 : ContainsPrimesAboveP 199 ![I199N0, I199N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI199N0
    exact isPrimeI199N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 199 (by decide) (𝕀 ⊙ MulI199N0)
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


def P211P0 : CertificateIrreducibleZModOfList' 211 3 2 7 [167, 156, 85, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [18, 30, 167], [108, 180, 44], [0, 1]]
 g := ![![[10, 192, 189], [61, 18, 201], [107, 139], [178, 161], [86, 126, 189], [30, 51], [1]], ![[58, 2, 48, 35], [84, 176, 142, 153], [38, 119], [156, 137], [166, 113, 199, 28], [3, 16], [41, 23, 129, 60]], ![[143, 33, 187, 196], [62, 129, 177, 79], [102, 58], [69, 51], [138, 140, 16, 113], [33, 20], [72, 11, 182, 151]]]
 h' := ![![[18, 30, 167], [152, 53, 20], [166, 171, 137], [10, 147, 75], [197, 198, 43], [91, 83, 20], [44, 55, 126], [0, 1]], ![[108, 180, 44], [198, 95, 2], [147, 6, 45], [95, 17, 69], [163, 141, 83], [44, 151, 159], [40, 144, 4], [18, 30, 167]], ![[0, 1], [87, 63, 189], [111, 34, 29], [138, 47, 67], [30, 83, 85], [101, 188, 32], [45, 12, 81], [108, 180, 44]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [178, 103], []]
 b := ![[], [189, 34, 151], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 3
  hpos := by decide
  P := [167, 156, 85, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![178717, -151287, 28274]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![847, -717, 134]
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



lemma PB218I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 217 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 217 (by omega)

def PB218I4 : PrimesBelowBoundCertificateInterval O 193 217 218 where
  m := 3
  g := ![3, 2, 1]
  P := ![197, 199, 211]
  hP := PB218I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1, I197N1]
    · exact ![I199N0, I199N1]
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
    · exact ![197, 197, 197]
    · exact ![39601, 199]
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
      exact NI197N1
    · dsimp ; intro j
      fin_cases j
      exact NI199N0
      exact NI199N1
    · dsimp ; intro j
      fin_cases j
      exact NI211N0
  β := ![I197N0, I197N1, I199N1]
  Il := ![[I197N0, I197N1, I197N1], [I199N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
