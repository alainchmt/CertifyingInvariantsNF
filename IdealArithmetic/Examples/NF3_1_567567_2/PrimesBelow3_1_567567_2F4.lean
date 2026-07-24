
import IdealArithmetic.Examples.NF3_1_567567_2.RI3_1_567567_2
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


def P197P0 : CertificateIrreducibleZModOfList' 197 3 2 7 [132, 82, 79, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [115, 175, 164], [3, 21, 33], [0, 1]]
 g := ![![[123, 158, 175], [96, 62], [99, 70, 134], [93, 171], [156, 114], [6, 134], [1]], ![[76, 20, 133, 6], [83, 173], [67, 57, 146, 76], [194, 143], [191, 55], [97, 101], [134, 111, 87, 114]], ![[162, 10, 80, 121], [53, 168], [60, 165, 105, 63], [15, 107], [78, 81], [118, 92], [85, 163, 192, 83]]]
 h' := ![![[115, 175, 164], [155, 84, 136], [131, 21, 72], [35, 45, 79], [57, 32, 34], [84, 119, 161], [65, 115, 118], [0, 1]], ![[3, 21, 33], [29, 84, 84], [100, 190, 31], [102, 196, 174], [10, 173, 52], [20, 11, 45], [77, 27, 62], [115, 175, 164]], ![[0, 1], [6, 29, 174], [86, 183, 94], [150, 153, 141], [102, 189, 111], [101, 67, 188], [36, 55, 17], [3, 21, 33]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25, 4], []]
 b := ![[], [9, 113, 24], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 3
  hpos := by decide
  P := [132, 82, 79, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-478710, 252554, -228914]
  a := ![-3, -2, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2430, 1282, -1162]
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

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![82, 1, 0]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![199, 0, 0], ![82, 1, 0]] 
 ![![199, 0, 0], ![82, 1, 0], ![90, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![82, 1, 0], ![2, 83, 4], ![101, -27, 81]]]
  hmulB := by decide  
  f := ![![![1719, 91709, 4420], ![1194, -219895, 0]], ![![664, 37762, 1820], ![598, -90545, 0]], ![![742, 41476, 1999], ![626, -99450, 0]]]
  g := ![![![1, 0, 0], ![-82, 199, 0], ![-90, 0, 199]], ![![0, 1, 0], ![-36, 83, 4], ![-25, -27, 81]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N0 : Nat.card (O ⧸ I199N0) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N0)

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := prime_ideal_of_norm_prime hp199.out _ NI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![-56, 1, 0]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![199, 0, 0], ![-56, 1, 0]] 
 ![![199, 0, 0], ![143, 1, 0], ![126, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![-56, 1, 0], ![2, -55, 4], ![101, -27, -57]]]
  hmulB := by decide  
  f := ![![![52679, -1625630, 118236], ![-22885, -5882241, 0]], ![![37833, -1168117, 84960], ![-16516, -4226760, 0]], ![![33390, -1029294, 74863], ![-14364, -3724434, 0]]]
  g := ![![![1, 0, 0], ![-143, 199, 0], ![-126, 0, 199]], ![![-1, 1, 0], ![37, -55, 4], ![56, -27, -57]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1

def I199N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![-26, 1, 0]] i)))

def SI199N2: IdealEqSpanCertificate' Table ![![199, 0, 0], ![-26, 1, 0]] 
 ![![199, 0, 0], ![173, 1, 0], ![37, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![-26, 1, 0], ![2, -25, 4], ![101, -27, -27]]]
  hmulB := by decide  
  f := ![![![6533, -83594, 13376], ![-1194, -665456, 0]], ![![5685, -72670, 11628], ![-994, -578493, 0]], ![![1225, -15543, 2487], ![-143, -123728, 0]]]
  g := ![![![1, 0, 0], ![-173, 199, 0], ![-37, 0, 199]], ![![-1, 1, 0], ![21, -25, 4], ![29, -27, -27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N2 : Nat.card (O ⧸ I199N2) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N2)

lemma isPrimeI199N2 : Ideal.IsPrime I199N2 := prime_ideal_of_norm_prime hp199.out _ NI199N2
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![199, 0, 0], ![82, 1, 0]] ![![199, 0, 0], ![-56, 1, 0]]
  ![![199, 0, 0], ![-53, -43, 1]] where
 M := ![![![39601, 0, 0], ![-11144, 199, 0]], ![![16318, 199, 0], ![-4590, 27, 4]]]
 hmul := by decide  
 g := ![![![![199, 0, 0], ![0, 0, 0]], ![![-3, 44, -1], ![199, 0, 0]]], ![![![82, 1, 0], ![0, 0, 0]], ![![31, 44, -1], ![203, 0, 0]]]]
 hle2 := by decide  

def MulI199N1 : IdealMulLeCertificate' Table 
  ![![199, 0, 0], ![-53, -43, 1]] ![![199, 0, 0], ![-26, 1, 0]]
  ![![199, 0, 0]] where
 M := ![![![39601, 0, 0], ![-5174, 199, 0]], ![![-10547, -8557, 199], ![1393, 995, -199]]]
 hmul := by decide  
 g := ![![![![199, 0, 0]], ![![-26, 1, 0]]], ![![![-53, -43, 1]], ![![7, 5, -1]]]]
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
instance hp211 : Fact (Nat.Prime 211) := {out := by norm_num}

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![-33, -32, 1]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![211, 0, 0], ![-33, -32, 1]] 
 ![![211, 0, 0], ![0, 211, 0], ![178, 179, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![-33, -32, 1], ![37, -92, -129], ![-3296, 896, -28]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-178, -179, 211]], ![![-1, -1, 1], ![109, 109, -129], ![8, 28, -28]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 2 2 7 [59, 126, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [85, 210], [0, 1]]
 g := ![![[113, 93], [208, 5], [14], [93], [104, 196], [64], [85, 1]], ![[0, 118], [0, 206], [14], [93], [95, 15], [64], [170, 210]]]
 h' := ![![[85, 210], [177, 127], [39, 146], [77, 196], [194, 84], [102, 14], [49, 203], [0, 1]], ![[0, 1], [0, 84], [0, 65], [68, 15], [160, 127], [26, 197], [2, 8], [85, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [81]]
 b := ![[], [125, 146]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 2
  hpos := by decide
  P := [59, 126, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1285, 800, -25]
  a := ![2, 0, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![15, 25, -25]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![-82, 1, 0]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![211, 0, 0], ![-82, 1, 0]] 
 ![![211, 0, 0], ![129, 1, 0], ![28, 0, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![-82, 1, 0], ![2, -81, 4], ![101, -27, -83]]]
  hmulB := by decide  
  f := ![![![-2897, 147249, -7272], ![1899, 383598, 0]], ![![-1729, 89985, -4444], ![1267, 234421, 0]], ![![-372, 19540, -965], ![284, 50904, 0]]]
  g := ![![![1, 0, 0], ![-129, 211, 0], ![-28, 0, 211]], ![![-1, 1, 0], ![49, -81, 4], ![28, -27, -83]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![211, 0, 0], ![-33, -32, 1]] ![![211, 0, 0], ![-82, 1, 0]]
  ![![211, 0, 0]] where
 M := ![![![44521, 0, 0], ![-17302, 211, 0]], ![![-6963, -6752, 211], ![2743, 2532, -211]]]
 hmul := by decide  
 g := ![![![![211, 0, 0]], ![![-82, 1, 0]]], ![![![-33, -32, 1]], ![![13, 12, -1]]]]
 hle2 := by decide  


def PBC211 : ContainsPrimesAboveP 211 ![I211N0, I211N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI211N0
    exact isPrimeI211N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 211 (by decide) (𝕀 ⊙ MulI211N0)


lemma PB214I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 213 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 213 (by omega)

def PB214I4 : PrimesBelowBoundCertificateInterval O 193 213 214 where
  m := 3
  g := ![1, 3, 2]
  P := ![197, 199, 211]
  hP := PB214I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0]
    · exact ![I199N0, I199N1, I199N2]
    · exact ![I211N0, I211N1]
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
    · exact ![7645373]
    · exact ![199, 199, 199]
    · exact ![44521, 211]
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
    · dsimp ; intro j
      fin_cases j
      exact NI211N0
      exact NI211N1
  β := ![I199N0, I199N1, I199N2, I211N1]
  Il := ![[], [I199N0, I199N1, I199N2], [I211N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
