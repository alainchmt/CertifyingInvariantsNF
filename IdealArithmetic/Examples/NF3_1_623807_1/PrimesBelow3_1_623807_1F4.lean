
import IdealArithmetic.Examples.NF3_1_623807_1.RI3_1_623807_1
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


def P197P0 : CertificateIrreducibleZModOfList' 197 3 2 7 [143, 106, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [189, 101, 143], [5, 95, 54], [0, 1]]
 g := ![![[102, 34, 54], [43, 182], [74, 52, 23], [96, 81], [189, 158], [18, 9], [1]], ![[81, 115, 158, 154], [49, 22], [157, 80, 126, 196], [145, 43], [95, 193], [41, 19], [146, 20, 186, 136]], ![[118, 113, 151, 41], [143, 23], [134, 47, 152, 26], [70, 163], [45, 85], [190, 96], [143, 164, 128, 61]]]
 h' := ![![[189, 101, 143], [139, 87, 60], [56, 156, 173], [55, 123, 107], [105, 183, 9], [145, 132, 54], [54, 91, 194], [0, 1]], ![[5, 95, 54], [63, 97, 17], [136, 123, 131], [111, 45, 174], [113, 139, 35], [41, 192, 169], [83, 71, 120], [189, 101, 143]], ![[0, 1], [185, 13, 120], [46, 115, 90], [170, 29, 113], [85, 72, 153], [120, 70, 171], [164, 35, 80], [5, 95, 54]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26, 104], []]
 b := ![[], [46, 119, 53], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 3
  hpos := by decide
  P := [143, 106, 3, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-311457, -1576, -2364]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1581, -8, -12]
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

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![-93, 1, 0]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![199, 0, 0], ![-93, 1, 0]] 
 ![![199, 0, 0], ![106, 1, 0], ![100, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![-93, 1, 0], ![0, -92, 2], ![152, 0, -94]]]
  hmulB := by decide  
  f := ![![![13486, -145, 0], ![28855, 0, 0]], ![![7162, -77, 0], ![15324, 0, 0]], ![![6904, -28, -1], ![14772, 100, 0]]]
  g := ![![![1, 0, 0], ![-106, 199, 0], ![-100, 0, 199]], ![![-1, 1, 0], ![48, -92, 2], ![48, 0, -94]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N0 : Nat.card (O ⧸ I199N0) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N0)

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := prime_ideal_of_norm_prime hp199.out _ NI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![-76, 1, 0]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![199, 0, 0], ![-76, 1, 0]] 
 ![![199, 0, 0], ![123, 1, 0], ![135, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![-76, 1, 0], ![0, -75, 2], ![152, 0, -77]]]
  hmulB := by decide  
  f := ![![![6765, -89, 0], ![17711, 0, 0]], ![![4257, -56, 0], ![11145, 0, 0]], ![![4613, -23, -1], ![12077, 100, 0]]]
  g := ![![![1, 0, 0], ![-123, 199, 0], ![-135, 0, 199]], ![![-1, 1, 0], ![45, -75, 2], ![53, 0, -77]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1

def I199N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![-30, 1, 0]] i)))

def SI199N2: IdealEqSpanCertificate' Table ![![199, 0, 0], ![-30, 1, 0]] 
 ![![199, 0, 0], ![169, 1, 0], ![162, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![-30, 1, 0], ![0, -29, 2], ![152, 0, -31]]]
  hmulB := by decide  
  f := ![![![3031, -101, 0], ![20099, 0, 0]], ![![2581, -86, 0], ![17115, 0, 0]], ![![2478, -68, -1], ![16432, 100, 0]]]
  g := ![![![1, 0, 0], ![-169, 199, 0], ![-162, 0, 199]], ![![-1, 1, 0], ![23, -29, 2], ![26, 0, -31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N2 : Nat.card (O ⧸ I199N2) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N2)

lemma isPrimeI199N2 : Ideal.IsPrime I199N2 := prime_ideal_of_norm_prime hp199.out _ NI199N2
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![199, 0, 0], ![-93, 1, 0]] ![![199, 0, 0], ![-76, 1, 0]]
  ![![199, 0, 0], ![-48, -84, 1]] where
 M := ![![![39601, 0, 0], ![-15124, 199, 0]], ![![-18507, 199, 0], ![7068, -168, 2]]]
 hmul := by decide  
 g := ![![![![199, 0, 0], ![0, 0, 0]], ![![-28, 85, -1], ![199, 0, 0]]], ![![![-45, 85, -1], ![199, 0, 0]], ![![36, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI199N1 : IdealMulLeCertificate' Table 
  ![![199, 0, 0], ![-48, -84, 1]] ![![199, 0, 0], ![-30, 1, 0]]
  ![![199, 0, 0]] where
 M := ![![![39601, 0, 0], ![-5970, 199, 0]], ![![-9552, -16716, 199], ![1592, 2388, -199]]]
 hmul := by decide  
 g := ![![![![199, 0, 0]], ![![-30, 1, 0]]], ![![![-48, -84, 1]], ![![8, 12, -1]]]]
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

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![211, 0, 0]] 
 ![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 3 2 7 [84, 134, 210, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [77, 139, 146], [135, 71, 65], [0, 1]]
 g := ![![[87, 175, 201], [92, 110, 80], [88, 105], [21, 45], [175, 15, 51], [155, 1], [1]], ![[178, 197, 72, 197], [14, 61, 120, 138], [185, 96], [47, 21], [160, 209, 65, 111], [117, 20], [48, 66, 72, 97]], ![[130, 37, 113, 34], [25, 64, 23, 170], [60, 180], [179, 209], [198, 37, 108, 208], [188, 70], [2, 112, 124, 114]]]
 h' := ![![[77, 139, 146], [79, 54, 74], [201, 4, 162], [182, 52, 152], [70, 159, 195], [155, 181, 85], [127, 77, 1], [0, 1]], ![[135, 71, 65], [44, 206, 56], [129, 149, 59], [107, 29, 27], [149, 93, 134], [63, 179, 178], [117, 157, 130], [77, 139, 146]], ![[0, 1], [33, 162, 81], [67, 58, 201], [26, 130, 32], [202, 170, 93], [99, 62, 159], [158, 188, 80], [135, 71, 65]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [103, 209], []]
 b := ![[], [0, 86, 185], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 3
  hpos := by decide
  P := [84, 134, 210, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![483823, 254677, -6330]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2293, 1207, -30]
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

instance hp223 : Fact (Nat.Prime 223) := {out := by norm_num}

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![-11, 24, 1]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![223, 0, 0], ![-11, 24, 1]] 
 ![![223, 0, 0], ![0, 223, 0], ![212, 24, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![-11, 24, 1], ![152, 13, 47], ![3496, 76, -34]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-212, -24, 223]], ![![-1, 0, 1], ![-44, -5, 47], ![48, 4, -34]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 2 2 7 [172, 163, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [60, 222], [0, 1]]
 g := ![![[93, 188], [66, 210], [222, 25], [210, 76], [180, 210], [199], [60, 1]], ![[0, 35], [178, 13], [161, 198], [87, 147], [69, 13], [199], [120, 222]]]
 h' := ![![[60, 222], [21, 100], [172, 136], [6, 5], [37, 116], [167, 87], [161, 83], [0, 1]], ![[0, 1], [0, 123], [81, 87], [83, 218], [84, 107], [35, 136], [12, 140], [60, 222]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [159, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 2
  hpos := by decide
  P := [172, 163, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6316, 76, -34]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4, 4, -34]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 49729 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![-47, 1, 0]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![223, 0, 0], ![-47, 1, 0]] 
 ![![223, 0, 0], ![176, 1, 0], ![34, 0, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![-47, 1, 0], ![0, -46, 2], ![152, 0, -48]]]
  hmulB := by decide  
  f := ![![![3620, -77, 0], ![17171, 0, 0]], ![![2868, -61, 0], ![13604, 0, 0]], ![![616, 10, -1], ![2922, 112, 0]]]
  g := ![![![1, 0, 0], ![-176, 223, 0], ![-34, 0, 223]], ![![-1, 1, 0], ![36, -46, 2], ![8, 0, -48]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![223, 0, 0], ![-11, 24, 1]] ![![223, 0, 0], ![-47, 1, 0]]
  ![![223, 0, 0]] where
 M := ![![![49729, 0, 0], ![-10481, 223, 0]], ![![-2453, 5352, 223], ![669, -1115, 0]]]
 hmul := by decide  
 g := ![![![![223, 0, 0]], ![![-47, 1, 0]]], ![![![-11, 24, 1]], ![![3, -5, 0]]]]
 hle2 := by decide  


def PBC223 : ContainsPrimesAboveP 223 ![I223N0, I223N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI223N0
    exact isPrimeI223N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 223 (by decide) (𝕀 ⊙ MulI223N0)


lemma PB224I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 223 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 223 (by omega)

def PB224I4 : PrimesBelowBoundCertificateInterval O 193 223 224 where
  m := 4
  g := ![1, 3, 1, 2]
  P := ![197, 199, 211, 223]
  hP := PB224I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0]
    · exact ![I199N0, I199N1, I199N2]
    · exact ![I211N0]
    · exact ![I223N0, I223N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC197
    · exact PBC199
    · exact PBC211
    · exact PBC223
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![7645373]
    · exact ![199, 199, 199]
    · exact ![9393931]
    · exact ![49729, 223]
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
    · dsimp ; intro j
      fin_cases j
      exact NI223N0
      exact NI223N1
  β := ![I199N0, I199N1, I199N2, I223N1]
  Il := ![[], [I199N0, I199N1, I199N2], [], [I223N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
