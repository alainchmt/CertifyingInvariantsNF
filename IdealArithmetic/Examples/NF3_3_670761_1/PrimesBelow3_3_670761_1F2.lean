
import IdealArithmetic.Examples.NF3_3_670761_1.RI3_3_670761_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0]] 
 ![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [46, 30, 48, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 14, 38], [31, 68, 45], [0, 1]]
 g := ![![[36, 65, 10], [7, 0, 17], [2, 59], [42, 78], [33, 35, 1], []], ![[43, 41, 12, 11], [24, 72, 53, 40], [63, 36], [5, 4], [22, 59, 53, 1], [61, 33]], ![[62, 13, 42, 79], [66, 69, 74, 66], [49, 26], [69, 12], [11, 19, 56, 22], [54, 33]]]
 h' := ![![[4, 14, 38], [10, 76, 50], [28, 9, 73], [55, 17, 15], [59, 56, 59], [0, 0, 1], [0, 1]], ![[31, 68, 45], [5, 35, 63], [76, 33, 77], [22, 4, 6], [13, 13, 81], [32, 1, 68], [4, 14, 38]], ![[0, 1], [3, 55, 53], [16, 41, 16], [64, 62, 62], [1, 14, 26], [54, 82, 14], [31, 68, 45]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64, 36], []]
 b := ![[], [32, 81, 34], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [46, 30, 48, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![238376, 69222, -687489]
  a := ![5, 4, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2872, 834, -8283]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 571787 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def PBC83 : ContainsPrimesAboveP 83 ![I83N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![83, 0, 0]]) timesTableT_eq_Table B_one_repr 83 (by decide) 𝕀

instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![38, 1, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![38, 1, 0]] 
 ![![89, 0, 0], ![38, 1, 0], ![15, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![38, 1, 0], ![-5, 33, 11], ![6, 23, 43]]]
  hmulB := by decide  
  f := ![![![16095, -121832, -40590], ![5518, 328410, 0]], ![![6849, -52002, -17325], ![2404, 140175, 0]], ![![2693, -20534, -6841], ![976, 55350, 0]]]
  g := ![![![1, 0, 0], ![-38, 89, 0], ![-15, 0, 89]], ![![0, 1, 0], ![-16, 33, 11], ![-17, 23, 43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N0 : Nat.card (O ⧸ I89N0) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N0)

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := prime_ideal_of_norm_prime hp89.out _ NI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-32, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-32, 1, 0]] 
 ![![89, 0, 0], ![57, 1, 0], ![78, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-32, 1, 0], ![-5, -37, 11], ![6, 23, -27]]]
  hmulB := by decide  
  f := ![![![-10007, -81431, 24200], ![2759, -195800, 0]], ![![-6399, -52116, 15488], ![1781, -125312, 0]], ![![-8786, -71366, 21209], ![2374, -171600, 0]]]
  g := ![![![1, 0, 0], ![-57, 89, 0], ![-78, 0, 89]], ![![-1, 1, 0], ![14, -37, 11], ![9, 23, -27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1

def I89N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-6, 1, 0]] i)))

def SI89N2: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-6, 1, 0]] 
 ![![89, 0, 0], ![83, 1, 0], ![34, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-6, 1, 0], ![-5, -11, 11], ![6, 23, -1]]]
  hmulB := by decide  
  f := ![![![21771, 48036, -48026], ![-890, 388574, 0]], ![![20302, 44790, -44781], ![-800, 362319, 0]], ![![8322, 18350, -18347], ![-266, 148444, 0]]]
  g := ![![![1, 0, 0], ![-83, 89, 0], ![-34, 0, 89]], ![![-1, 1, 0], ![6, -11, 11], ![-21, 23, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N2 : Nat.card (O ⧸ I89N2) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N2)

lemma isPrimeI89N2 : Ideal.IsPrime I89N2 := prime_ideal_of_norm_prime hp89.out _ NI89N2
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![38, 1, 0]] ![![89, 0, 0], ![-32, 1, 0]]
  ![![89, 0, 0], ![-22, -8, 1]] where
 M := ![![![7921, 0, 0], ![-2848, 89, 0]], ![![3382, 89, 0], ![-1221, 1, 11]]]
 hmul := by decide  
 g := ![![![![89, 0, 0], ![0, 0, 0]], ![![-10, 9, -1], ![89, 0, 0]]], ![![![38, 1, 0], ![0, 0, 0]], ![![-11, 1, 0], ![11, 0, 0]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-22, -8, 1]] ![![89, 0, 0], ![-6, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-534, 89, 0]], ![![-1958, -712, 89], ![178, 89, -89]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-6, 1, 0]]], ![![![-22, -8, 1]], ![![2, 1, -1]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N1, I89N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
    exact isPrimeI89N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0 ⊙ MulI89N1)
instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![13, 1, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![13, 1, 0]] 
 ![![97, 0, 0], ![13, 1, 0], ![43, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![13, 1, 0], ![-5, 8, 11], ![6, 23, 18]]]
  hmulB := by decide  
  f := ![![![-6645, 10808, 14850], ![-776, -130950, 0]], ![![-887, 1441, 1980], ![-96, -17460, 0]], ![![-2948, 4791, 6583], ![-327, -58050, 0]]]
  g := ![![![1, 0, 0], ![-13, 97, 0], ![-43, 0, 97]], ![![0, 1, 0], ![-6, 8, 11], ![-11, 23, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N0 : Nat.card (O ⧸ I97N0) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N0)

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := prime_ideal_of_norm_prime hp97.out _ NI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![37, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![37, 1, 0]] 
 ![![97, 0, 0], ![37, 1, 0], ![33, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![37, 1, 0], ![-5, 32, 11], ![6, 23, 42]]]
  hmulB := by decide  
  f := ![![![7513, -53784, -18480], ![2328, 162960, 0]], ![![2830, -20490, -7040], ![971, 62080, 0]], ![![2543, -18298, -6287], ![826, 55440, 0]]]
  g := ![![![1, 0, 0], ![-37, 97, 0], ![-33, 0, 97]], ![![0, 1, 0], ![-16, 32, 11], ![-23, 23, 42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1

def I97N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![47, 1, 0]] i)))

def SI97N2: IdealEqSpanCertificate' Table ![![97, 0, 0], ![47, 1, 0]] 
 ![![97, 0, 0], ![47, 1, 0], ![67, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![47, 1, 0], ![-5, 42, 11], ![6, 23, 52]]]
  hmulB := by decide  
  f := ![![![15101, -150588, -39424], ![5820, 347648, 0]], ![![7317, -72941, -19096], ![2814, 168392, 0]], ![![10402, -104015, -27231], ![4079, 240128, 0]]]
  g := ![![![1, 0, 0], ![-47, 97, 0], ![-67, 0, 97]], ![![0, 1, 0], ![-28, 42, 11], ![-47, 23, 52]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N2 : Nat.card (O ⧸ I97N2) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N2)

lemma isPrimeI97N2 : Ideal.IsPrime I97N2 := prime_ideal_of_norm_prime hp97.out _ NI97N2
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![13, 1, 0]] ![![97, 0, 0], ![37, 1, 0]]
  ![![97, 0, 0], ![8, -40, 1]] where
 M := ![![![9409, 0, 0], ![3589, 97, 0]], ![![1261, 97, 0], ![476, 45, 11]]]
 hmul := by decide  
 g := ![![![![89, 40, -1], ![97, 0, 0]], ![![29, 41, -1], ![97, 0, 0]]], ![![![5, 41, -1], ![97, 0, 0]], ![![4, 5, 0], ![11, 0, 0]]]]
 hle2 := by decide  

def MulI97N1 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![8, -40, 1]] ![![97, 0, 0], ![47, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![4559, 97, 0]], ![![776, -3880, 97], ![582, -1649, -388]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![47, 1, 0]]], ![![![8, -40, 1]], ![![6, -17, -4]]]]
 hle2 := by decide  


def PBC97 : ContainsPrimesAboveP 97 ![I97N0, I97N1, I97N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
    exact isPrimeI97N1
    exact isPrimeI97N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 97 (by decide) (𝕀 ⊙ MulI97N0 ⊙ MulI97N1)
instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-39, 1, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-39, 1, 0]] 
 ![![101, 0, 0], ![62, 1, 0], ![18, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-39, 1, 0], ![-5, -44, 11], ![6, 23, -34]]]
  hmulB := by decide  
  f := ![![![6960, 67779, -16940], ![-1919, 155540, 0]], ![![4258, 41592, -10395], ![-1211, 95445, 0]], ![![1257, 12079, -3019], ![-299, 27720, 0]]]
  g := ![![![1, 0, 0], ![-62, 101, 0], ![-18, 0, 101]], ![![-1, 1, 0], ![25, -44, 11], ![-8, 23, -34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N0 : Nat.card (O ⧸ I101N0) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N0)

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := prime_ideal_of_norm_prime hp101.out _ NI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-35, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-35, 1, 0]] 
 ![![101, 0, 0], ![66, 1, 0], ![10, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-35, 1, 0], ![-5, -40, 11], ![6, 23, -30]]]
  hmulB := by decide  
  f := ![![![14116, 123036, -33825], ![-3636, 310575, 0]], ![![9241, 80383, -22099], ![-2322, 202909, 0]], ![![1425, 12181, -3349], ![-281, 30750, 0]]]
  g := ![![![1, 0, 0], ![-66, 101, 0], ![-10, 0, 101]], ![![-1, 1, 0], ![25, -40, 11], ![-12, 23, -30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-27, 1, 0]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-27, 1, 0]] 
 ![![101, 0, 0], ![74, 1, 0], ![22, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-27, 1, 0], ![-5, -32, 11], ![6, 23, -22]]]
  hmulB := by decide  
  f := ![![![6960, 46797, -16082], ![-1313, 147662, 0]], ![![5086, 34282, -11781], ![-1009, 108171, 0]], ![![1527, 10193, -3503], ![-245, 32164, 0]]]
  g := ![![![1, 0, 0], ![-74, 101, 0], ![-22, 0, 101]], ![![-1, 1, 0], ![21, -32, 11], ![-12, 23, -22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-39, 1, 0]] ![![101, 0, 0], ![-35, 1, 0]]
  ![![101, 0, 0], ![-60, 2, 1]] where
 M := ![![![10201, 0, 0], ![-3535, 101, 0]], ![![-3939, 101, 0], ![1360, -79, 11]]]
 hmul := by decide  
 g := ![![![![101, 0, 0], ![0, 0, 0]], ![![25, -1, -1], ![101, 0, 0]]], ![![![21, -1, -1], ![101, 0, 0]], ![![20, -1, 0], ![11, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-60, 2, 1]] ![![101, 0, 0], ![-27, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-2727, 101, 0]], ![![-6060, 202, 101], ![1616, -101, 0]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-27, 1, 0]]], ![![![-60, 2, 1]], ![![16, -1, 0]]]]
 hle2 := by decide  


def PBC101 : ContainsPrimesAboveP 101 ![I101N0, I101N1, I101N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
    exact isPrimeI101N1
    exact isPrimeI101N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 101 (by decide) (𝕀 ⊙ MulI101N0 ⊙ MulI101N1)
instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0]] 
 ![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [44, 92, 45, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 83, 54], [36, 19, 49], [0, 1]]
 g := ![![[51, 19, 8], [54, 67, 66], [88, 3, 17], [98, 34], [70, 68], [1]], ![[15, 38, 28, 24], [85, 13, 31, 42], [64, 6, 33, 31], [79, 76], [28, 38], [44, 85, 42, 80]], ![[99, 8, 13, 46], [80, 27, 36, 60], [96, 78, 22, 52], [53, 13], [40, 9], [27, 53, 68, 23]]]
 h' := ![![[22, 83, 54], [96, 28, 27], [42, 6, 90], [32, 31, 29], [92, 3, 31], [59, 11, 58], [0, 1]], ![[36, 19, 49], [12, 22, 68], [38, 69, 77], [27, 28, 62], [102, 36, 30], [60, 46, 48], [22, 83, 54]], ![[0, 1], [11, 53, 8], [48, 28, 39], [16, 44, 12], [59, 64, 42], [45, 46, 100], [36, 19, 49]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65, 28], []]
 b := ![[], [62, 31, 30], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [44, 92, 45, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4882097, -5989862, 9214380]
  a := ![-11, -13, 24]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-47399, -58154, 89460]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 1092727 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def PBC103 : ContainsPrimesAboveP 103 ![I103N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![103, 0, 0]]) timesTableT_eq_Table B_one_repr 103 (by decide) 𝕀

instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![53, 1, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![53, 1, 0]] 
 ![![107, 0, 0], ![53, 1, 0], ![99, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![53, 1, 0], ![-5, 48, 11], ![6, 23, 58]]]
  hmulB := by decide  
  f := ![![![33435, -383162, -87780], ![13054, 853860, 0]], ![![16527, -189757, -43472], ![6528, 422864, 0]], ![![30955, -354514, -81217], ![12038, 790020, 0]]]
  g := ![![![1, 0, 0], ![-53, 107, 0], ![-99, 0, 107]], ![![0, 1, 0], ![-34, 48, 11], ![-65, 23, 58]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N0 : Nat.card (O ⧸ I107N0) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N0)

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := prime_ideal_of_norm_prime hp107.out _ NI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-44, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-44, 1, 0]] 
 ![![107, 0, 0], ![63, 1, 0], ![37, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-44, 1, 0], ![-5, -49, 11], ![6, 23, -39]]]
  hmulB := by decide  
  f := ![![![-210, -2500, 561], ![107, -5457, 0]], ![![-105, -1471, 330], ![108, -3210, 0]], ![![-50, -865, 194], ![92, -1887, 0]]]
  g := ![![![1, 0, 0], ![-63, 107, 0], ![-37, 0, 107]], ![![-1, 1, 0], ![25, -49, 11], ![0, 23, -39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-9, 1, 0]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-9, 1, 0]] 
 ![![107, 0, 0], ![98, 1, 0], ![27, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-9, 1, 0], ![-5, -14, 11], ![6, 23, -4]]]
  hmulB := by decide  
  f := ![![![44435, 125044, -98230], ![-2568, 955510, 0]], ![![40702, 114513, -89958], ![-2246, 875046, 0]], ![![11214, 31553, -24787], ![-631, 241110, 0]]]
  g := ![![![1, 0, 0], ![-98, 107, 0], ![-27, 0, 107]], ![![-1, 1, 0], ![10, -14, 11], ![-20, 23, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![53, 1, 0]] ![![107, 0, 0], ![-44, 1, 0]]
  ![![107, 0, 0], ![21, 49, 1]] where
 M := ![![![11449, 0, 0], ![-4708, 107, 0]], ![![5671, 107, 0], ![-2337, 4, 11]]]
 hmul := by decide  
 g := ![![![![86, -49, -1], ![107, 0, 0]], ![![-44, 1, 0], ![0, 0, 0]]], ![![![32, -48, -1], ![107, 0, 0]], ![![-24, -5, 0], ![11, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![21, 49, 1]] ![![107, 0, 0], ![-9, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-963, 107, 0]], ![![2247, 5243, 107], ![-428, -642, 535]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-9, 1, 0]]], ![![![21, 49, 1]], ![![-4, -6, 5]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1, I107N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
    exact isPrimeI107N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0 ⊙ MulI107N1)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0]] 
 ![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [77, 50, 51, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [78, 68, 69], [89, 40, 40], [0, 1]]
 g := ![![[91, 21, 74], [62, 12], [34, 73, 31], [101, 103, 108], [88, 94], [1]], ![[32, 96, 35, 70], [21, 61], [21, 96, 40, 99], [97, 72, 11, 76], [44, 74], [2, 10, 49, 92]], ![[2, 32, 77, 62], [98, 15], [77, 91, 70, 72], [75, 68, 104, 30], [3, 106], [61, 80, 56, 17]]]
 h' := ![![[78, 68, 69], [26, 82, 69], [107, 9, 98], [71, 70, 85], [25, 95, 76], [32, 59, 58], [0, 1]], ![[89, 40, 40], [39, 11, 25], [81, 49, 72], [88, 4, 55], [19, 84, 3], [30, 64, 69], [78, 68, 69]], ![[0, 1], [104, 16, 15], [67, 51, 48], [7, 35, 78], [71, 39, 30], [56, 95, 91], [89, 40, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48, 7], []]
 b := ![[], [77, 103, 101], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [77, 50, 51, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![54241903369, 45916203893, -124346921941]
  a := ![261, 262, -587]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![497632141, 421249577, -1140797449]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 1295029 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def PBC109 : ContainsPrimesAboveP 109 ![I109N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![109, 0, 0]]) timesTableT_eq_Table B_one_repr 109 (by decide) 𝕀

instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0]] 
 ![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [21, 71, 61, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [98, 44, 47], [67, 68, 66], [0, 1]]
 g := ![![[33, 27, 26], [82, 111], [1, 91], [4, 81], [105, 110, 105], [1]], ![[85, 23, 89, 70], [83, 11], [37, 106], [41, 72], [107, 84, 53, 24], [77, 101, 43, 89]], ![[51, 61, 33, 94], [74, 4], [103, 57], [64, 69], [38, 25, 71, 5], [105, 6, 110, 24]]]
 h' := ![![[98, 44, 47], [4, 71, 79], [101, 34, 26], [3, 110, 54], [55, 55, 9], [92, 42, 52], [0, 1]], ![[67, 68, 66], [78, 1, 8], [76, 102, 89], [47, 102, 28], [2, 86, 33], [93, 77, 86], [98, 44, 47]], ![[0, 1], [21, 41, 26], [28, 90, 111], [65, 14, 31], [36, 85, 71], [12, 107, 88], [67, 68, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14, 98], []]
 b := ![[], [12, 42, 46], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [21, 71, 61, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3750922, 4068000, -7647840]
  a := ![11, 12, -24]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![33194, 36000, -67680]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 1442897 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def PBC113 : ContainsPrimesAboveP 113 ![I113N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![113, 0, 0]]) timesTableT_eq_Table B_one_repr 113 (by decide) 𝕀

instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0]] 
 ![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [39, 69, 38, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [99, 98, 13], [117, 28, 114], [0, 1]]
 g := ![![[17], [13, 112, 122], [107, 37, 26], [27, 83, 107], [78, 29, 47], [1]], ![[93, 87, 75, 11], [118, 124, 69, 32], [90, 54, 62, 62], [91, 109, 6, 19], [80, 12, 115, 1], [51, 28, 109, 38]], ![[65, 96, 69, 116], [83, 29, 111, 91], [3, 93, 48, 106], [82, 86, 108, 55], [76, 83, 62, 67], [50, 36, 19, 89]]]
 h' := ![![[99, 98, 13], [1, 12], [18, 36, 73], [90, 16, 36], [6, 88, 108], [88, 58, 89], [0, 1]], ![[117, 28, 114], [46, 33, 29], [71, 8, 99], [120, 20, 73], [119, 43, 104], [62, 79, 71], [99, 98, 13]], ![[0, 1], [8, 82, 98], [82, 83, 82], [113, 91, 18], [56, 123, 42], [98, 117, 94], [117, 28, 114]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [123, 52], []]
 b := ![[], [8, 54, 123], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [39, 69, 38, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![250444, 76708, -718058]
  a := ![5, 4, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1972, 604, -5654]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 2048383 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def PBC127 : ContainsPrimesAboveP 127 ![I127N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![127, 0, 0]]) timesTableT_eq_Table B_one_repr 127 (by decide) 𝕀

instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0]] 
 ![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [80, 33, 55, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [126, 57, 47], [81, 73, 84], [0, 1]]
 g := ![![[41, 83, 107], [120, 51, 46], [102, 46], [92, 3], [77, 48], [76, 1], []], ![[105, 70, 114, 127], [69, 35, 48, 126], [102, 74], [58, 39], [115, 55], [70, 89], [60, 113]], ![[12, 40, 124, 109], [67, 120, 6, 81], [85, 64], [58, 114], [91, 11], [114, 105], [23, 113]]]
 h' := ![![[126, 57, 47], [94, 126, 32], [100, 96, 96], [20, 41, 96], [31, 119, 93], [77, 32, 110], [0, 0, 1], [0, 1]], ![[81, 73, 84], [65, 89, 5], [113, 44, 123], [46, 53, 27], [106, 100, 68], [108, 113, 102], [72, 69, 73], [126, 57, 47]], ![[0, 1], [111, 47, 94], [103, 122, 43], [22, 37, 8], [48, 43, 101], [75, 117, 50], [5, 62, 57], [81, 73, 84]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49, 86], []]
 b := ![[], [24, 108, 79], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [80, 33, 55, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![345709, 12164660, 11858120]
  a := ![-9, 10, 20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2639, 92860, 90520]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 2248091 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def PBC131 : ContainsPrimesAboveP 131 ![I131N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![131, 0, 0]]) timesTableT_eq_Table B_one_repr 131 (by decide) 𝕀

instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0]] 
 ![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [110, 50, 34, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [94, 1, 55], [9, 135, 82], [0, 1]]
 g := ![![[39, 70, 34], [74, 25], [135, 77], [24, 96, 11], [41, 100], [103, 1], []], ![[134, 14, 58, 46], [45, 9], [49, 73], [33, 136, 33, 111], [79, 28], [61, 4], [10, 11]], ![[97, 103, 136, 24], [74, 64], [83, 9], [51, 68, 99, 96], [7, 60], [133, 1], [120, 11]]]
 h' := ![![[94, 1, 55], [91, 15, 50], [82, 72, 132], [100, 134, 112], [48, 58, 82], [41, 83, 10], [0, 0, 1], [0, 1]], ![[9, 135, 82], [43, 87, 40], [91, 10, 134], [136, 98, 22], [62, 61, 12], [126, 70, 24], [64, 122, 135], [94, 1, 55]], ![[0, 1], [95, 35, 47], [17, 55, 8], [70, 42, 3], [125, 18, 43], [22, 121, 103], [33, 15, 1], [9, 135, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 29], []]
 b := ![[], [16, 89, 129], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [110, 50, 34, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2773291, 3903404, -4700196]
  a := ![9, 12, -20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![20243, 28492, -34308]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 2571353 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def PBC137 : ContainsPrimesAboveP 137 ![I137N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![137, 0, 0]]) timesTableT_eq_Table B_one_repr 137 (by decide) 𝕀



lemma PB183I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB183I2 : PrimesBelowBoundCertificateInterval O 79 137 183 where
  m := 11
  g := ![1, 3, 3, 3, 1, 3, 1, 1, 1, 1, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB183I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0, I89N1, I89N2]
    · exact ![I97N0, I97N1, I97N2]
    · exact ![I101N0, I101N1, I101N2]
    · exact ![I103N0]
    · exact ![I107N0, I107N1, I107N2]
    · exact ![I109N0]
    · exact ![I113N0]
    · exact ![I127N0]
    · exact ![I131N0]
    · exact ![I137N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC83
    · exact PBC89
    · exact PBC97
    · exact PBC101
    · exact PBC103
    · exact PBC107
    · exact PBC109
    · exact PBC113
    · exact PBC127
    · exact PBC131
    · exact PBC137
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![571787]
    · exact ![89, 89, 89]
    · exact ![97, 97, 97]
    · exact ![101, 101, 101]
    · exact ![1092727]
    · exact ![107, 107, 107]
    · exact ![1295029]
    · exact ![1442897]
    · exact ![2048383]
    · exact ![2248091]
    · exact ![2571353]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
      exact NI89N2
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
      exact NI97N2
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
      exact NI101N2
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
      exact NI107N2
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
  β := ![I89N0, I89N1, I89N2, I97N0, I97N1, I97N2, I101N0, I101N1, I101N2, I107N0, I107N1, I107N2]
  Il := ![[], [I89N0, I89N1, I89N2], [I97N0, I97N1, I97N2], [I101N0, I101N1, I101N2], [], [I107N0, I107N1, I107N2], [], [], [], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
