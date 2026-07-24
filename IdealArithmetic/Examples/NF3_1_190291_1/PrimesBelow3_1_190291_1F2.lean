
import IdealArithmetic.Examples.NF3_1_190291_1.RI3_1_190291_1
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [14, 14, 55, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [62, 37, 61], [49, 45, 22], [0, 1]]
 g := ![![[43, 4, 10], [55, 31, 77], [79, 49], [6, 38], [23, 28, 1], []], ![[24, 75], [31, 64, 77, 10], [0, 38], [49, 78], [8, 26, 11, 21], [55, 69]], ![[74, 21, 60, 54], [60, 2, 76, 60], [49, 75], [38, 3], [56, 4, 7, 72], [11, 69]]]
 h' := ![![[62, 37, 61], [60, 26, 33], [63, 31, 34], [16, 44, 7], [10, 33, 72], [0, 0, 1], [0, 1]], ![[49, 45, 22], [28, 43], [12, 9, 18], [26, 12, 11], [31, 61, 24], [3, 30, 45], [62, 37, 61]], ![[0, 1], [38, 14, 50], [43, 43, 31], [56, 27, 65], [67, 72, 70], [6, 53, 37], [49, 45, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27, 65], []]
 b := ![[], [14, 30, 52], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [14, 14, 55, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1381784, 228914, -91300]
  a := ![-3, -2, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-16648, 2758, -1100]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![37, 1, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![37, 1, 0]] 
 ![![89, 0, 0], ![37, 1, 0], ![47, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![37, 1, 0], ![2, 38, 8], ![83, -5, 36]]]
  hmulB := by decide  
  f := ![![![6701, 163804, 34496], ![4628, -383768, 0]], ![![2770, 68074, 14336], ![1959, -159488, 0]], ![![3530, 86503, 18217], ![2465, -202664, 0]]]
  g := ![![![1, 0, 0], ![-37, 89, 0], ![-47, 0, 89]], ![![0, 1, 0], ![-20, 38, 8], ![-16, -5, 36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N0 : Nat.card (O ⧸ I89N0) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N0)

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := prime_ideal_of_norm_prime hp89.out _ NI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-32, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-32, 1, 0]] 
 ![![89, 0, 0], ![57, 1, 0], ![32, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-32, 1, 0], ![2, -31, 8], ![83, -5, -33]]]
  hmulB := by decide  
  f := ![![![-453, 8522, -2200], ![267, 24475, 0]], ![![-287, 5454, -1408], ![179, 15664, 0]], ![![-160, 3064, -791], ![104, 8800, 0]]]
  g := ![![![1, 0, 0], ![-57, 89, 0], ![-32, 0, 89]], ![![-1, 1, 0], ![17, -31, 8], ![16, -5, -33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1

def I89N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-5, 1, 0]] i)))

def SI89N2: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-5, 1, 0]] 
 ![![89, 0, 0], ![84, 1, 0], ![20, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-5, 1, 0], ![2, -4, 8], ![83, -5, -6]]]
  hmulB := by decide  
  f := ![![![9049, -18168, 36352], ![-712, -404416, 0]], ![![8542, -17145, 34304], ![-622, -381632, 0]], ![![2035, -4083, 8169], ![-133, -90880, 0]]]
  g := ![![![1, 0, 0], ![-84, 89, 0], ![-20, 0, 89]], ![![-1, 1, 0], ![2, -4, 8], ![7, -5, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N2 : Nat.card (O ⧸ I89N2) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N2)

lemma isPrimeI89N2 : Ideal.IsPrime I89N2 := prime_ideal_of_norm_prime hp89.out _ NI89N2
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![37, 1, 0]] ![![89, 0, 0], ![-32, 1, 0]]
  ![![89, 0, 0], ![8, 23, 1]] where
 M := ![![![7921, 0, 0], ![-2848, 89, 0]], ![![3293, 89, 0], ![-1182, 6, 8]]]
 hmul := by decide  
 g := ![![![![81, -23, -1], ![89, 0, 0]], ![![-32, 1, 0], ![0, 0, 0]]], ![![![29, -22, -1], ![89, 0, 0]], ![![-14, -2, 0], ![8, 0, 0]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![8, 23, 1]] ![![89, 0, 0], ![-5, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-445, 89, 0]], ![![712, 2047, 89], ![89, -89, 178]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-5, 1, 0]]], ![![![8, 23, 1]], ![![1, -1, 2]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![26, -6, 3]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![26, -6, 3]] 
 ![![97, 0, 0], ![0, 97, 0], ![41, 95, 1]] where
  M :=![![![26, -6, 3], ![237, 5, -51], ![-564, 63, 17]]]
  hmulB := by decide  
  f := ![![![-34, -3, -3]], ![![-255, -22, -21]], ![![-266, -23, -22]]]
  g := ![![![-1, -3, 3], ![24, 50, -51], ![-13, -16, 17]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [68, 40, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [57, 96], [0, 1]]
 g := ![![[12, 81], [36], [75], [66], [12], [57, 1]], ![[70, 16], [36], [75], [66], [12], [17, 96]]]
 h' := ![![[57, 96], [78, 88], [95, 6], [65, 47], [73, 39], [4, 77], [0, 1]], ![[0, 1], [50, 9], [49, 91], [28, 50], [65, 58], [28, 20], [57, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [66, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [68, 40, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1630, 891, -9]
  a := ![2, 0, 9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-13, 18, -9]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-34, -3, -3]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![-34, -3, -3]] 
 ![![97, 0, 0], ![17, 1, 0], ![59, 0, 1]] where
  M :=![![![-34, -3, -3], ![-255, -22, -21], ![-183, -18, -16]]]
  hmulB := by decide  
  f := ![![![26, -6, 3]], ![![7, -1, 0]], ![![10, -3, 2]]]
  g := ![![![2, -3, -3], ![14, -22, -21], ![11, -18, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![26, -6, 3]] ![![-34, -3, -3]]
  ![![97, 0, 0]] where
 M := ![![![97, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC97 : ContainsPrimesAboveP 97 ![I97N0, I97N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
    exact isPrimeI97N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 97 (by decide) (𝕀 ⊙ MulI97N0)
instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![13, -5, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![13, -5, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![13, 96, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![13, -5, 1], ![73, 3, -41], ![-437, 36, 13]]]
  hmulB := by decide  
  f := ![![![-12, 5, -1], ![101, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-13, -96, 101]], ![![0, -1, 1], ![6, 39, -41], ![-6, -12, 13]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [6, 61, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [40, 100], [0, 1]]
 g := ![![[27, 17], [49], [83, 70], [71], [80], [40, 1]], ![[0, 84], [49], [55, 31], [71], [80], [80, 100]]]
 h' := ![![[40, 100], [58, 44], [7, 94], [74, 26], [55, 24], [63, 79], [0, 1]], ![[0, 1], [0, 57], [30, 7], [3, 75], [5, 77], [92, 22], [40, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [91]]
 b := ![[], [100, 96]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [6, 61, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![324330, 1974768, -957564]
  a := ![-129, -64, -452]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![126462, 929712, -957564]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![41, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![41, 1, 0]] 
 ![![101, 0, 0], ![41, 1, 0], ![88, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![41, 1, 0], ![2, 42, 8], ![83, -5, 40]]]
  hmulB := by decide  
  f := ![![![-2185, -57946, -11040], ![-1414, 139380, 0]], ![![-915, -23515, -4480], ![-504, 56560, 0]], ![![-1920, -50488, -9619], ![-1192, 121440, 0]]]
  g := ![![![1, 0, 0], ![-41, 101, 0], ![-88, 0, 101]], ![![0, 1, 0], ![-24, 42, 8], ![-32, -5, 40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![13, -5, 1]] ![![101, 0, 0], ![41, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![4141, 101, 0]], ![![1313, -505, 101], ![606, -202, 0]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![41, 1, 0]]], ![![![13, -5, 1]], ![![6, -2, 0]]]]
 hle2 := by decide  


def PBC101 : ContainsPrimesAboveP 101 ![I101N0, I101N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
    exact isPrimeI101N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 101 (by decide) (𝕀 ⊙ MulI101N0)
instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-1, 33, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-1, 33, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![102, 33, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-1, 33, 1], ![149, 27, 263], ![2717, -154, -39]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-102, -33, 103]], ![![-1, 0, 1], ![-259, -84, 263], ![65, 11, -39]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [31, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [86, 102], [0, 1]]
 g := ![![[67, 30], [64, 79], [89, 100], [15], [26], [86, 1]], ![[72, 73], [60, 24], [37, 3], [15], [26], [69, 102]]]
 h' := ![![[86, 102], [76, 37], [22, 39], [29, 93], [59, 85], [12, 52], [0, 1]], ![[0, 1], [65, 66], [80, 64], [96, 10], [56, 18], [55, 51], [86, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [83]]
 b := ![[], [18, 93]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [31, 17, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1569, 1719, -1006]
  a := ![-3, -1, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![981, 339, -1006]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![46, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![46, 1, 0]] 
 ![![103, 0, 0], ![46, 1, 0], ![39, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![46, 1, 0], ![2, 47, 8], ![83, -5, 45]]]
  hmulB := by decide  
  f := ![![![-7061, -221037, -37632], ![-5253, 484512, 0]], ![![-3188, -98678, -16800], ![-2265, 216300, 0]], ![![-2691, -83694, -14249], ![-1950, 183456, 0]]]
  g := ![![![1, 0, 0], ![-46, 103, 0], ![-39, 0, 103]], ![![0, 1, 0], ![-24, 47, 8], ![-14, -5, 45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![-1, 33, 1]] ![![103, 0, 0], ![46, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![4738, 103, 0]], ![![-103, 3399, 103], ![103, 1545, 309]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![46, 1, 0]]], ![![![-1, 33, 1]], ![![1, 15, 3]]]]
 hle2 := by decide  


def PBC103 : ContainsPrimesAboveP 103 ![I103N0, I103N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 103 (by decide) (𝕀 ⊙ MulI103N0)
instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0]] 
 ![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [57, 93, 103, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [95, 90, 90], [16, 16, 17], [0, 1]]
 g := ![![[34, 105, 10], [8, 38, 76], [58, 10], [73, 95, 34], [69, 16], [1]], ![[64, 101, 11, 27], [89, 22, 8, 1], [34, 37], [34, 19, 39, 16], [14, 102], [29, 59, 63, 9]], ![[9, 12, 63, 66], [70, 83, 45, 97], [65, 61], [103, 39, 57, 91], [4, 10], [33, 77, 33, 98]]]
 h' := ![![[95, 90, 90], [79, 36, 44], [48, 62, 41], [12, 46, 63], [65, 63, 26], [50, 14, 4], [0, 1]], ![[16, 16, 17], [27, 82, 92], [18, 45, 30], [43, 22, 12], [88, 20, 94], [43, 78, 40], [95, 90, 90]], ![[0, 1], [71, 96, 78], [97, 0, 36], [48, 39, 32], [47, 24, 94], [75, 15, 63], [16, 16, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [85, 22], []]
 b := ![[], [47, 24, 102], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [57, 93, 103, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1341994, 294036, -124120]
  a := ![-3, -2, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-12542, 2748, -1160]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 1225043 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def PBC107 : ContainsPrimesAboveP 107 ![I107N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![107, 0, 0]]) timesTableT_eq_Table B_one_repr 107 (by decide) 𝕀

instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![22, 10, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![22, 10, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![22, 10, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![22, 10, 1], ![103, 27, 79], ![808, -39, 7]]]
  hmulB := by decide  
  f := ![![![-21, -10, -1], ![109, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-22, -10, 109]], ![![0, 0, 1], ![-15, -7, 79], ![6, -1, 7]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [58, 108, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 108], [0, 1]]
 g := ![![[62, 97], [26], [69, 78], [66, 94], [88], [1, 1]], ![[50, 12], [26], [38, 31], [51, 15], [88], [2, 108]]]
 h' := ![![[1, 108], [107, 36], [31, 74], [96, 80], [4, 51], [51, 52], [0, 1]], ![[0, 1], [34, 73], [105, 35], [67, 29], [55, 58], [103, 57], [1, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59]]
 b := ![[], [67, 84]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [58, 108, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![138997, 75656, -27685]
  a := ![23, 21, 91]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![6863, 3234, -27685]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![30, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![30, 1, 0]] 
 ![![109, 0, 0], ![30, 1, 0], ![102, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![30, 1, 0], ![2, 31, 8], ![83, -5, 29]]]
  hmulB := by decide  
  f := ![![![-6369, -110335, -28480], ![-2725, 388040, 0]], ![![-1778, -30343, -7832], ![-653, 106711, 0]], ![![-5952, -103249, -26651], ![-2579, 363120, 0]]]
  g := ![![![1, 0, 0], ![-30, 109, 0], ![-102, 0, 109]], ![![0, 1, 0], ![-16, 31, 8], ![-25, -5, 29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![22, 10, 1]] ![![109, 0, 0], ![30, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![3270, 109, 0]], ![![2398, 1090, 109], ![763, 327, 109]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![30, 1, 0]]], ![![![22, 10, 1]], ![![7, 3, 1]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0)
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


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [40, 36, 86, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [20, 87, 65], [7, 25, 48], [0, 1]]
 g := ![![[56, 70, 51], [32, 100], [34, 91], [91, 16], [71, 111, 51], [1]], ![[74, 50, 12, 108], [45, 91], [51, 26], [75, 1], [31, 76, 34, 79], [90, 59, 112, 35]], ![[79, 61, 18, 92], [2, 28], [37, 61], [41, 9], [5, 48, 59, 12], [63, 55, 95, 78]]]
 h' := ![![[20, 87, 65], [48, 3, 27], [56, 43, 103], [88, 103, 59], [98, 28, 4], [73, 77, 27], [0, 1]], ![[7, 25, 48], [70, 41, 79], [47, 60, 59], [77, 22, 34], [79, 89, 112], [106, 38, 30], [20, 87, 65]], ![[0, 1], [105, 69, 7], [80, 10, 64], [59, 101, 20], [111, 109, 110], [83, 111, 56], [7, 25, 48]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 33], []]
 b := ![[], [17, 53, 36], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [40, 36, 86, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-94242, 13221, 904]
  a := ![-1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-834, 117, 8]
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



lemma PB124I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 123 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 123 (by omega)

def PB124I2 : PrimesBelowBoundCertificateInterval O 79 123 124 where
  m := 8
  g := ![1, 3, 2, 2, 2, 1, 2, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113]
  hP := PB124I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0, I89N1, I89N2]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1]
    · exact ![I107N0]
    · exact ![I109N0, I109N1]
    · exact ![I113N0]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![571787]
    · exact ![89, 89, 89]
    · exact ![9409, 97]
    · exact ![10201, 101]
    · exact ![10609, 103]
    · exact ![1225043]
    · exact ![11881, 109]
    · exact ![1442897]
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
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
  β := ![I89N0, I89N1, I89N2, I97N1, I101N1, I103N1, I109N1]
  Il := ![[], [I89N0, I89N1, I89N2], [I97N1], [I101N1], [I103N1], [], [I109N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
