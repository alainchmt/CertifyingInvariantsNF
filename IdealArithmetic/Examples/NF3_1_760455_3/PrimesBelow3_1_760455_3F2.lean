
import IdealArithmetic.Examples.NF3_1_760455_3.RI3_1_760455_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![49, -29, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![49, -29, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![49, 54, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![49, -29, 1], ![-21, 48, -202], ![-1071, 871, -10]]]
  hmulB := by decide  
  f := ![![![-48, 29, -1], ![83, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-49, -54, 83]], ![![0, -1, 1], ![119, 132, -202], ![-7, 17, -10]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [82, 69, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 82], [0, 1]]
 g := ![![[14, 4], [52, 37], [68], [25], [33, 30], [1]], ![[70, 79], [72, 46], [68], [25], [38, 53], [1]]]
 h' := ![![[14, 82], [52, 81], [48, 28], [35, 20], [33, 78], [1, 14], [0, 1]], ![[0, 1], [24, 2], [25, 55], [66, 63], [46, 5], [31, 69], [14, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [78]]
 b := ![[], [59, 39]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [82, 69, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![46, 49, -1925]
  a := ![-2, 0, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1137, 1253, -1925]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![36, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![36, 1, 0]] 
 ![![83, 0, 0], ![36, 1, 0], ![10, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![36, 1, 0], ![2, 35, 7], ![37, -30, 37]]]
  hmulB := by decide  
  f := ![![![-491, -10497, -2100], ![-249, 24900, 0]], ![![-224, -4549, -910], ![-82, 10790, 0]], ![![-70, -1265, -253], ![-5, 3000, 0]]]
  g := ![![![1, 0, 0], ![-36, 83, 0], ![-10, 0, 83]], ![![0, 1, 0], ![-16, 35, 7], ![9, -30, 37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![49, -29, 1]] ![![83, 0, 0], ![36, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![2988, 83, 0]], ![![4067, -2407, 83], ![1743, -996, -166]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![36, 1, 0]]], ![![![49, -29, 1]], ![![21, -12, -2]]]]
 hle2 := by decide  


def PBC83 : ContainsPrimesAboveP 83 ![I83N0, I83N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 83 (by decide) (𝕀 ⊙ MulI83N0)
instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0]] 
 ![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [47, 62, 86, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [53, 18, 56], [39, 70, 33], [0, 1]]
 g := ![![[50, 30, 64], [55, 16], [58, 18], [30, 37, 50], [36, 3, 1], []], ![[9, 67, 43, 74], [34, 17], [49, 81], [28, 83, 36, 3], [70, 20, 80, 13], [32, 21]], ![[20, 12, 58, 33], [58, 84], [75, 84], [57, 37, 15, 60], [71, 17, 44, 12], [55, 21]]]
 h' := ![![[53, 18, 56], [16, 88, 81], [51, 12, 4], [14, 51, 14], [88, 30, 53], [0, 0, 1], [0, 1]], ![[39, 70, 33], [25, 31, 7], [33, 58, 62], [72, 9, 9], [88, 4, 50], [59, 5, 70], [53, 18, 56]], ![[0, 1], [34, 59, 1], [1, 19, 23], [12, 29, 66], [46, 55, 75], [4, 84, 18], [39, 70, 33]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 2], []]
 b := ![[], [60, 63, 54], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [47, 62, 86, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4588039, -4082341, 4131647]
  a := ![5, -5, 18]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![51551, -45869, 46423]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 704969 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def PBC89 : ContainsPrimesAboveP 89 ![I89N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![89, 0, 0]]) timesTableT_eq_Table B_one_repr 89 (by decide) 𝕀

instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![0, 0, -1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![0, 0, -1]] 
 ![![97, 0, 0], ![2, 1, 0], ![0, 0, 1]] where
  M :=![![![0, 0, -1], ![-37, 30, -1], ![-2, -1, 30]]]
  hmulB := by decide  
  f := ![![![-899, -1, -30]], ![![-30, 0, -1]], ![![-1, 0, 0]]]
  g := ![![![0, 0, -1], ![-1, 30, -1], ![0, -1, 30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N0 : Nat.card (O ⧸ I97N0) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N0)

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := prime_ideal_of_norm_prime hp97.out _ NI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![8, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![8, 1, 0]] 
 ![![97, 0, 0], ![8, 1, 0], ![20, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![8, 1, 0], ![2, 7, 7], ![37, -30, 9]]]
  hmulB := by decide  
  f := ![![![12121, 42825, 42840], ![1455, -593640, 0]], ![![992, 3526, 3528], ![195, -48888, 0]], ![![2492, 8829, 8833], ![387, -122400, 0]]]
  g := ![![![1, 0, 0], ![-8, 97, 0], ![-20, 0, 97]], ![![0, 1, 0], ![-2, 7, 7], ![1, -30, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1

def I97N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-10, 1, 0]] i)))

def SI97N2: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-10, 1, 0]] 
 ![![97, 0, 0], ![87, 1, 0], ![40, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-10, 1, 0], ![2, -11, 7], ![37, -30, -9]]]
  hmulB := by decide  
  f := ![![![-2559, 14350, -9135], ![485, 126585, 0]], ![![-2299, 12866, -8190], ![389, 113490, 0]], ![![-1050, 5917, -3767], ![251, 52200, 0]]]
  g := ![![![1, 0, 0], ![-87, 97, 0], ![-40, 0, 97]], ![![-1, 1, 0], ![7, -11, 7], ![31, -30, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N2 : Nat.card (O ⧸ I97N2) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N2)

lemma isPrimeI97N2 : Ideal.IsPrime I97N2 := prime_ideal_of_norm_prime hp97.out _ NI97N2
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![0, 0, -1]] ![![97, 0, 0], ![8, 1, 0]]
  ![![97, 0, 0], ![58, 29, 1]] where
 M := ![![![0, 0, -97], ![-37, 30, -9]]]
 hmul := by decide  
 g := ![![![![0, 0, -1], ![0, 0, 0]], ![![-53, -26, -1], ![88, 0, 0]]]]
 hle2 := by decide  

def MulI97N1 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![58, 29, 1]] ![![97, 0, 0], ![-10, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![-970, 97, 0]], ![![5626, 2813, 97], ![-485, -291, 194]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![-10, 1, 0]]], ![![![58, 29, 1]], ![![-5, -3, 2]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![45, -21, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![45, -21, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![45, 80, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![45, -21, 1], ![-5, 36, -146], ![-775, 631, -6]]]
  hmulB := by decide  
  f := ![![![-44, 21, -1], ![101, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-45, -80, 101]], ![![0, -1, 1], ![65, 116, -146], ![-5, 11, -6]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [29, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [99, 100], [0, 1]]
 g := ![![[14, 25], [37], [62, 49], [81], [19], [99, 1]], ![[65, 76], [37], [65, 52], [81], [19], [97, 100]]]
 h' := ![![[99, 100], [34, 96], [20, 80], [98, 7], [86, 92], [58, 76], [0, 1]], ![[0, 1], [44, 5], [62, 21], [84, 94], [3, 9], [7, 25], [99, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [83]]
 b := ![[], [92, 92]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [29, 2, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![54011, 63217, -1162928]
  a := ![-66, 2, -199]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![518671, 921757, -1162928]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![45, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![45, 1, 0]] 
 ![![101, 0, 0], ![45, 1, 0], ![6, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![45, 1, 0], ![2, 44, 7], ![37, -30, 46]]]
  hmulB := by decide  
  f := ![![![451, 13856, 2205], ![404, -31815, 0]], ![![190, 6158, 980], ![203, -14140, 0]], ![![21, 823, 131], ![37, -1890, 0]]]
  g := ![![![1, 0, 0], ![-45, 101, 0], ![-6, 0, 101]], ![![0, 1, 0], ![-20, 44, 7], ![11, -30, 46]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![45, -21, 1]] ![![101, 0, 0], ![45, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![4545, 101, 0]], ![![4545, -2121, 101], ![2020, -909, -101]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![45, 1, 0]]], ![![![45, -21, 1]], ![![20, -9, -1]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0]] 
 ![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [36, 32, 68, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [98, 63, 15], [40, 39, 88], [0, 1]]
 g := ![![[3, 15, 36], [77, 86, 61], [62, 70, 60], [3, 100], [53, 92], [1]], ![[96, 52, 56, 82], [62, 26, 78, 25], [90, 75, 77, 25], [88, 82], [101, 13], [47, 54, 73, 79]], ![[10, 3, 0, 71], [4, 85, 96, 96], [74, 60, 95, 96], [99, 23], [44, 49], [48, 102, 76, 24]]]
 h' := ![![[98, 63, 15], [9, 25, 6], [34, 62, 79], [31, 9, 36], [6, 77, 93], [67, 71, 35], [0, 1]], ![[40, 39, 88], [28, 3, 94], [75, 100, 97], [26, 96, 97], [102, 55, 44], [37, 41, 61], [98, 63, 15]], ![[0, 1], [3, 75, 3], [49, 44, 30], [20, 101, 73], [59, 74, 69], [60, 94, 7], [40, 39, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [81, 63], []]
 b := ![[], [68, 23, 37], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [36, 32, 68, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4382341, 4050784, -5681686]
  a := ![-5, 4, -18]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-42547, 39328, -55162]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0]] 
 ![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [93, 20, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [48, 46, 106], [45, 60, 1], [0, 1]]
 g := ![![[34, 8, 16], [75, 17, 89], [2, 92], [6, 106, 13], [63, 89], [1]], ![[35, 103, 1, 98], [85, 89, 92, 55], [94, 81], [20, 21, 79, 96], [74, 12], [94, 34, 45, 106]], ![[61, 43, 67, 1], [90, 52, 104, 35], [11, 79], [16, 86, 80, 12], [77, 56], [15, 31, 59, 1]]]
 h' := ![![[48, 46, 106], [87, 78, 103], [22, 81, 93], [84, 37, 29], [8, 68, 21], [14, 87, 93], [0, 1]], ![[45, 60, 1], [16, 72, 3], [27, 87, 42], [67, 15, 98], [55, 80, 15], [93, 42, 36], [48, 46, 106]], ![[0, 1], [47, 64, 1], [16, 46, 79], [41, 55, 87], [38, 66, 71], [64, 85, 85], [45, 60, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 50], []]
 b := ![[], [64, 74, 50], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [93, 20, 14, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8774, 20972, -321321]
  a := ![-2, 0, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![82, 196, -3003]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![5, 1, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![5, 1, 0]] 
 ![![109, 0, 0], ![5, 1, 0], ![13, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![5, 1, 0], ![2, 4, 7], ![37, -30, 6]]]
  hmulB := by decide  
  f := ![![![-1319, -2640, -4620], ![0, 71940, 0]], ![![-60, -120, -210], ![1, 3270, 0]], ![![-158, -315, -551], ![15, 8580, 0]]]
  g := ![![![1, 0, 0], ![-5, 109, 0], ![-13, 0, 109]], ![![0, 1, 0], ![-1, 4, 7], ![1, -30, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N0 : Nat.card (O ⧸ I109N0) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N0)

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := prime_ideal_of_norm_prime hp109.out _ NI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![12, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![12, 1, 0]] 
 ![![109, 0, 0], ![12, 1, 0], ![106, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![12, 1, 0], ![2, 11, 7], ![37, -30, 13]]]
  hmulB := by decide  
  f := ![![![18465, 103372, 65800], ![3052, -1024600, 0]], ![![2020, 11370, 7238], ![437, -112706, 0]], ![![17958, 100527, 63989], ![2957, -996400, 0]]]
  g := ![![![1, 0, 0], ![-12, 109, 0], ![-106, 0, 109]], ![![0, 1, 0], ![-8, 11, 7], ![-9, -30, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1

def I109N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2496335, 2757, 83006]] i)))

def SI109N2: IdealEqSpanCertificate' Table ![![2496335, 2757, 83006]] 
 ![![109, 0, 0], ![92, 1, 0], ![50, 0, 1]] where
  M :=![![![2496335, 2757, 83006], ![3076736, 3398, 102305], ![268021, 296, 8912]]]
  hmulB := by decide  
  f := ![![![696, -608, 497]], ![![745, -638, 385]], ![![122, -107, 92]]]
  g := ![![![-17501, 2757, 83006], ![-21570, 3398, 102305], ![-1879, 296, 8912]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N2 : Nat.card (O ⧸ I109N2) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N2)

lemma isPrimeI109N2 : Ideal.IsPrime I109N2 := prime_ideal_of_norm_prime hp109.out _ NI109N2
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![5, 1, 0]] ![![109, 0, 0], ![12, 1, 0]]
  ![![-696, 608, -497]] where
 M := ![![![11881, 0, 0], ![1308, 109, 0]], ![![545, 109, 0], ![62, 16, 7]]]
 hmul := by decide  
 g := ![![![![-272100515, -300513, -9047654]], ![![-33032756, -36482, -1098377]]], ![![![-15558411, -17183, -517335]], ![![-1888777, -2086, -62804]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![-696, 608, -497]] ![![2496335, 2757, 83006]]
  ![![109, 0, 0]] where
 M := ![![![-109, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N1, I109N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N1
    exact isPrimeI109N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0 ⊙ MulI109N1)
instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![2, 50, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![2, 50, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![2, 50, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![2, 50, 1], ![137, -78, 351], ![1852, -1499, 22]]]
  hmulB := by decide  
  f := ![![![-1, -50, -1], ![113, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-2, -50, 113]], ![![0, 0, 1], ![-5, -156, 351], ![16, -23, 22]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [110, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [100, 112], [0, 1]]
 g := ![![[71, 95], [31], [22], [82], [91, 91], [100, 1]], ![[79, 18], [31], [22], [82], [38, 22], [87, 112]]]
 h' := ![![[100, 112], [80, 35], [10, 101], [82, 94], [47, 46], [74, 59], [0, 1]], ![[0, 1], [77, 78], [53, 12], [103, 19], [14, 67], [98, 54], [100, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [93]]
 b := ![[], [48, 103]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [110, 13, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![14326, -10682, -182]
  a := ![3, 18, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![130, -14, -182]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-12, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-12, 1, 0]] 
 ![![113, 0, 0], ![101, 1, 0], ![91, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-12, 1, 0], ![2, -13, 7], ![37, -30, -11]]]
  hmulB := by decide  
  f := ![![![-8679, 57421, -30926], ![1469, 499234, 0]], ![![-7751, 51312, -27636], ![1357, 446124, 0]], ![![-6981, 46241, -24905], ![1261, 402038, 0]]]
  g := ![![![1, 0, 0], ![-101, 113, 0], ![-91, 0, 113]], ![![-1, 1, 0], ![6, -13, 7], ![36, -30, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![2, 50, 1]] ![![113, 0, 0], ![-12, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![-1356, 113, 0]], ![![226, 5650, 113], ![113, -678, 339]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![-12, 1, 0]]], ![![![2, 50, 1]], ![![1, -6, 3]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0)
instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![19, 1, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![19, 1, 0]] 
 ![![127, 0, 0], ![19, 1, 0], ![24, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![19, 1, 0], ![2, 18, 7], ![37, -30, 20]]]
  hmulB := by decide  
  f := ![![![9522, 88579, 34454], ![2159, -625094, 0]], ![![1415, 13245, 5152], ![382, -93472, 0]], ![![1793, 16739, 6511], ![451, -118128, 0]]]
  g := ![![![1, 0, 0], ![-19, 127, 0], ![-24, 0, 127]], ![![0, 1, 0], ![-4, 18, 7], ![1, -30, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N0 : Nat.card (O ⧸ I127N0) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N0)

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := prime_ideal_of_norm_prime hp127.out _ NI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-59, 0, -2]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![-59, 0, -2]] 
 ![![127, 0, 0], ![112, 1, 0], ![93, 0, 1]] where
  M :=![![![-59, 0, -2], ![-74, 1, -2], ![-4, -2, 1]]]
  hmulB := by decide  
  f := ![![![3, -4, -2]], ![![2, -3, -2]], ![![1, -2, -1]]]
  g := ![![![1, 0, -2], ![0, 1, -2], ![1, -2, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1

def I127N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-4, 1, 0]] i)))

def SI127N2: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-4, 1, 0]] 
 ![![127, 0, 0], ![123, 1, 0], ![70, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-4, 1, 0], ![2, -5, 7], ![37, -30, -3]]]
  hmulB := by decide  
  f := ![![![5313, -13298, 18620], ![-254, -337820, 0]], ![![5145, -12878, 18032], ![-253, -327152, 0]], ![![2930, -7330, 10263], ![-90, -186200, 0]]]
  g := ![![![1, 0, 0], ![-123, 127, 0], ![-70, 0, 127]], ![![-1, 1, 0], ![1, -5, 7], ![31, -30, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N2 : Nat.card (O ⧸ I127N2) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N2)

lemma isPrimeI127N2 : Ideal.IsPrime I127N2 := prime_ideal_of_norm_prime hp127.out _ NI127N2
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![19, 1, 0]] ![![-59, 0, -2]]
  ![![127, 0, 0], ![14, -54, 1]] where
 M := ![![![-7493, 0, -254]], ![![-1195, 1, -40]]]
 hmul := by decide  
 g := ![![![![-59, 0, -2], ![0, 0, 0]]], ![![![-19, 37, -1], ![87, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![14, -54, 1]] ![![127, 0, 0], ![-4, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![-508, 127, 0]], ![![1778, -6858, 127], ![-127, 254, -381]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![-4, 1, 0]]], ![![![14, -54, 1]], ![![-1, 2, -3]]]]
 hle2 := by decide  


def PBC127 : ContainsPrimesAboveP 127 ![I127N0, I127N1, I127N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
    exact isPrimeI127N1
    exact isPrimeI127N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 127 (by decide) (𝕀 ⊙ MulI127N0 ⊙ MulI127N1)

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1039, 818, 287]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![-1039, 818, 287]] 
 ![![131, 0, 0], ![36, 1, 0], ![101, 0, 1]] where
  M :=![![![-1039, 818, 287], ![12255, -10467, 6013], ![30840, -24253, -8831]]]
  hmulB := by decide  
  f := ![![![238267366, 263147, 7922663]], ![![67719771, 74791, 2251760]], ![![183897601, 203100, 6114806]]]
  g := ![![![-454, 818, 287], ![-1666, -10467, 6013], ![13709, -24253, -8831]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N0 : Nat.card (O ⧸ I131N0) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N0)

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := prime_ideal_of_norm_prime hp131.out _ NI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-15398, -17, -512]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![-15398, -17, -512]] 
 ![![131, 0, 0], ![113, 1, 0], ![45, 0, 1]] where
  M :=![![![-15398, -17, -512], ![-18978, -21, -631], ![-1653, -2, -55]]]
  hmulB := by decide  
  f := ![![![107, -89, 25]], ![![98, -81, 17]], ![![12, -10, 3]]]
  g := ![![![73, -17, -512], ![90, -21, -631], ![8, -2, -55]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![-1039, 818, 287]] ![![-15398, -17, -512]]
  ![![107, -89, 25]] where
 M := ![![![107, -89, 25]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI131N1 : IdealMulLeCertificate' Table 
  ![![107, -89, 25]] ![![-15398, -17, -512]]
  ![![131, 0, 0]] where
 M := ![![![131, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC131 : ContainsPrimesAboveP 131 ![I131N0, I131N1, I131N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
    exact isPrimeI131N1
    exact isPrimeI131N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 131 (by decide) (𝕀 ⊙ MulI131N0 ⊙ MulI131N1)
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


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [48, 100, 94, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [46, 120, 45], [134, 16, 92], [0, 1]]
 g := ![![[39, 136, 39], [20, 39], [68, 105], [68, 107, 107], [80, 65], [43, 1], []], ![[41, 84, 117, 29], [83, 112], [3, 74], [9, 88, 119, 53], [54, 7], [0, 119], [57, 107]], ![[15, 46, 25, 83], [41, 129], [23, 19], [7, 19, 116, 97], [97, 126], [46, 15], [10, 107]]]
 h' := ![![[46, 120, 45], [100, 124, 54], [52, 128, 54], [24, 21, 67], [77, 14, 45], [128, 36, 105], [0, 0, 1], [0, 1]], ![[134, 16, 92], [135, 3, 5], [134, 72, 48], [2, 22, 99], [84, 37, 117], [115, 121, 12], [65, 67, 16], [46, 120, 45]], ![[0, 1], [50, 10, 78], [127, 74, 35], [51, 94, 108], [75, 86, 112], [22, 117, 20], [77, 70, 120], [134, 16, 92]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [78, 110], []]
 b := ![[], [5, 75, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [48, 100, 94, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1510425, 1319584, -1078190]
  a := ![-3, 4, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-11025, 9632, -7870]
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



lemma PB247I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB247I2 : PrimesBelowBoundCertificateInterval O 79 137 247 where
  m := 11
  g := ![2, 1, 3, 2, 1, 1, 3, 2, 3, 3, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB247I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0]
    · exact ![I97N0, I97N1, I97N2]
    · exact ![I101N0, I101N1]
    · exact ![I103N0]
    · exact ![I107N0]
    · exact ![I109N0, I109N1, I109N2]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1, I127N2]
    · exact ![I131N0, I131N1, I131N1]
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
    · exact ![6889, 83]
    · exact ![704969]
    · exact ![97, 97, 97]
    · exact ![10201, 101]
    · exact ![1092727]
    · exact ![1225043]
    · exact ![109, 109, 109]
    · exact ![12769, 113]
    · exact ![127, 127, 127]
    · exact ![131, 131, 131]
    · exact ![2571353]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
      exact NI97N2
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
      exact NI109N2
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
      exact NI127N2
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
  β := ![I83N1, I97N0, I97N1, I97N2, I101N1, I109N0, I109N1, I109N2, I113N1, I127N0, I127N1, I127N2, I131N0, I131N1]
  Il := ![[I83N1], [], [I97N0, I97N1, I97N2], [I101N1], [], [], [I109N0, I109N1, I109N2], [I113N1], [I127N0, I127N1, I127N2], [I131N0, I131N1, I131N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
