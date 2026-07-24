
import IdealArithmetic.Examples.NF5_5_10125000000_1.RI5_5_10125000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7291, -9823, -12036, -7081, -2816]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![7291, -9823, -12036, -7081, -2816]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![0, 0, 67, 0, 0], ![0, 0, 0, 67, 0], ![6, 54, 55, 23, 1]] where
  M :=![![![7291, -9823, -12036, -7081, -2816], ![70318, -96232, -118124, -70495, -28324], ![319206, -434601, -533155, -316707, -126828], ![1550554, -2115165, -2595392, -1544420, -619252], ![4415776, -6020758, -7387300, -4393956, -1761239]]]
  hmulB := by decide  
  f := ![![![3105, 3325, 1248, -35, -136]], ![![4010, 3734, 1280, -53, -140]], ![![42, 615, 347, 3, -36]], ![![-1462, -1887, -748, 30, 76]], ![![3006, 3130, 1159, -33, -127]]]
  g := ![![![361, 2123, 2132, 861, -2816], ![3586, 21392, 21488, 8671, -28324], ![16122, 95733, 96155, 38811, -126828], ![78598, 467529, 469604, 189528, -619252], ![223630, 1329644, 1335535, 539023, -1761239]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 4 2 6 [18, 4, 16, 1, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 8, 7, 63], [30, 8, 3, 9], [12, 50, 57, 62], [0, 1]]
 g := ![![[21, 52, 30, 6], [65, 3, 25, 17], [3, 16, 21], [16, 31, 1], [1], []], ![[39, 54, 57, 44, 19, 66], [35, 53, 12, 52, 65, 30], [59, 42, 36], [57, 39, 22], [64, 65, 1], [2, 62, 16]], ![[59, 26, 66, 2, 16, 56], [12, 25, 59, 59, 33, 4], [32, 6, 55], [33, 63, 64], [17, 58, 9], [23, 40, 14]], ![[37, 4, 41, 58, 1, 47], [41, 15, 47, 58, 11, 15], [54, 50, 59], [30, 10, 17], [41, 55, 16], [63, 8, 25]]]
 h' := ![![[24, 8, 7, 63], [36, 44, 56, 41], [36, 57, 25, 33], [36, 58, 60, 50], [49, 63, 51, 66], [0, 0, 1], [0, 1]], ![[30, 8, 3, 9], [59, 57, 42, 34], [20, 50, 16, 19], [55, 18, 40, 6], [3, 24, 43, 42], [4, 64, 33, 1], [24, 8, 7, 63]], ![[12, 50, 57, 62], [64, 58, 45, 61], [56, 66, 16, 23], [30, 43, 63, 51], [50, 62, 13, 59], [17, 3, 0, 3], [30, 8, 3, 9]], ![[0, 1], [42, 42, 58, 65], [20, 28, 10, 59], [56, 15, 38, 27], [23, 52, 27, 34], [15, 0, 33, 63], [12, 50, 57, 62]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [4, 31, 63], []]
 b := ![[], [], [49, 61, 44, 60], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 4
  hpos := by decide
  P := [18, 4, 16, 1, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1713551964987154, 2346104653373560, 2876532115382968, 1716635383683252, 692525958959506]
  a := ![-25, -17, 5, -1, -50]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-87592652518570, -523138763140892, -525558143692386, -212111368244558, 692525958959506]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 20151121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3105, -3325, -1248, 35, 136]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![-3105, -3325, -1248, 35, 136]] 
 ![![67, 0, 0, 0, 0], ![42, 1, 0, 0, 0], ![35, 0, 1, 0, 0], ![48, 0, 0, 1, 0], ![62, 0, 0, 0, 1]] where
  M :=![![![-3105, -3325, -1248, 35, 136], ![-4010, -3734, -1280, 53, 140], ![-42, -615, -347, -3, 36], ![1462, 1887, 748, -30, -76], ![2452, 2300, 836, -6, -99]]]
  hmulB := by decide  
  f := ![![![-7291, 9823, 12036, 7081, 2816]], ![![-5620, 7594, 9308, 5491, 2188]], ![![-8573, 11618, 14245, 8426, 3364]], ![![-28366, 38607, 47360, 28124, 11260]], ![![-72654, 98952, 121396, 72134, 28893]]]
  g := ![![![2539, -3325, -1248, 35, 136], ![2782, -3734, -1280, 53, 140], ![535, -615, -347, -3, 36], ![-1460, 1887, 748, -30, -76], ![-1746, 2300, 836, -6, -99]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![7291, -9823, -12036, -7081, -2816]] ![![-3105, -3325, -1248, 35, 136]]
  ![![67, 0, 0, 0, 0]] where
 M := ![![![-67, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0, 0, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0, 0, 0]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![0, 0, 0, 71, 0], ![0, 0, 0, 0, 71]] where
  M :=![![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![0, 0, 0, 71, 0], ![0, 0, 0, 0, 71]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 5 2 6 [9, 7, 17, 64, 4, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [60, 48, 36, 44, 69], [49, 43, 43, 5, 42], [14, 34, 38, 62, 9], [15, 16, 25, 31, 22], [0, 1]]
 g := ![![[17, 6, 64, 40, 8], [21, 54, 18, 12, 64], [20, 15, 10, 43, 50], [5, 23, 67, 1], [], []], ![[12, 16, 47, 14, 50, 11, 0, 69], [31, 47, 45, 62, 6, 29, 64, 26], [17, 5, 63, 49, 57, 0, 23, 14], [15, 25, 3, 24], [61, 22, 43, 54], [16, 32, 21, 4]], ![[59, 35, 28, 45, 14, 18, 58, 34], [1, 18, 52, 15, 48, 27, 30, 46], [36, 21, 4, 27, 2, 1, 21, 56], [49, 43, 10, 57], [40, 67, 43, 27], [22, 0, 38, 60]], ![[44, 1, 61, 24, 62, 35, 63, 16], [10, 70, 47, 28, 44, 30, 53, 16], [57, 69, 59, 39, 55, 31, 20, 50], [55, 13, 60, 24], [32, 45, 39, 27], [8, 10, 11, 10]], ![[24, 10, 11, 58, 31, 33, 16, 59], [67, 6, 59, 56, 0, 68, 48, 62], [59, 3, 51, 61, 11, 30, 51, 28], [65, 66, 20, 15], [20, 27, 66, 54], [41, 69, 67, 58]]]
 h' := ![![[60, 48, 36, 44, 69], [24, 30, 9, 37, 24], [33, 46, 16, 70, 8], [26, 42, 3, 18, 60], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[49, 43, 43, 5, 42], [35, 30, 62, 58, 70], [65, 49, 15, 40, 22], [52, 36, 59, 70, 8], [51, 37, 16, 37, 33], [48, 35, 46, 27, 14], [60, 48, 36, 44, 69]], ![[14, 34, 38, 62, 9], [16, 20, 35, 6, 31], [50, 41, 56, 30, 36], [57, 9, 0, 51, 5], [70, 21, 70, 36, 25], [2, 13, 22, 57, 58], [49, 43, 43, 5, 42]], ![[15, 16, 25, 31, 22], [69, 51, 35, 3, 25], [46, 2, 45, 27, 46], [20, 28, 4, 17, 51], [36, 33, 55, 54, 33], [53, 25, 69, 63, 13], [14, 34, 38, 62, 9]], ![[0, 1], [46, 11, 1, 38, 63], [30, 4, 10, 46, 30], [3, 27, 5, 57, 18], [37, 51, 1, 15, 50], [69, 69, 4, 66, 57], [15, 16, 25, 31, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 34, 40, 22], [], [], []]
 b := ![[], [46, 30, 63, 22, 11], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 5
  hpos := by decide
  P := [9, 7, 17, 64, 4, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![503316480055893517076, -686694864900720416077, -842484542539652377952, -501370380672617275984, -201148962436479012014]
  a := ![-37, -48, -6, -1, -77]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![7088964507829486156, -9671758660573526987, -11865979472389470112, -7061554657360806704, -2833083977978577634]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 1804229351 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def PBC71 : ContainsPrimesAboveP 71 ![I71N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![71, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 71 (by decide) 𝕀

instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3297, 2338, 2474, 192, -278]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![-3297, 2338, 2474, 192, -278]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![30, 47, 60, 1, 0], ![57, 23, 63, 0, 1]] where
  M :=![![![-3297, 2338, 2474, 192, -278], ![8724, -6547, -6828, -526, 768], ![-16408, 12084, 12753, 994, -1436], ![18172, -13334, -14216, -1123, 1604], ![-14604, 10824, 11520, 912, -1301]]]
  hmulB := by decide  
  f := ![![![103, -142, -174, -104, -42]], ![![1052, -1431, -1756, -1042, -416]], ![![4672, -6384, -7831, -4666, -1876]], ![![4874, -6655, -8164, -4861, -1952]], ![![5335, -7287, -8939, -5324, -2139]]]
  g := ![![![93, -4, 116, 192, -278], ![-264, 7, -324, -526, 768], ![488, -22, 597, 994, -1436], ![-542, 35, -656, -1123, 1604], ![441, -29, 531, 912, -1301]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [66, 44, 30, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 70, 57], [35, 2, 16], [0, 1]]
 g := ![![[22, 24, 64], [44, 27], [26, 25], [36, 36, 35], [43, 1], []], ![[56, 62, 31, 54], [43, 18], [33, 65], [36, 62, 21, 49], [46, 4], [8, 37]], ![[11, 66, 36, 6], [19, 67], [10, 38], [26, 22, 58, 18], [52, 9], [49, 37]]]
 h' := ![![[8, 70, 57], [40, 12, 8], [30, 50, 10], [33, 63, 5], [9, 13, 53], [0, 0, 1], [0, 1]], ![[35, 2, 16], [1, 4, 43], [24, 46, 23], [42, 55, 24], [49, 7, 44], [47, 5, 2], [8, 70, 57]], ![[0, 1], [10, 57, 22], [13, 50, 40], [4, 28, 44], [56, 53, 49], [35, 68, 70], [35, 2, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 25], []]
 b := ![[], [21, 25, 70], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [66, 44, 30, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2140675324, -3007435922, -3670357699, -2234680976, -936817762]
  a := ![-8, -7, 1, -1, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1679174206, 1692731212, 2594931779, -2234680976, -936817762]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 389017 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, -142, -174, -104, -42]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![103, -142, -174, -104, -42]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![2, 14, 1, 0, 0], ![45, 68, 0, 1, 0], ![36, 69, 0, 0, 1]] where
  M :=![![![103, -142, -174, -104, -42], ![1052, -1431, -1756, -1042, -416], ![4672, -6384, -7831, -4666, -1876], ![22948, -31258, -38360, -22799, -9124], ![65052, -88752, -108888, -64800, -25997]]]
  hmulB := by decide  
  f := ![![![-3297, 2338, 2474, 192, -278]], ![![8724, -6547, -6828, -526, 768]], ![![1358, -1026, -1067, -82, 120]], ![![6343, -4840, -5030, -387, 566]], ![![6420, -4887, -5076, -390, 571]]]
  g := ![![![91, 168, -174, -104, -42], ![910, 1681, -1756, -1042, -416], ![4080, 7534, -7831, -4666, -1876], ![19919, 36790, -38360, -22799, -9124], ![56640, 104601, -108888, -64800, -25997]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P1 : CertificateIrreducibleZModOfList' 73 2 2 6 [28, 64, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 72], [0, 1]]
 g := ![![[44, 1], [38], [57], [36, 36], [8], [1]], ![[53, 72], [38], [57], [68, 37], [8], [1]]]
 h' := ![![[9, 72], [54, 1], [60, 44], [14, 38], [49, 6], [45, 9], [0, 1]], ![[0, 1], [63, 72], [18, 29], [64, 35], [30, 67], [53, 64], [9, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59]]
 b := ![[], [68, 66]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N1 : CertifiedPrimeIdeal' SI73N1 73 where
  n := 2
  hpos := by decide
  P := [28, 64, 1]
  hirr := P73P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3003906, 6803268, 7681694, 6117352, 3765220]
  a := ![52, 39, -8, -1, 103]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5879398, -10637268, 7681694, 6117352, 3765220]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N1 B_one_repr
lemma NI73N1 : Nat.card (O ⧸ I73N1) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![-3297, 2338, 2474, 192, -278]] ![![103, -142, -174, -104, -42]]
  ![![73, 0, 0, 0, 0]] where
 M := ![![![73, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![81, -23, -42, -5, 5]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![81, -23, -42, -5, 5]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![38, 42, 1, 1, 0], ![70, 69, 40, 0, 1]] where
  M :=![![![81, -23, -42, -5, 5], ![-160, 161, 164, 16, -20], ![396, -288, -337, -42, 42], ![-592, 414, 512, 75, -74], ![602, -482, -590, -114, 75]]]
  hmulB := by decide  
  f := ![![![-383, 287, 264, 17, -29]], ![![904, -673, -620, -40, 68]], ![![-1512, 1128, 1037, 66, -114]], ![![294, -218, -201, -13, 22]], ![![-328, 247, 226, 14, -25]]]
  g := ![![![-1, -2, -3, -5, 5], ![8, 11, 12, 16, -20], ![-12, -18, -25, -42, 42], ![22, 30, 43, 75, -74], ![-4, -11, -44, -114, 75]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [32, 21, 74, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 59, 29], [69, 19, 50], [0, 1]]
 g := ![![[2, 60, 21], [66, 55, 5], [34, 71, 73], [65, 11, 16], [5, 1], []], ![[20, 26, 60, 12], [75, 32, 33, 3], [11, 7, 67, 54], [60, 37, 77, 12], [69, 45], [43, 51]], ![[7, 61, 37, 20], [39, 67, 76, 1], [6, 14, 36, 1], [78, 15, 50, 26], [77, 5], [22, 51]]]
 h' := ![![[15, 59, 29], [21, 22, 69], [18, 60, 20], [53, 25, 51], [77, 21, 4], [0, 0, 1], [0, 1]], ![[69, 19, 50], [11, 21, 53], [18, 11, 66], [29, 64, 35], [54, 75, 53], [34, 25, 19], [15, 59, 29]], ![[0, 1], [74, 36, 36], [57, 8, 72], [46, 69, 72], [58, 62, 22], [28, 54, 59], [69, 19, 50]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [68, 78], []]
 b := ![[], [13, 41, 30], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [32, 21, 74, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![124738712958, -177090977654, -215723951518, -132387923504, -56318529550]
  a := ![-35, -20, 10, 2, -69]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![115161732590, 117331396816, 27460824734, -132387923504, -56318529550]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 493039 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![68389, -93256, -114424, -68066, -27285]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![68389, -93256, -114424, -68066, -27285]] 
 ![![79, 0, 0, 0, 0], ![29, 1, 0, 0, 0], ![39, 0, 1, 0, 0], ![52, 0, 0, 1, 0], ![51, 0, 0, 0, 1]] where
  M :=![![![68389, -93256, -114424, -68066, -27285], ![682418, -930556, -1141780, -679197, -272264], ![3063554, -4177509, -5125749, -3049091, -1222262], ![14943630, -20377373, -25002768, -14873094, -5962050], ![42512318, -57970460, -71128994, -42311634, -16961095]]]
  hmulB := by decide  
  f := ![![![-195447, 144190, 153390, 12054, -17291]], ![![-64875, 47876, 50898, 3997, -5737]], ![![-109505, 80763, 86009, 6767, -9697]], ![![-113854, 84027, 89216, 6996, -10054]], ![![-138173, 101906, 108560, 8544, -12240]]]
  g := ![![![154004, -93256, -114424, -68066, -27285], ![1536730, -930556, -1141780, -679197, -272264], ![6898780, -4177509, -5125749, -3049091, -1222262], ![33651403, -20377373, -25002768, -14873094, -5962050], ![95733003, -57970460, -71128994, -42311634, -16961095]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1

def I79N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, -175, -188, 9, 38]] i)))

def SI79N2: IdealEqSpanCertificate' Table ![![263, -175, -188, 9, 38]] 
 ![![79, 0, 0, 0, 0], ![49, 1, 0, 0, 0], ![39, 0, 1, 0, 0], ![47, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  M :=![![![263, -175, -188, 9, 38], ![-1122, 1002, 1152, 337, 36], ![358, 537, 809, 1157, 656], ![-8122, 9863, 11924, 6294, 2296], ![-16056, 22884, 28224, 17442, 7177]]]
  hmulB := by decide  
  f := ![![![869561, -648335, -599264, -38909, 65870]], ![![513349, -382737, -353772, -22970, 38886]], ![![472991, -352668, -325971, -21164, 35830]], ![![478699, -356904, -329896, -21421, 36262]], ![![128571, -95871, -88608, -5751, 9739]]]
  g := ![![![195, -175, -188, 9, 38], ![-1409, 1002, 1152, 337, 36], ![-1491, 537, 809, 1157, 656], ![-16113, 9863, 11924, 6294, 2296], ![-39525, 22884, 28224, 17442, 7177]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N2 : Nat.card (O ⧸ I79N2) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N2)

lemma isPrimeI79N2 : Ideal.IsPrime I79N2 := prime_ideal_of_norm_prime hp79.out _ NI79N2
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![81, -23, -42, -5, 5]] ![![68389, -93256, -114424, -68066, -27285]]
  ![![-981933, 1338995, 1642924, 977307, 391766]] where
 M := ![![![-981933, 1338995, 1642924, 977307, 391766]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI79N1 : IdealMulLeCertificate' Table 
  ![![-981933, 1338995, 1642924, 977307, 391766]] ![![263, -175, -188, 9, 38]]
  ![![79, 0, 0, 0, 0]] where
 M := ![![![-15400316327, 21000113538, 25766863412, 15327619816, 6144249964]]]
 hmul := by decide  
 g := ![![![![-194940713, 265824222, 326162828, 194020504, 77775316]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1, I79N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
    exact isPrimeI79N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0 ⊙ MulI79N1)
instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 6671, 4010, 125, -440]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![3, 6671, 4010, 125, -440]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![15, 53, 25, 1, 0], ![45, 38, 31, 0, 1]] where
  M :=![![![3, 6671, 4010, 125, -440], ![13450, -2076, -4508, -465, 500], ![-14690, 11721, 10643, 707, -1180], ![11682, -12235, -10332, -688, 1164], ![-13500, 5184, 6600, 654, -767]]]
  hmulB := by decide  
  f := ![![![329, -157, -150, 103, 96]], ![![-2674, 2806, 3320, 1421, 412]], ![![-3422, 6297, 7965, 5813, 2636]], ![![-3069, 4169, 5113, 3031, 1212]], ![![-3299, 4900, 6071, 3876, 1629]]]
  g := ![![![216, 202, 175, 125, -440], ![-25, 43, -101, -465, 500], ![335, 230, 356, 707, -1180], ![-366, -241, -352, -688, 1164], ![135, -4, 169, 654, -767]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [47, 45, 48, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [69, 59, 6], [49, 23, 77], [0, 1]]
 g := ![![[78, 66, 30], [57, 10, 7], [59, 68], [10, 16], [18, 35, 1], []], ![[28, 60, 62, 55], [10, 68, 11, 47], [50, 10], [21, 70], [24, 31, 82, 20], [59, 36]], ![[15, 12, 44, 17], [60, 39, 54, 48], [66, 70], [3, 12], [67, 28, 6, 30], [71, 36]]]
 h' := ![![[69, 59, 6], [60, 47, 69], [29, 16, 16], [35, 2, 63], [67, 35, 4], [0, 0, 1], [0, 1]], ![[49, 23, 77], [39, 24, 43], [73, 78, 49], [4, 80, 50], [59, 64, 53], [79, 60, 23], [69, 59, 6]], ![[0, 1], [29, 12, 54], [30, 72, 18], [12, 1, 53], [30, 67, 26], [60, 23, 59], [49, 23, 77]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 75], []]
 b := ![[], [58, 3, 29], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [47, 45, 48, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-353435497, 734294670, 843807706, 648264950, 377722512]
  a := ![8, -2, -6, -10, 16]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-326203889, -578038592, -326171252, 648264950, 377722512]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 571787 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![329, -157, -150, 103, 96]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![329, -157, -150, 103, 96]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![4, 59, 1, 0, 0], ![13, 37, 0, 1, 0], ![77, 18, 0, 0, 1]] where
  M :=![![![329, -157, -150, 103, 96], ![-2674, 2806, 3320, 1421, 412], ![-3422, 6297, 7965, 5813, 2636], ![-32390, 42239, 51544, 29390, 11420], ![-80928, 111930, 137568, 82872, 33515]]]
  hmulB := by decide  
  f := ![![![3, 6671, 4010, 125, -440]], ![![13450, -2076, -4508, -465, 500]], ![![9384, -1013, -2883, -316, 320]], ![![6137, -28, -1506, -196, 168]], ![![2757, 5801, 2822, 23, -309]]]
  g := ![![![-94, 38, -150, 103, 96], ![-797, -3049, 3320, 1421, 412], ![-3781, -8749, 7965, 5813, 2636], ![-18072, -51709, 51544, 29390, 11420], ![-51677, -140652, 137568, 82872, 33515]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P1 : CertificateIrreducibleZModOfList' 83 2 2 6 [24, 62, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 82], [0, 1]]
 g := ![![[51, 7], [52, 70], [75], [27], [36, 26], [1]], ![[32, 76], [28, 13], [75], [27], [1, 57], [1]]]
 h' := ![![[21, 82], [80, 16], [43, 53], [10, 65], [49, 44], [59, 21], [0, 1]], ![[0, 1], [1, 67], [77, 30], [47, 18], [60, 39], [2, 62], [21, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38]]
 b := ![[], [8, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N1 : CertifiedPrimeIdeal' SI83N1 83 where
  n := 2
  hpos := by decide
  P := [24, 62, 1]
  hirr := P83P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1384334, 2994129, 3402056, 2655310, 1601086]
  a := ![40, 24, -6, 1, 67]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2081870, -3913171, 3402056, 2655310, 1601086]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N1 B_one_repr
lemma NI83N1 : Nat.card (O ⧸ I83N1) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![3, 6671, 4010, 125, -440]] ![![329, -157, -150, 103, 96]]
  ![![83, 0, 0, 0, 0]] where
 M := ![![![83, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0, 0, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0, 0, 0]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![0, 0, 0, 89, 0], ![0, 0, 0, 0, 89]] where
  M :=![![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![0, 0, 0, 89, 0], ![0, 0, 0, 0, 89]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 5 2 6 [9, 45, 75, 27, 31, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [78, 75, 86, 2, 15], [28, 72, 10, 69, 4], [7, 5, 0, 40, 35], [34, 25, 82, 67, 35], [0, 1]]
 g := ![![[21, 55, 43, 81, 45], [56, 62, 52, 45], [66, 6, 43, 67], [34, 55, 41, 7, 71], [1], []], ![[67, 17, 70, 85, 58, 60, 41, 59], [62, 82, 75, 73], [17, 48, 58, 11], [58, 81, 26, 12, 43, 18, 70, 59], [35, 64, 79, 58, 24, 83, 49, 29], [76, 33, 27, 47]], ![[43, 83, 81, 43, 36, 23, 30, 80], [37, 77, 68, 72], [40, 65, 45, 69], [88, 9, 13, 6, 8, 30, 43, 45], [33, 3, 63, 76, 77, 60, 59, 88], [41, 3, 56, 16]], ![[47, 84, 50, 75, 59, 45, 51, 61], [62, 73, 69, 22], [40, 80, 54, 72], [15, 27, 0, 35, 63, 48, 62, 66], [7, 51, 66, 69, 75, 79, 0, 70], [84, 28, 69, 68]], ![[40, 16, 84, 23, 46, 10, 75, 24], [63, 74, 32, 10], [70, 40, 64, 50], [72, 65, 19, 15, 69, 57, 61, 29], [46, 39, 39, 44, 62, 43, 72, 75], [81, 85, 1, 68]]]
 h' := ![![[78, 75, 86, 2, 15], [64, 11, 3, 62, 32], [37, 67, 57, 24, 32], [50, 14, 44, 73, 45], [80, 44, 14, 62, 58], [0, 0, 1], [0, 1]], ![[28, 72, 10, 69, 4], [81, 68, 55, 56, 40], [4, 49, 66, 13, 42], [54, 0, 15, 29, 79], [46, 88, 55, 7, 40], [60, 62, 43, 16, 68], [78, 75, 86, 2, 15]], ![[7, 5, 0, 40, 35], [23, 45, 26, 32, 51], [0, 5, 19, 22, 28], [2, 19, 73, 16, 46], [72, 6, 53, 86, 16], [59, 24, 72, 62, 72], [28, 72, 10, 69, 4]], ![[34, 25, 82, 67, 35], [16, 39, 78, 84, 62], [60, 78, 88, 9, 17], [8, 40, 48, 45, 61], [23, 47, 35, 49, 54], [5, 43, 32, 40, 64], [7, 5, 0, 40, 35]], ![[0, 1], [24, 15, 16, 33, 82], [18, 68, 37, 21, 59], [84, 16, 87, 15, 36], [11, 82, 21, 63, 10], [71, 49, 30, 60, 63], [34, 25, 82, 67, 35]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34, 39, 49, 50], [], [], []]
 b := ![[], [52, 3, 41, 58, 56], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 5
  hpos := by decide
  P := [9, 45, 75, 27, 31, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7592429027337689, 10363792741091919, 12713873258409584, 7569128163786085, 3039100437819751]
  a := ![4, 1, -2, -1, 9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-85308191318401, 116447109450471, 142852508521456, 85046383862765, 34147195930559]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 5584059449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def PBC89 : ContainsPrimesAboveP 89 ![I89N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![89, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 89 (by decide) 𝕀

instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4315, -5888, -7228, -4302, -1724]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![4315, -5888, -7228, -4302, -1724]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![29, 44, 61, 1, 0], ![69, 12, 92, 0, 1]] where
  M :=![![![4315, -5888, -7228, -4302, -1724], ![43116, -58797, -72132, -42910, -17208], ![193652, -264024, -323981, -192698, -77216], ![943984, -1287410, -1579580, -939729, -376792], ![2686740, -3663414, -4495032, -2673750, -1071673]]]
  hmulB := by decide  
  f := ![![![-10397, 6092, 7364, 638, -836]], ![![26356, -21185, -22532, -1794, 2552]], ![![-53252, 38916, 42915, 3506, -4864]], ![![-23989, 16214, 18447, 1539, -2092]], ![![-55165, 39018, 43584, 3592, -4941]]]
  g := ![![![2557, 2104, 4266, -4302, -1724], ![25514, 20987, 42562, -42910, -17208], ![114534, 94240, 191077, -192698, -77216], ![558709, 459610, 932049, -939729, -376792], ![1589391, 1307646, 2651522, -2673750, -1071673]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [1, 7, 57, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 41, 62], [15, 55, 35], [0, 1]]
 g := ![![[72, 86, 12], [68, 44], [0, 64], [62, 16], [2, 48], [1]], ![[78, 57, 87, 27], [55, 62], [7, 94], [33, 48], [32, 12], [82, 12, 91, 96]], ![[19, 38, 92, 11], [28, 49], [39, 89], [44, 35], [2, 11], [89, 70, 17, 1]]]
 h' := ![![[25, 41, 62], [90, 5, 77], [35, 56, 23], [36, 34, 8], [96, 49, 4], [96, 90, 40], [0, 1]], ![[15, 55, 35], [67, 38, 83], [92, 0, 81], [14, 64, 26], [12, 83, 57], [23, 47, 20], [25, 41, 62]], ![[0, 1], [21, 54, 34], [90, 41, 90], [41, 96, 63], [45, 62, 36], [85, 57, 37], [15, 55, 35]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54, 45], []]
 b := ![[], [91, 47, 29], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [1, 7, 57, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-322590801808, 459580832690, 559484157378, 344245896037, 147151982774]
  a := ![49, 29, -10, -4, 95]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-210919676271, -169619199858, -350283483671, 344245896037, 147151982774]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 912673 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10397, 6092, 7364, 638, -836]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![-10397, 6092, 7364, 638, -836]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![79, 37, 1, 0, 0], ![84, 96, 0, 1, 0], ![52, 9, 0, 0, 1]] where
  M :=![![![-10397, 6092, 7364, 638, -836], ![26356, -21185, -22532, -1794, 2552], ![-53252, 38916, 42915, 3506, -4864], ![63288, -45646, -50604, -4149, 5736], ![-50700, 38346, 41736, 3378, -4729]]]
  hmulB := by decide  
  f := ![![![4315, -5888, -7228, -4302, -1724]], ![![43116, -58797, -72132, -42910, -17208]], ![![21957, -29945, -36741, -21858, -8764]], ![![56140, -76562, -93932, -55881, -22408]], ![![34012, -46379, -56908, -33852, -13569]]]
  g := ![![![-6209, -3300, 7364, 638, -836], ![18808, 9915, -22532, -1794, 2552], ![-35929, -18987, 42915, 3506, -4864], ![42384, 22406, -50604, -4149, 5736], ![-34904, -18429, 41736, 3378, -4729]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P1 : CertificateIrreducibleZModOfList' 97 2 2 6 [60, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 96], [0, 1]]
 g := ![![[], [], [], [], [11], [0, 1]], ![[], [], [], [], [11], [0, 96]]]
 h' := ![![[0, 96], [75], [50], [70], [19], [0, 37], [0, 1]], ![[0, 1], [75], [50], [70], [19], [0, 60], [0, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [76]]
 b := ![[], [0, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N1 : CertifiedPrimeIdeal' SI97N1 97 where
  n := 2
  hpos := by decide
  P := [60, 0, 1]
  hirr := P97P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-497078, 1148588, 1294026, 1039636, 644376]
  a := ![22, 13, -6, -1, 43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2304764, -1570462, 1294026, 1039636, 644376]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N1 B_one_repr
lemma NI97N1 : Nat.card (O ⧸ I97N1) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![4315, -5888, -7228, -4302, -1724]] ![![-10397, 6092, 7364, 638, -836]]
  ![![97, 0, 0, 0, 0]] where
 M := ![![![97, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-497, 368, 606, 182, -116]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![-497, 368, 606, 182, -116]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![30, 84, 58, 1, 0], ![47, 52, 91, 0, 1]] where
  M :=![![![-497, 368, 606, 182, -116], ![3844, -2887, -4268, -1174, 728], ![-14016, 10344, 14981, 3822, -2712], ![42580, -32226, -45584, -12107, 7280], ![-56768, 40904, 58532, 13608, -11585]]]
  hmulB := by decide  
  f := ![![![-6813, -10348, -4818, -22, 532]], ![![-16004, -6551, 628, 494, -88]], ![![9816, -8964, -9119, -702, 1032]], ![![-9778, -13530, -6026, 9, 664]], ![![-2399, -16276, -10195, -396, 1139]]]
  g := ![![![-5, -88, 6, 182, -116], ![48, 573, -24, -1174, 728], ![-12, -1680, 397, 3822, -2712], ![630, 6002, -58, -12107, 7280], ![787, -4948, 3203, 13608, -11585]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [22, 65, 45, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [34, 64, 25], [22, 36, 76], [0, 1]]
 g := ![![[26, 28, 13], [21, 22], [9, 12, 1], [6, 9], [70, 5], [1]], ![[52, 49], [67, 4], [82, 97, 94, 5], [38, 82], [33, 68], [3, 25, 49, 71]], ![[25, 81, 97, 79], [18, 19], [46, 96, 15, 16], [34, 5], [32, 31], [17, 97, 96, 30]]]
 h' := ![![[34, 64, 25], [59, 10, 66], [4, 43, 74], [65, 79, 1], [55, 18, 3], [79, 36, 56], [0, 1]], ![[22, 36, 76], [8, 62], [88, 87, 2], [90, 86, 92], [57, 79, 53], [50, 17, 88], [34, 64, 25]], ![[0, 1], [96, 29, 35], [47, 72, 25], [97, 37, 8], [80, 4, 45], [73, 48, 58], [22, 36, 76]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46, 24], []]
 b := ![[], [98, 12, 96], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [22, 65, 45, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9205118290, 12977011400, 15827422943, 9661688595, 4070495900]
  a := ![16, 10, -3, 1, 28]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4855139440, -10002679380, -9059065767, 9661688595, 4070495900]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 1030301 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, -5, -6, -1, 1]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![7, -5, -6, -1, 1]] 
 ![![101, 0, 0, 0, 0], ![27, 1, 0, 0, 0], ![26, 0, 1, 0, 0], ![90, 0, 0, 1, 0], ![85, 0, 0, 0, 1]] where
  M :=![![![7, -5, -6, -1, 1], ![-32, 25, 32, 8, -4], ![84, -58, -79, -14, 18], ![-268, 222, 300, 95, -26], ![214, -96, -158, 20, 97]]]
  hmulB := by decide  
  f := ![![![2269, -1145, -1456, -129, 165]], ![![555, -262, -344, -31, 39]], ![![690, -372, -459, -40, 52]], ![![1898, -932, -1200, -107, 136]], ![![2007, -1039, -1306, -115, 148]]]
  g := ![![![3, -5, -6, -1, 1], ![-19, 25, 32, 8, -4], ![34, -58, -79, -14, 18], ![-202, 222, 300, 95, -26], ![-31, -96, -158, 20, 97]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-65, 90, 110, 66, 27]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![-65, 90, 110, 66, 27]] 
 ![![101, 0, 0, 0, 0], ![60, 1, 0, 0, 0], ![89, 0, 1, 0, 0], ![27, 0, 0, 1, 0], ![76, 0, 0, 0, 1]] where
  M :=![![![-65, 90, 110, 66, 27], ![-678, 918, 1128, 667, 264], ![-2954, 4053, 4967, 2969, 1202], ![-14722, 20003, 24560, 14568, 5806], ![-41386, 56536, 69346, 41310, 16607]]]
  hmulB := by decide  
  f := ![![![-130959, 97920, 90588, 5894, -9961]], ![![-74722, 55880, 51692, 3363, -5684]], ![![-120577, 90147, 83403, 5427, -9171]], ![![-30411, 22747, 21036, 1368, -2313]], ![![-102062, 76304, 70598, 4594, -7763]]]
  g := ![![![-189, 90, 110, 66, 27], ![-1923, 918, 1128, 667, 264], ![-8512, 4053, 4967, 2969, 1202], ![-41934, 20003, 24560, 14568, 5806], ![-118642, 56536, 69346, 41310, 16607]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![-497, 368, 606, 182, -116]] ![![7, -5, -6, -1, 1]]
  ![![-37951, 28077, 39812, 9927, -7045]] where
 M := ![![![-37951, 28077, 39812, 9927, -7045]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![-37951, 28077, 39812, 9927, -7045]] ![![-65, 90, 110, 66, 27]]
  ![![101, 0, 0, 0, 0]] where
 M := ![![![11245037, -16009207, -19493000, -11987993, -5118478]]]
 hmul := by decide  
 g := ![![![![111337, -158507, -193000, -118693, -50678]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-915, 675, 720, 61, -82]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![-915, 675, 720, 61, -82]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![0, 0, 0, 103, 0], ![30, 91, 49, 101, 1]] where
  M :=![![![-915, 675, 720, 61, -82], ![2582, -1898, -2052, -179, 244], ![-5130, 3803, 4187, 445, -480], ![6354, -4581, -5216, -506, 768], ![-6532, 5126, 6072, 1232, -513]]]
  hmulB := by decide  
  f := ![![![1419, 1455, 532, -17, -58]], ![![1706, 1724, 624, -21, -68]], ![![146, 179, 73, -1, -8]], ![![-734, -779, -292, 8, 32]], ![![1260, 1258, 451, -16, -49]]]
  g := ![![![15, 79, 46, 81, -82], ![-46, -234, -136, -241, 244], ![90, 461, 269, 475, -480], ![-162, -723, -416, -758, 768], ![86, 503, 303, 515, -513]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 4 2 6 [68, 22, 44, 93, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [74, 90, 37, 72], [30, 60, 19, 59], [9, 55, 47, 75], [0, 1]]
 g := ![![[8, 12, 88, 9], [80, 86, 50, 61], [8, 62, 97, 66], [24, 63, 25], [56, 10, 1], []], ![[32, 45, 35, 1, 87, 72], [76, 47, 20, 9, 18, 72], [39, 87, 80, 41, 59, 56], [45, 10, 64], [40, 3, 63], [50, 17, 10, 41, 32, 79]], ![[82, 50, 93, 83, 73, 7], [23, 15, 93, 85, 16, 81], [95, 15, 75, 98, 7, 63], [20, 72, 97], [3, 45, 23], [19, 1, 26, 84, 9, 100]], ![[46, 41, 59, 55, 102, 57], [31, 28, 79, 93, 71, 73], [33, 26, 85, 0, 79, 37], [33, 68, 52], [68, 37, 55], [7, 100, 51, 79, 101, 90]]]
 h' := ![![[74, 90, 37, 72], [19, 31, 69, 100], [74, 44, 46, 79], [25, 93, 14, 13], [3, 45, 29, 98], [0, 0, 0, 1], [0, 1]], ![[30, 60, 19, 59], [90, 42, 49, 102], [47, 14, 13, 102], [96, 50, 101, 26], [90, 21, 78, 95], [21, 68, 101, 28], [74, 90, 37, 72]], ![[9, 55, 47, 75], [13, 29, 51, 7], [46, 32, 3, 84], [101, 5, 79, 21], [15, 51, 60, 32], [61, 10, 20, 34], [30, 60, 19, 59]], ![[0, 1], [87, 1, 37, 100], [85, 13, 41, 44], [78, 58, 12, 43], [57, 89, 39, 84], [47, 25, 85, 40], [9, 55, 47, 75]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [70, 83, 76], []]
 b := ![[], [], [92, 74, 99, 86], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 4
  hpos := by decide
  P := [68, 22, 44, 93, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-594249460826010068, 813986569048516946, 997937298725590006, 595756828813993148, 240511706035008213]
  a := ![-105, -72, 16, 0, -217]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-75821365455109286, -204588142525604179, -104729478611551577, -230057528939046955, 240511706035008213]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 112550881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1419, 1455, 532, -17, -58]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![1419, 1455, 532, -17, -58]] 
 ![![103, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![67, 0, 1, 0, 0], ![37, 0, 0, 1, 0], ![98, 0, 0, 0, 1]] where
  M :=![![![1419, 1455, 532, -17, -58], ![1706, 1724, 624, -21, -68], ![146, 179, 73, -1, -8], ![-734, -779, -292, 8, 32], ![-1056, -1052, -376, 14, 41]]]
  hmulB := by decide  
  f := ![![![-915, 675, 720, 61, -82]], ![![-46, 34, 36, 3, -4]], ![![-645, 476, 509, 44, -58]], ![![-267, 198, 208, 17, -22]], ![![-934, 692, 744, 70, -83]]]
  g := ![![![-384, 1455, 532, -17, -58], ![-451, 1724, 624, -21, -68], ![-52, 179, 73, -1, -8], ![210, -779, -292, 8, 32], ![272, -1052, -376, 14, 41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![-915, 675, 720, 61, -82]] ![![1419, 1455, 532, -17, -58]]
  ![![103, 0, 0, 0, 0]] where
 M := ![![![103, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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


lemma PB3864I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB3864I2 : PrimesBelowBoundCertificateInterval O 61 103 3864 where
  m := 9
  g := ![2, 1, 2, 3, 2, 1, 2, 3, 2]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB3864I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0, I67N1]
    · exact ![I71N0]
    · exact ![I73N0, I73N1]
    · exact ![I79N0, I79N1, I79N2]
    · exact ![I83N0, I83N1]
    · exact ![I89N0]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1, I101N2]
    · exact ![I103N0, I103N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC67
    · exact PBC71
    · exact PBC73
    · exact PBC79
    · exact PBC83
    · exact PBC89
    · exact PBC97
    · exact PBC101
    · exact PBC103
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![20151121, 67]
    · exact ![1804229351]
    · exact ![389017, 5329]
    · exact ![493039, 79, 79]
    · exact ![571787, 6889]
    · exact ![5584059449]
    · exact ![912673, 9409]
    · exact ![1030301, 101, 101]
    · exact ![112550881, 103]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
      exact NI79N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
      exact NI101N2
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
  β := ![I67N1, I79N1, I79N2, I101N1, I101N2, I103N1]
  Il := ![[I67N1], [], [], [I79N1, I79N2], [], [], [], [I101N1, I101N2], [I103N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
