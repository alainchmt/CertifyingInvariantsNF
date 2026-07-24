
import IdealArithmetic.Examples.NF5_1_42187500_1.RI5_1_42187500_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![575, -154, -154, -2, 304]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![575, -154, -154, -2, 304]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![0, 0, 67, 0, 0], ![1, 16, 47, 1, 0], ![3, 45, 43, 0, 1]] where
  M :=![![![575, -154, -154, -2, 304], ![606, 727, 770, -926, -1544], ![-4014, 758, 1651, -2, -3392], ![-3696, -3240, -5088, 5501, 9240], ![1534, 1382, 2312, -2466, -4049]]]
  hmulB := by decide  
  f := ![![![-41788451, -28767126, -4818006, -20044382, -33873712]], ![![-87791806, -60435787, -10121970, -42110498, -71164024]], ![![-184438546, -126967302, -21264871, -88468382, -149505856]], ![![-153207659, -105467992, -17664101, -73488075, -124190104]], ![![-180100081, -123980707, -20764667, -86387380, -145989097]]]
  g := ![![![-5, -206, -196, -2, 304], ![92, 1269, 1652, -926, -1544], ![92, 2290, 2203, -2, -3392], ![-551, -7568, -9865, 5501, 9240], ![241, 3329, 4363, -2466, -4049]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [55, 38, 25, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 29, 38], [18, 37, 29], [0, 1]]
 g := ![![[2, 57, 26], [18, 13, 59], [33, 39], [1, 55], [42, 1], []], ![[36, 21, 25, 7], [28, 53, 31, 13], [49, 62], [27, 24], [12, 29], [6, 37]], ![[13, 63, 1, 33], [36, 44, 0, 25], [10, 19], [10, 23], [13, 37], [15, 37]]]
 h' := ![![[24, 29, 38], [15, 29, 48], [17, 32, 40], [31, 24, 21], [35, 24, 51], [0, 0, 1], [0, 1]], ![[18, 37, 29], [57, 37, 64], [39, 57, 16], [11, 26, 14], [25, 26, 52], [45, 0, 37], [24, 29, 38]], ![[0, 1], [6, 1, 22], [50, 45, 11], [59, 17, 32], [41, 17, 31], [35, 0, 29], [18, 37, 29]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50, 22], []]
 b := ![[], [39, 65, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [55, 38, 25, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-362783, 1552387, 2542383, -1975292, -5038572]
  a := ![-5, 3, 27, -28, -60]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![249675, 3878997, 4657309, -1975292, -5038572]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 300763 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41788451, 28767126, 4818006, 20044382, 33873712]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![41788451, 28767126, 4818006, 20044382, 33873712]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![38, 40, 1, 0, 0], ![44, 57, 0, 1, 0], ![38, 22, 0, 0, 1]] where
  M :=![![![41788451, 28767126, 4818006, 20044382, 33873712], ![87791806, 60435787, 10121970, 42110498, 71164024], ![184438546, 126967302, 21264871, 88468382, 149505856], ![149844144, 103152552, 17276304, 71874721, 121463640], ![59851326, 41201590, 6900568, 28708478, 48515475]]]
  hmulB := by decide  
  f := ![![![-575, 154, 154, 2, -304]], ![![-606, -727, -770, 926, 1544]], ![![-628, -358, -397, 554, 800]], ![![-838, -469, -478, 707, 976]], ![![-548, -172, -200, 342, 395]]]
  g := ![![![-34484323, -30622456, 4818006, 20044382, 33873712], ![-72446834, -64333581, 10121970, 42110498, 71164024], ![-152200864, -135156032, 21264871, 88468382, 149505856], ![-123653156, -109805355, 17276304, 71874721, 121463640], ![-49390020, -43858878, 6900568, 28708478, 48515475]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P1 : CertificateIrreducibleZModOfList' 67 2 2 6 [33, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 66], [0, 1]]
 g := ![![[0, 65], [], [], [], [], [1]], ![[0, 2], [], [], [], [], [1]]]
 h' := ![![[0, 66], [0, 47], [39], [21], [17], [34], [0, 1]], ![[0, 1], [0, 20], [39], [21], [17], [34], [0, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65]]
 b := ![[], [0, 66]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N1 : CertifiedPrimeIdeal' SI67N1 67 where
  n := 2
  hpos := by decide
  P := [33, 0, 1]
  hirr := P67P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![78185, 82295, 113186, -104313, -202899]
  a := ![6, -68, -31, -33, 69]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![120553, 89022, 113186, -104313, -202899]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N1 B_one_repr
lemma NI67N1 : Nat.card (O ⧸ I67N1) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![575, -154, -154, -2, 304]] ![![41788451, 28767126, 4818006, 20044382, 33873712]]
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


def P71P0 : CertificateIrreducibleZModOfList' 71 5 2 6 [2, 2, 15, 1, 53, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 17, 6, 1, 59], [56, 4, 26, 40, 34], [10, 56, 42, 35, 18], [54, 64, 68, 66, 31], [0, 1]]
 g := ![![[51, 33, 15, 4, 10], [63, 8, 29, 22, 58], [2, 32, 43, 42, 43], [30, 39, 18, 1], [], []], ![[70, 33, 57, 3, 35, 70], [36, 31, 38, 17, 12, 63, 46, 61], [28, 10, 36, 45, 10, 67, 7, 67], [56, 24, 49, 49], [55, 27, 65, 2], [59, 0, 12, 2]], ![[50, 24, 6, 34, 65, 3, 9, 28], [33, 55, 8, 40, 37, 47, 30, 66], [54, 51, 45, 43, 36, 68, 41, 55], [64, 59, 69, 45], [61, 25, 3, 43], [37, 0, 27, 20]], ![[22, 35, 13, 50, 69, 40, 33, 15], [67, 67, 7, 44, 66, 0, 13, 16], [63, 24, 33, 68, 58, 39, 67, 36], [35, 64, 31, 49], [49, 50, 27, 60], [50, 68, 63, 40]], ![[40, 20, 67, 4, 33, 18, 56, 39], [47, 65, 61, 51, 53, 24, 48, 41], [23, 54, 20, 62, 66, 65, 42, 21], [40, 6, 11, 15], [35, 49, 32, 1], [19, 1, 19, 38]]]
 h' := ![![[40, 17, 6, 1, 59], [16, 16, 48, 65, 62], [67, 53, 50, 20, 49], [11, 4, 4, 57, 16], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[56, 4, 26, 40, 34], [56, 11, 56, 52], [42, 70, 55, 22, 29], [19, 26, 32, 5, 38], [42, 58, 38, 47, 7], [62, 35, 2, 55, 59], [40, 17, 6, 1, 59]], ![[10, 56, 42, 35, 18], [18, 32, 2, 54, 17], [26, 60, 1, 30, 58], [62, 14, 25, 29, 49], [30, 28, 23, 1, 20], [9, 19, 47, 13, 55], [56, 4, 26, 40, 34]], ![[54, 64, 68, 66, 31], [33, 29, 53, 51, 42], [40, 12, 45, 43, 63], [20, 57, 30, 69, 12], [44, 15, 64, 5, 64], [0, 32, 53, 10, 29], [10, 56, 42, 35, 18]], ![[0, 1], [56, 54, 54, 62, 21], [49, 18, 62, 27, 14], [48, 41, 51, 53, 27], [25, 41, 17, 18, 50], [38, 56, 39, 64, 70], [54, 64, 68, 66, 31]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19, 38, 7, 59], [], [], []]
 b := ![[], [47, 60, 43, 54, 70], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 5
  hpos := by decide
  P := [2, 2, 15, 1, 53, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-61791158, -206381522, -339829146, 299199396, 656559720]
  a := ![-1, -2, 6, -9, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-870298, -2906782, -4786326, 4214076, 9247320]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6325, -364, -408, -1742, 1736]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![6325, -364, -408, -1742, 1736]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![46, 69, 36, 1, 0], ![3, 2, 48, 0, 1]] where
  M :=![![![6325, -364, -408, -1742, 1736], ![1730, 9395, 15296, -12998, -29584], ![-72166, 440, -1369, 24770, -8056], ![3464, -57878, -93822, 75111, 183552], ![-1058, 26656, 43226, -34782, -84487]]]
  hmulB := by decide  
  f := ![![![2109, -2120, 124, 82, 952]], ![![1986, 3103, 244, -1246, -3776]], ![![-8798, -300, -749, 1810, 3928]], ![![-1080, 1377, -58, -227, -992]], ![![-5719, -158, -486, 1164, 2513]]]
  g := ![![![1113, 1594, -288, -1742, 1736], ![9430, 13225, 26072, -12998, -29584], ![-16266, -23186, -6937, 24770, -8056], ![-54826, -76817, -159018, 75111, 183552], ![25375, 35556, 73298, -34782, -84487]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [63, 58, 58, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [53, 12, 64], [35, 60, 9], [0, 1]]
 g := ![![[71, 58, 69], [53, 70], [3, 6], [55, 60, 3], [15, 1], []], ![[37, 4, 22, 41], [9, 6], [9, 1], [8, 34, 62, 46], [5, 23], [50, 8]], ![[52, 56, 1, 61], [64, 2], [52, 50], [36, 45, 69, 35], [38, 71], [32, 8]]]
 h' := ![![[53, 12, 64], [51, 30, 19], [18, 10, 56], [39, 54, 58], [4, 16, 21], [0, 0, 1], [0, 1]], ![[35, 60, 9], [53, 2, 67], [67, 10, 58], [59, 70, 1], [42, 23, 21], [24, 58, 60], [53, 12, 64]], ![[0, 1], [15, 41, 60], [18, 53, 32], [70, 22, 14], [13, 34, 31], [12, 15, 12], [35, 60, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32, 32], []]
 b := ![[], [46, 51, 36], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [63, 58, 58, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-22227565, -4412999, -9305145, 16123248, 16146819]
  a := ![8, 11, -43, 58, 95]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-11127910, -15742613, -18695745, 16123248, 16146819]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 389017 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![114613, -10217, -13271, -26788, 42926]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![114613, -10217, -13271, -26788, 42926]] 
 ![![73, 0, 0, 0, 0], ![17, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![39, 0, 0, 1, 0], ![41, 0, 0, 0, 1]] where
  M :=![![![114613, -10217, -13271, -26788, 42926], ![59064, 171056, 279289, -246334, -536086], ![-1318506, 48601, 40802, 399080, -275578], ![-105570, -1061709, -1725951, 1437247, 3351468], ![58454, 488677, 794695, -664992, -1541683]]]
  hmulB := by decide  
  f := ![![![9624280331, 6625344579, 1109632911, 4616413202, 7801440430]], ![![2518247393, 1733558881, 290341728, 1207910622, 2041291008]], ![![977408281, 672846846, 112690441, 468826784, 792287008]], ![![5614485945, 3865006290, 647323038, 2693062351, 4551101598]], ![![5594244211, 3851071900, 644989264, 2683353132, 4534693643]]]
  g := ![![![-5303, -10217, -13271, -26788, 42926], ![382189, 171056, 279289, -246334, -536086], ![-89487, 48601, 40802, 399080, -275578], ![-2333445, -1061709, -1725951, 1437247, 3351468], ![1075487, 488677, 794695, -664992, -1541683]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1

def I73N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151781, -62669, -97315, 29328, 212412]] i)))

def SI73N2: IdealEqSpanCertificate' Table ![![151781, -62669, -97315, 29328, 212412]] 
 ![![73, 0, 0, 0, 0], ![57, 1, 0, 0, 0], ![36, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![63, 0, 0, 0, 1]] where
  M :=![![![151781, -62669, -97315, 29328, 212412], ![454152, 237550, 398599, -472814, -710124], ![-1893062, 615441, 944062, -146624, -2123148], ![-2423536, -1581537, -2636429, 2937057, 4783188], ![1130426, 723893, 1207343, -1351760, -2187385]]]
  hmulB := by decide  
  f := ![![![-115580521, -79566089, -13325929, -55442062, -93694428]], ![![-93574255, -64416793, -10788698, -44885902, -75855000]], ![![-63986812, -44048855, -7377400, -30693282, -51870084]], ![![-12010562, -8268127, -1384765, -5761233, -9736188]], ![![-102015343, -70227774, -11761922, -48934980, -82697725]]]
  g := ![![![-85918, -62669, -97315, 29328, 212412], ![262922, 237550, 398599, -472814, -710124], ![868293, 615441, 944062, -146624, -2123148], ![-1787035, -1581537, -2636429, 2937057, 4783188], ![816664, 723893, 1207343, -1351760, -2187385]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N2 : Nat.card (O ⧸ I73N2) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N2)

lemma isPrimeI73N2 : Ideal.IsPrime I73N2 := prime_ideal_of_norm_prime hp73.out _ NI73N2
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![6325, -364, -408, -1742, 1736]] ![![114613, -10217, -13271, -26788, 42926]]
  ![![1526757461, 2551124233, 4183949675, -3900703550, -7935540866]] where
 M := ![![![1526757461, 2551124233, 4183949675, -3900703550, -7935540866]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI73N1 : IdealMulLeCertificate' Table 
  ![![1526757461, 2551124233, 4183949675, -3900703550, -7935540866]] ![![151781, -62669, -97315, 29328, 212412]]
  ![![73, 0, 0, 0, 0]] where
 M := ![![![-6047191433037509, 3509937876402428, 5521215307756114, -2504539892860844, -11670172678347850]]]
 hmul := by decide  
 g := ![![![![-82838238808733, 48081340772636, 75633086407618, -34308765655628, -159865379155450]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1, I73N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
    exact isPrimeI73N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0 ⊙ MulI73N1)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![168005315, 115663685, 19370627, 80596196, 136204114]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![168005315, 115663685, 19370627, 80596196, 136204114]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![48, 15, 63, 1, 0], ![62, 10, 24, 0, 1]] where
  M :=![![![168005315, 115663685, 19370627, 80596196, 136204114], ![353004424, 242983860, 40698851, 169314006, 286133782], ![741581570, 510523051, 85501170, 355700168, 601099162], ![602447034, 414748937, 69460339, 288995425, 488386212], ![240668434, 165667663, 27747381, 115422256, 195050635]]]
  hmulB := by decide  
  f := ![![![7872635, -139137, 1499, -2582062, 1167230]], ![![-247602, 11623426, 18854925, -15241772, -36820894]], ![![-88883560, -2971799, -7388624, 35142778, 1203206]], ![![-65906246, -1145166, -3761068, 24662221, -2458548]], ![![-20957222, 873069, 811743, 6210610, -4698621]]]
  g := ![![![-153737559, -31080005, -105406183, 80596196, 136204114], ![-322966612, -65291950, -221434105, 169314006, 286133782], ![-678483222, -137164191, -465189738, 355700168, 601099162], ![-551256690, -111443602, -377955956, 288995425, 488386212], ![-220161256, -44508513, -150950253, 115422256, 195050635]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [7, 21, 44, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [57, 61, 69], [57, 17, 10], [0, 1]]
 g := ![![[37, 26, 19], [19, 19, 40], [33, 11, 38], [19, 2, 45], [35, 1], []], ![[53, 51, 70, 57], [2, 55, 59, 59], [11, 14, 4, 41], [47, 73, 32, 69], [4, 52], [68, 21]], ![[65, 62, 58, 25], [16, 30, 30, 45], [47, 78, 12, 36], [16, 74, 0, 50], [58, 8], [48, 21]]]
 h' := ![![[57, 61, 69], [25, 57, 63], [6, 13, 35], [25, 46, 14], [71, 48, 19], [0, 0, 1], [0, 1]], ![[57, 17, 10], [65, 47, 27], [0, 11, 70], [73, 60, 15], [36, 59, 1], [8, 7, 17], [57, 61, 69]], ![[0, 1], [37, 54, 68], [2, 55, 53], [58, 52, 50], [10, 51, 59], [69, 72, 61], [57, 17, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46, 53], []]
 b := ![[], [11, 1, 29], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [7, 21, 44, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-23586971, 8741858, 13617488, -3368564, -30074390]
  a := ![-10, 11, 55, -47, -119]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![25350839, 4557142, 11995220, -3368564, -30074390]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 493039 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7872635, 139137, -1499, 2582062, -1167230]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![-7872635, 139137, -1499, 2582062, -1167230]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![57, 32, 1, 0, 0], ![36, 70, 0, 1, 0], ![30, 73, 0, 0, 1]] where
  M :=![![![-7872635, 139137, -1499, 2582062, -1167230], ![247602, -11623426, -18854925, 15241772, 36820894], ![88883560, 2971799, 7388624, -35142778, -1203206], ![-18898396, 70917591, 114536887, -86886001, -226259100], ![8042448, -32687861, -52812485, 40282918, 104227323]]]
  hmulB := by decide  
  f := ![![![-168005315, -115663685, -19370627, -80596196, -136204114]], ![![-353004424, -242983860, -40698851, -169314006, -286133782]], ![![-273595267, -188339704, -31544179, -131237108, -221784996]], ![![-396974026, -273259643, -45768639, -190410619, -321786064]], ![![-393039884, -270549367, -45314966, -188521906, -318594179]]]
  g := ![![![-831956, -1206955, -1499, 2582062, -1167230], ![-7320915, -40039432, -18854925, 15241772, 36820894], ![12265420, 29295751, 7388624, -35142778, -1203206], ![42635039, 240565463, 114536887, -86886001, -226259100], ![-19729755, -111026420, -52812485, 40282918, 104227323]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P1 : CertificateIrreducibleZModOfList' 79 2 2 6 [55, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [62, 78], [0, 1]]
 g := ![![[75, 23], [62, 21], [4, 23], [0, 22], [52], [1]], ![[0, 56], [21, 58], [8, 56], [21, 57], [52], [1]]]
 h' := ![![[62, 78], [66, 55], [17, 10], [0, 24], [7, 38], [24, 62], [0, 1]], ![[0, 1], [0, 24], [5, 69], [66, 55], [72, 41], [76, 17], [62, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32]]
 b := ![[], [57, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N1 : CertifiedPrimeIdeal' SI79N1 79 where
  n := 2
  hpos := by decide
  P := [55, 17, 1]
  hirr := P79P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![37769, 5036, 9780, -19906, -13752]
  a := ![6, -16, -32, 10, 72]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![7715, 26448, 9780, -19906, -13752]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N1 B_one_repr
lemma NI79N1 : Nat.card (O ⧸ I79N1) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![168005315, 115663685, 19370627, 80596196, 136204114]] ![![-7872635, 139137, -1499, 2582062, -1167230]]
  ![![79, 0, 0, 0, 0]] where
 M := ![![![-79, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0)
instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![32071, -2868, -3728, -7484, 12040]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![32071, -2868, -3728, -7484, 12040]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![50, 80, 1, 1, 0], ![47, 82, 54, 0, 1]] where
  M :=![![![32071, -2868, -3728, -7484, 12040], ![16596, 47867, 78156, -68956, -150008], ![-368972, 13700, 11579, 111548, -77432], ![-29956, -297120, -483020, 402359, 937872], ![16548, 136756, 222400, -186164, -431421]]]
  hmulB := by decide  
  f := ![![![130517, 90092, 15056, 62660, 105832]], ![![274324, 188745, 31628, 131748, 222760]], ![![577268, 396964, 66537, 276476, 467176]], ![![355630, 244868, 41007, 170771, 288664]], ![![722757, 497302, 83322, 346600, 585779]]]
  g := ![![![-1923, -4716, -7788, -7484, 12040], ![126684, 215241, 99368, -68956, -150008], ![-27796, -30852, 49173, 111548, -77432], ![-773830, -1317968, -620849, 402359, 937872], ![356645, 607306, 285606, -186164, -431421]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [47, 65, 35, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [81, 72, 26], [50, 10, 57], [0, 1]]
 g := ![![[23, 7, 26], [70, 75, 61], [52, 3], [74, 12], [81, 48, 1], []], ![[52, 63, 19, 68], [27, 7, 7, 28], [56, 33], [9, 81], [18, 64, 51, 27], [4, 12]], ![[16, 9, 43, 47], [39, 37, 59, 72], [52, 28], [58, 63], [17, 34, 52, 8], [56, 12]]]
 h' := ![![[81, 72, 26], [30, 75, 62], [4, 16, 12], [46, 61, 70], [11, 32, 57], [0, 0, 1], [0, 1]], ![[50, 10, 57], [9, 34, 80], [5, 9, 38], [75, 7, 45], [0, 8, 74], [65, 50, 10], [81, 72, 26]], ![[0, 1], [78, 57, 24], [50, 58, 33], [81, 15, 51], [63, 43, 35], [34, 33, 72], [50, 10, 57]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 10], []]
 b := ![[], [52, 53, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [47, 65, 35, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10530713, 3078805, 3930052, 874554, -8646311]
  a := ![6, 7, -26, 44, 59]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![4242388, 7736289, 5662124, 874554, -8646311]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 571787 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, -11, 1, 0, 4]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![13, -11, 1, 0, 4]] 
 ![![83, 0, 0, 0, 0], ![34, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![47, 0, 0, 1, 0], ![33, 0, 0, 0, 1]] where
  M :=![![![13, -11, 1, 0, 4], ![8, 18, 1, -6, -20], ![-46, -5, -6, 12, 28], ![30, -27, 3, -1, 12], ![-34, 15, -3, 4, 1]]]
  hmulB := by decide  
  f := ![![![433, 299, 53, 202, 340]], ![![188, 130, 23, 88, 148]], ![![54, 37, 6, 26, 44]], ![![265, 182, 32, 123, 208]], ![![179, 124, 22, 84, 141]]]
  g := ![![![3, -11, 1, 0, 4], ![4, 18, 1, -6, -20], ![-16, -5, -6, 12, 28], ![7, -27, 3, -1, 12], ![-9, 15, -3, 4, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1

def I83N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3945375, -2716001, -454883, -1892458, -3198132]] i)))

def SI83N2: IdealEqSpanCertificate' Table ![![-3945375, -2716001, -454883, -1892458, -3198132]] 
 ![![83, 0, 0, 0, 0], ![47, 1, 0, 0, 0], ![32, 0, 1, 0, 0], ![13, 0, 0, 1, 0], ![19, 0, 0, 0, 1]] where
  M :=![![![-3945375, -2716001, -454883, -1892458, -3198132], ![-8288722, -5705932, -955649, -3975792, -6718836], ![-17413464, -11987415, -2007688, -8352586, -14115324], ![-14147256, -9738979, -1631111, -6785933, -11467788], ![-5650780, -3889979, -651507, -2710458, -4580497]]]
  hmulB := by decide  
  f := ![![![68413, 3097, 7001, -28116, -3492]], ![![38317, 2959, 5908, -17362, -5832]], ![![17226, 301, 986, -6448, 636]], ![![15105, -6754, -10524, 3601, 22776]], ![![13707, 4050, 6968, -10156, -11557]]]
  g := ![![![2694330, -2716001, -454883, -1892458, -3198132], ![5660410, -5705932, -955649, -3975792, -6718836], ![11891757, -11987415, -2007688, -8352586, -14115324], ![9661270, -9738979, -1631111, -6785933, -11467788], ![3858938, -3889979, -651507, -2710458, -4580497]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N2 : Nat.card (O ⧸ I83N2) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N2)

lemma isPrimeI83N2 : Ideal.IsPrime I83N2 := prime_ideal_of_norm_prime hp83.out _ NI83N2
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![32071, -2868, -3728, -7484, 12040]] ![![13, -11, 1, 0, 4]]
  ![![-68413, -3097, -7001, 28116, 3492]] where
 M := ![![![-68413, -3097, -7001, 28116, 3492]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI83N1 : IdealMulLeCertificate' Table 
  ![![-68413, -3097, -7001, 28116, 3492]] ![![-3945375, -2716001, -454883, -1892458, -3198132]]
  ![![83, 0, 0, 0, 0]] where
 M := ![![![-83, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC83 : ContainsPrimesAboveP 83 ![I83N0, I83N1, I83N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N1
    exact isPrimeI83N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 83 (by decide) (𝕀 ⊙ MulI83N0 ⊙ MulI83N1)
instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 27, 21, 170, 362]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![199, 27, 21, 170, 362]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![0, 0, 0, 89, 0], ![48, 49, 48, 58, 1]] where
  M :=![![![199, 27, 21, 170, 362], ![894, 412, 93, 168, 230], ![628, 1049, 94, 566, 866], ![702, 305, 79, 559, 1116], ![312, 541, 45, 110, 51]]]
  hmulB := by decide  
  f := ![![![-3, 7, 11, -8, -22]], ![![-52, -6, -11, 26, 14]], ![![54, -75, -120, 80, 242]], ![![308, 51, 91, -175, -132]], ![![198, -7, -6, -60, 41]]]
  g := ![![![-193, -199, -195, -234, 362], ![-114, -122, -123, -148, 230], ![-460, -465, -466, -558, 866], ![-594, -611, -601, -721, 1116], ![-24, -22, -27, -32, 51]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 4 2 6 [62, 84, 49, 50, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [64, 51, 78, 70], [8, 78, 59, 37], [56, 48, 41, 71], [0, 1]]
 g := ![![[65, 51, 32, 85], [51, 84, 4], [2, 86, 55], [21, 85, 63, 79], [39, 1], []], ![[20, 18, 32, 30, 78, 29], [4, 22, 69], [20, 38, 45], [24, 25, 48, 41, 13, 60], [68, 57, 71, 59, 84, 19], [40, 79, 5]], ![[9, 44, 74, 85, 4, 29], [40, 45, 9], [83, 42, 36], [7, 65, 41, 12, 70, 41], [77, 66, 87, 85, 79, 75], [44, 85, 34]], ![[64, 71, 46, 13, 0, 42], [23, 74, 79], [1, 70, 20], [40, 62, 32, 84, 55, 4], [13, 82, 17, 52, 82, 32], [38, 35, 57]]]
 h' := ![![[64, 51, 78, 70], [60, 6, 4, 68], [75, 74, 71, 2], [33, 44, 44, 12], [74, 44, 52, 48], [0, 0, 1], [0, 1]], ![[8, 78, 59, 37], [8, 21, 36, 53], [16, 51, 59, 43], [59, 55, 58, 32], [51, 15, 11, 22], [14, 50, 30, 34], [64, 51, 78, 70]], ![[56, 48, 41, 71], [59, 18, 68, 39], [15, 81, 38, 3], [55, 53, 69, 83], [53, 77, 44, 65], [6, 25, 74, 41], [8, 78, 59, 37]], ![[0, 1], [38, 44, 70, 18], [29, 61, 10, 41], [64, 26, 7, 51], [38, 42, 71, 43], [68, 14, 73, 14], [56, 48, 41, 71]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [84, 74, 28], []]
 b := ![[], [], [50, 88, 57, 69], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 4
  hpos := by decide
  P := [62, 84, 49, 50, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-53342984, 60007788, 95841842, -60426690, -194873316]
  a := ![2, -7, -11, 4, 25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![104500856, 107964048, 106177090, 126317142, -194873316]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 62742241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, -7, -11, 8, 22]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![3, -7, -11, 8, 22]] 
 ![![89, 0, 0, 0, 0], ![21, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![81, 0, 0, 1, 0], ![36, 0, 0, 0, 1]] where
  M :=![![![3, -7, -11, 8, 22], ![52, 6, 11, -26, -14], ![-54, 75, 120, -80, -242], ![-308, -51, -91, 175, 132], ![142, 23, 41, -80, -59]]]
  hmulB := by decide  
  f := ![![![-199, -27, -21, -170, -362]], ![![-57, -11, -6, -42, -88]], ![![-16, -13, -2, -14, -26]], ![![-189, -28, -20, -161, -342]], ![![-84, -17, -9, -70, -147]]]
  g := ![![![-14, -7, -11, 8, 22], ![28, 6, 11, -26, -14], ![147, 75, 120, -80, -242], ![-200, -51, -91, 175, 132], ![91, 23, 41, -80, -59]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![199, 27, 21, 170, 362]] ![![3, -7, -11, 8, 22]]
  ![![89, 0, 0, 0, 0]] where
 M := ![![![-89, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0)
instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![119, 42, 78, -108, -140]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![119, 42, 78, -108, -140]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![41, 16, 1, 0, 0], ![60, 87, 0, 1, 0], ![54, 87, 0, 0, 1]] where
  M :=![![![119, 42, 78, -108, -140], ![-388, 165, 270, -104, -596], ![-1296, -610, -999, 1212, 1732], ![2532, -970, -1478, 351, 3240], ![-1176, 438, 686, -180, -1521]]]
  hmulB := by decide  
  f := ![![![6623, -762, 538, -1180, -2212]], ![![-5604, 6129, -318, -400, -3100]], ![![1807, 600, 167, -528, -1336]], ![![-772, 4993, 60, -1113, -4188]], ![![-1458, 5061, 4, -988, -3949]]]
  g := ![![![113, 210, 78, -108, -140], ![278, 585, 270, -104, -596], ![-1305, -2482, -999, 1212, 1732], ![-1370, -2987, -1478, 351, 3240], ![656, 1417, 686, -180, -1521]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [77, 80, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 96], [0, 1]]
 g := ![![[93, 73], [64], [44], [9], [33], [17, 1]], ![[73, 24], [64], [44], [9], [33], [34, 96]]]
 h' := ![![[17, 96], [16, 49], [71, 89], [89, 23], [54, 94], [49, 18], [0, 1]], ![[0, 1], [73, 48], [32, 8], [92, 74], [3, 3], [64, 79], [17, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [87]]
 b := ![[], [91, 92]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [77, 80, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![29179, -15575, -27834, 15329, 61557]
  a := ![10, -11, -50, 45, 117]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-31685, -64529, -27834, 15329, 61557]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![423435, 291492, 48820, 203106, 343236]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![423435, 291492, 48820, 203106, 343236]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![33, 50, 1, 0, 0], ![48, 28, 0, 1, 0], ![57, 38, 0, 0, 1]] where
  M :=![![![423435, 291492, 48820, 203106, 343236], ![889578, 612385, 102564, 426698, 721092], ![1868882, 1286536, 215473, 896434, 1514916], ![1518344, 1045226, 175058, 728293, 1230768], ![606462, 417488, 69922, 290898, 491599]]]
  hmulB := by decide  
  f := ![![![299, -16, 24, -70, -84]], ![![-238, 309, 152, -134, -420]], ![![-31, 150, 85, -88, -240]], ![![88, 74, 46, -67, -144]], ![![77, 114, 78, -96, -221]]]
  g := ![![![-314445, -215252, 48820, 203106, 343236], ![-660606, -452215, 102564, 426698, 721092], ![-1387843, -950042, 215473, 896434, 1514916], ![-1127530, -771846, 175058, 728293, 1230768], ![-450363, -308294, 69922, 290898, 491599]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P1 : CertificateIrreducibleZModOfList' 97 2 2 6 [15, 76, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [21, 96], [0, 1]]
 g := ![![[18, 54], [43], [72], [33], [86], [21, 1]], ![[85, 43], [43], [72], [33], [86], [42, 96]]]
 h' := ![![[21, 96], [25, 32], [66, 25], [51, 13], [62, 79], [73, 38], [0, 1]], ![[0, 1], [18, 65], [9, 72], [33, 84], [72, 18], [95, 59], [21, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56]]
 b := ![[], [94, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N1 : CertifiedPrimeIdeal' SI97N1 97 where
  n := 2
  hpos := by decide
  P := [15, 76, 1]
  hirr := P97P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7157, -7684, -14508, 10408, 30511]
  a := ![6, -5, -33, 30, 71]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-18070, -7558, -14508, 10408, 30511]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N1 B_one_repr
lemma NI97N1 : Nat.card (O ⧸ I97N1) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N1

def I97N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7427, -2541, -3909, 742, 8730]] i)))

def SI97N2: IdealEqSpanCertificate' Table ![![7427, -2541, -3909, 742, 8730]] 
 ![![97, 0, 0, 0, 0], ![31, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![39, 0, 0, 1, 0], ![68, 0, 0, 0, 1]] where
  M :=![![![7427, -2541, -3909, 742, 8730], ![18202, 11506, 19197, -21568, -34746], ![-91060, 24221, 36676, 46, -85086], ![-94164, -75511, -125255, 132661, 230364], ![44052, 34601, 57421, -61106, -105475]]]
  hmulB := by decide  
  f := ![![![669693, 462975, 77261, 320704, 541026]], ![![228487, 157933, 26360, 109462, 184692]], ![![92679, 63904, 10687, 44364, 74892]], ![![294025, 203232, 33920, 140803, 237546]], ![![479382, 331329, 55303, 229572, 387317]]]
  g := ![![![-5167, -2541, -3909, 742, 8730], ![27759, 11506, 19197, -21568, -34746], ![47547, 24221, 36676, 46, -85086], ![-180047, -75511, -125255, 132661, 230364], ![82578, 34601, 57421, -61106, -105475]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N2 : Nat.card (O ⧸ I97N2) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N2)

lemma isPrimeI97N2 : Ideal.IsPrime I97N2 := prime_ideal_of_norm_prime hp97.out _ NI97N2
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![119, 42, 78, -108, -140]] ![![423435, 291492, 48820, 203106, 343236]]
  ![![-15361995, -10575202, -1771182, -7368582, -12452408]] where
 M := ![![![-15361995, -10575202, -1771182, -7368582, -12452408]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI97N1 : IdealMulLeCertificate' Table 
  ![![-15361995, -10575202, -1771182, -7368582, -12452408]] ![![7427, -2541, -3909, 742, 8730]]
  ![![97, 0, 0, 0, 0]] where
 M := ![![![2147483, -17945, 33271, -731380, 253946]]]
 hmul := by decide  
 g := ![![![![22139, -185, 343, -7540, 2618]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![115, -1106, -1790, 1418, 3508]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![115, -1106, -1790, 1418, 3508]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![0, 0, 0, 101, 0], ![93, 26, 85, 41, 1]] where
  M :=![![![115, -1106, -1790, 1418, 3508], ![8434, 415, 910, -3506, -524], ![-4554, 12326, 19879, -14662, -39452], ![-51000, -4940, -9484, 24429, 10920], ![23522, 2182, 4220, -11142, -4733]]]
  hmulB := by decide  
  f := ![![![1895, 1294, 218, 898, 1516]], ![![3930, 2731, 454, 1894, 3196]], ![![8286, 5686, 955, 3986, 6748]], ![![6776, 4636, 780, 3225, 5448]], ![![12507, 8580, 1441, 5991, 10131]]]
  g := ![![![-3229, -914, -2970, -1410, 3508], ![566, 139, 450, 178, -524], ![36282, 10278, 33399, 15870, -39452], ![-10560, -2860, -9284, -4191, 10920], ![4591, 1240, 4025, 1811, -4733]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 4 2 6 [78, 24, 70, 95, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [40, 47, 8, 42], [87, 47, 78, 78], [81, 6, 15, 82], [0, 1]]
 g := ![![[72, 65, 22, 85], [54, 39, 58], [12, 46, 44, 87], [68, 2, 47], [67, 6, 1], []], ![[81, 46, 3, 81, 76, 53], [44, 92, 25], [8, 72, 82, 47, 73, 57], [95, 51, 65], [49, 19, 87], [94, 21, 19, 96, 44, 55]], ![[98, 97, 15, 25, 15, 64], [43, 74, 9], [10, 26, 23, 19, 50, 64], [44, 93, 80], [49, 4, 33], [13, 80, 23, 56, 82, 54]], ![[13, 23, 57, 95, 27, 43], [18, 34, 20], [66, 14, 92, 72, 100, 78], [86, 41, 37], [2, 60, 5], [54, 3, 16, 38, 38, 9]]]
 h' := ![![[40, 47, 8, 42], [52, 14, 4, 40], [74, 84, 53, 19], [18, 47, 20, 84], [26, 45, 37, 59], [0, 0, 0, 1], [0, 1]], ![[87, 47, 78, 78], [81, 89, 51, 24], [68, 4, 26, 96], [47, 7, 60, 15], [65, 21, 71, 41], [7, 11, 95, 84], [40, 47, 8, 42]], ![[81, 6, 15, 82], [59, 41, 98, 62], [22, 89, 64, 98], [84, 4, 25, 62], [53, 67, 44, 22], [80, 76, 73, 72], [87, 47, 78, 78]], ![[0, 1], [90, 58, 49, 76], [79, 25, 59, 90], [28, 43, 97, 41], [26, 69, 50, 80], [9, 14, 34, 45], [81, 6, 15, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [64, 83, 98], []]
 b := ![[], [], [3, 77, 66, 35], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 4
  hpos := by decide
  P := [78, 24, 70, 95, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-382443656, 53419937, 68789211, 75274352, -185271132]
  a := ![3, 2, -15, 21, 32]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![166809620, 48222469, 156602331, 75954364, -185271132]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 104060401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1895, -1294, -218, -898, -1516]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![-1895, -1294, -218, -898, -1516]] 
 ![![101, 0, 0, 0, 0], ![18, 1, 0, 0, 0], ![80, 0, 1, 0, 0], ![79, 0, 0, 1, 0], ![8, 0, 0, 0, 1]] where
  M :=![![![-1895, -1294, -218, -898, -1516], ![-3930, -2731, -454, -1894, -3196], ![-8286, -5686, -955, -3986, -6748], ![-6776, -4636, -780, -3225, -5448], ![-2666, -1846, -308, -1298, -2199]]]
  hmulB := by decide  
  f := ![![![-115, 1106, 1790, -1418, -3508]], ![![-104, 193, 310, -218, -620]], ![![-46, 754, 1221, -978, -2388]], ![![415, 914, 1494, -1351, -2852]], ![![-242, 66, 100, -2, -231]]]
  g := ![![![1207, -1294, -218, -898, -1516], ![2542, -2731, -454, -1894, -3196], ![5340, -5686, -955, -3986, -6748], ![4331, -4636, -780, -3225, -5448], ![1736, -1846, -308, -1298, -2199]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![115, -1106, -1790, 1418, 3508]] ![![-1895, -1294, -218, -898, -1516]]
  ![![101, 0, 0, 0, 0]] where
 M := ![![![-101, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1235, 1263, -73, -112, -704]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![-1235, 1263, -73, -112, -704]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![0, 0, 0, 103, 0], ![97, 44, 26, 54, 1]] where
  M :=![![![-1235, 1263, -73, -112, -704], ![-1520, -1900, -177, 702, 2176], ![5054, -223, 416, -1196, -2456], ![-2294, 3055, -119, -469, -2124], ![3066, -1987, 207, -196, 313]]]
  hmulB := by decide  
  f := ![![![29, 21, 35, -38, -64]], ![![-166, 38, 57, 8, -136]], ![![-264, -253, -418, 426, 776]], ![![1072, -185, -269, -133, 684]], ![![447, -124, -188, 6, 433]]]
  g := ![![![651, 313, 177, 368, -704], ![-2064, -948, -551, -1134, 2176], ![2362, 1047, 624, 1276, -2456], ![1978, 937, 535, 1109, -2124], ![-265, -153, -77, -166, 313]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 4 2 6 [40, 36, 39, 77, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [80, 21, 32, 1], [43, 21, 81, 86], [6, 60, 93, 16], [0, 1]]
 g := ![![[101, 44, 20, 2], [83, 22, 79, 4], [36, 17, 34, 79], [5, 27, 33], [19, 26, 1], []], ![[81, 27, 34, 46, 7, 18], [58, 3, 18, 68, 101, 100], [50, 67, 0, 67, 12, 55], [92, 3, 49], [5, 46, 32], [89, 28, 29, 88, 19, 1]], ![[87, 29, 85, 57, 81, 27], [47, 2, 5, 65, 26, 94], [58, 2, 18, 39, 94, 43], [98, 21, 100], [12, 80, 2], [22, 97, 28, 4, 66, 31]], ![[100, 71, 36, 71, 14, 23], [89, 4, 46, 61, 25, 98], [63, 34, 43, 33, 77, 14], [91, 63, 61], [14, 88, 83], [7, 66, 16, 94, 39, 79]]]
 h' := ![![[80, 21, 32, 1], [79, 50, 5, 38], [2, 99, 71, 2], [85, 33, 19, 39], [64, 27, 34, 62], [0, 0, 0, 1], [0, 1]], ![[43, 21, 81, 86], [23, 62, 5, 92], [53, 1, 12, 93], [28, 70, 32, 63], [0, 69, 49, 7], [32, 60, 90, 54], [80, 21, 32, 1]], ![[6, 60, 93, 16], [80, 52, 99, 33], [97, 65, 74, 96], [24, 32, 19, 84], [37, 1, 41, 10], [38, 60, 43, 65], [43, 21, 81, 86]], ![[0, 1], [17, 42, 97, 43], [95, 41, 49, 15], [91, 71, 33, 20], [34, 6, 82, 24], [39, 86, 73, 86], [6, 60, 93, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [20, 66, 28], []]
 b := ![[], [], [94, 53, 27, 38], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 4
  hpos := by decide
  P := [40, 36, 39, 77, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![95270057210, 12946664123, 23719539723, -50456117529, -32081083211]
  a := ![-16, 25, 79, -71, -199]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![31137234259, 13830236169, 8328424303, 16329343455, -32081083211]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 112550881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 21, 35, -38, -64]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![29, 21, 35, -38, -64]] 
 ![![103, 0, 0, 0, 0], ![78, 1, 0, 0, 0], ![96, 0, 1, 0, 0], ![28, 0, 0, 1, 0], ![24, 0, 0, 0, 1]] where
  M :=![![![29, 21, 35, -38, -64], ![-166, 38, 57, 8, -136], ![-264, -253, -418, 426, 776], ![1072, -185, -269, -133, 684], ![-492, 87, 127, 58, -321]]]
  hmulB := by decide  
  f := ![![![-1235, 1263, -73, -112, -704]], ![![-950, 938, -57, -78, -512]], ![![-1102, 1175, -64, -116, -680]], ![![-358, 373, -21, -35, -212]], ![![-258, 275, -15, -28, -161]]]
  g := ![![![-23, 21, 35, -38, -64], ![-54, 38, 57, 8, -136], ![282, -253, -418, 426, 776], ![278, -185, -269, -133, 684], ![-130, 87, 127, 58, -321]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![-1235, 1263, -73, -112, -704]] ![![29, 21, 35, -38, -64]]
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


lemma PB405I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB405I2 : PrimesBelowBoundCertificateInterval O 61 103 405 where
  m := 9
  g := ![2, 1, 3, 2, 3, 2, 3, 2, 2]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB405I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0, I67N1]
    · exact ![I71N0]
    · exact ![I73N0, I73N1, I73N2]
    · exact ![I79N0, I79N1]
    · exact ![I83N0, I83N1, I83N2]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1, I97N2]
    · exact ![I101N0, I101N1]
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
    · exact ![300763, 4489]
    · exact ![1804229351]
    · exact ![389017, 73, 73]
    · exact ![493039, 6241]
    · exact ![571787, 83, 83]
    · exact ![62742241, 89]
    · exact ![9409, 9409, 97]
    · exact ![104060401, 101]
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
      exact NI73N2
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
      exact NI83N2
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
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
      exact NI103N1
  β := ![I73N1, I73N2, I83N1, I83N2, I89N1, I97N2, I101N1, I103N1]
  Il := ![[], [], [I73N1, I73N2], [], [I83N1, I83N2], [I89N1], [I97N2], [I101N1], [I103N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
