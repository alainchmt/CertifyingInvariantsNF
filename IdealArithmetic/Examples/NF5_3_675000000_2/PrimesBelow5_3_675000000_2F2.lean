
import IdealArithmetic.Examples.NF5_3_675000000_2.RI5_3_675000000_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-22237, 1633, -2653, 21270, 28561]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![-22237, 1633, -2653, 21270, 28561]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![42, 55, 1, 0, 0], ![37, 64, 0, 1, 0], ![39, 55, 0, 0, 1]] where
  M :=![![![-22237, 1633, -2653, 21270, 28561], ![-143408, 14329, -12346, 115672, 140996], ![-665280, 51530, -76019, 621220, 824080], ![-339072, 32828, -30510, 279449, 345334], ![-115566, 7004, -15648, 118938, 165303]]]
  hmulB := by decide  
  f := ![![![17039, -5661, -211, 2396, -2069]], ![![26136, 16311, -12522, 3336, 37028]], ![![27914, 9899, -9715, 3676, 27486]], ![![35245, 12041, -12027, 4633, 33919]], ![![30509, 10328, -10367, 4014, 29216]]]
  g := ![![![-27040, -41561, -2653, 21270, 28561], ![-140352, -215887, -12346, 115672, 140996], ![-785026, -1206715, -76019, 621220, 824080], ![-341273, -524884, -30510, 279449, 345334], ![-153819, -236359, -15648, 118938, 165303]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [25, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [59, 66], [0, 1]]
 g := ![![[3, 59], [53, 15], [36], [15], [64], [1]], ![[0, 8], [0, 52], [36], [15], [64], [1]]]
 h' := ![![[59, 66], [15, 27], [25, 45], [56, 61], [30, 22], [42, 59], [0, 1]], ![[0, 1], [0, 40], [0, 22], [37, 6], [55, 45], [39, 8], [59, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [30, 41]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [25, 8, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-12644, -852, -2913, 20262, 32658]
  a := ![-25, -8, 9, -28, -75]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-28562, -43785, -2913, 20262, 32658]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17585, 5410, 2332, -5022, -8787]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![17585, 5410, 2332, -5022, -8787]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![29, 57, 1, 0, 0], ![29, 47, 0, 1, 0], ![55, 2, 0, 0, 1]] where
  M :=![![![17585, 5410, 2332, -5022, -8787], ![50208, 15436, 6667, -14342, -25116], ![143560, 44085, 19004, -40930, -71640], ![15836, 4883, 2097, -4525, -7902], ![12362, 3788, 1638, -3522, -6175]]]
  hmulB := by decide  
  f := ![![![12173, -1078, 1222, -10604, -13545]], ![![65944, -5866, 6585, -57286, -73068]], ![![66675, -5927, 6663, -57944, -73923]], ![![53907, -4793, 5386, -46843, -59757]], ![![12979, -1150, 1302, -11302, -14434]]]
  g := ![![![8640, 1882, 2332, -5022, -8787], ![24689, 5369, 6667, -14342, -25116], ![70442, 15341, 19004, -40930, -71640], ![7774, 1699, 2097, -4525, -7902], ![6069, 1318, 1638, -3522, -6175]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P1 : CertificateIrreducibleZModOfList' 67 2 2 6 [31, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [44, 66], [0, 1]]
 g := ![![[31, 59], [48, 36], [54], [39], [60], [1]], ![[14, 8], [24, 31], [54], [39], [60], [1]]]
 h' := ![![[44, 66], [53, 27], [61, 61], [44, 11], [39, 46], [36, 44], [0, 1]], ![[0, 1], [35, 40], [65, 6], [59, 56], [53, 21], [29, 23], [44, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [37, 44]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N1 : CertifiedPrimeIdeal' SI67N1 67 where
  n := 2
  hpos := by decide
  P := [31, 23, 1]
  hirr := P67P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-312255, -97770, -141556, 890930, 1546770]
  a := ![-169, -58, 56, -170, -510]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1598753, -552184, -141556, 890930, 1546770]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N1 B_one_repr
lemma NI67N1 : Nat.card (O ⧸ I67N1) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1249, -157, -139, 170, 256]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![1249, -157, -139, 170, 256]] 
 ![![67, 0, 0, 0, 0], ![22, 1, 0, 0, 0], ![52, 0, 1, 0, 0], ![22, 0, 0, 1, 0], ![60, 0, 0, 0, 1]] where
  M :=![![![1249, -157, -139, 170, 256], ![-1368, 980, -241, -198, 1016], ![-8920, -1755, 2392, -1170, -6440], ![5368, -947, -465, 735, 664], ![-3776, 364, 474, -512, -951]]]
  hmulB := by decide  
  f := ![![![9859, 2209, 977, -2426, -3296]], ![![3486, 860, 377, -894, -1320]], ![![9164, 1909, 850, -2186, -2776]], ![![3166, 803, 351, -821, -1240]], ![![9132, 1954, 868, -2204, -2871]]]
  g := ![![![-107, -157, -139, 170, 256], ![-1000, 980, -241, -198, 1016], ![4738, -1755, 2392, -1170, -6440], ![-84, -947, -465, 735, 664], ![476, 364, 474, -512, -951]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![-22237, 1633, -2653, 21270, 28561]] ![![17585, 5410, 2332, -5022, -8787]]
  ![![-9859, -2209, -977, 2426, 3296]] where
 M := ![![![-9859, -2209, -977, 2426, 3296]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![-9859, -2209, -977, 2426, 3296]] ![![1249, -157, -139, 170, 256]]
  ![![67, 0, 0, 0, 0]] where
 M := ![![![-67, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1, I67N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
    exact isPrimeI67N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0 ⊙ MulI67N1)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19053687, 5852085, 2524503, -5436836, -9510372]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![19053687, 5852085, 2524503, -5436836, -9510372]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![21, 3, 25, 1, 0], ![41, 2, 33, 0, 1]] where
  M :=![![![19053687, 5852085, 2524503, -5436836, -9510372], ![54335632, 16728994, 7215385, -15523058, -27200544], ![155512120, 47688955, 20574566, -44339470, -77474520], ![17076012, 5292599, 2281645, -4894597, -8617284], ![13460808, 4086878, 1764472, -3818888, -6625325]]]
  hmulB := by decide  
  f := ![![![686137, 272571, -250957, 88028, 716148]], ![![-5377072, 235528, 812663, -725162, -1808256]], ![![11565400, -3847175, -122404, 1609470, -1468920]], ![![4111551, -1250101, -100733, 570423, -333600]], ![![5599927, -1636724, -169271, 775934, -348641]]]
  g := ![![![7368345, 580047, 6370249, -5436836, -9510372], ![21063974, 1657736, 18209997, -15523058, -27200544], ![60043610, 4727555, 51911556, -44339470, -77474520], ![6664383, 524098, 5760802, -4894597, -8617284], ![5145011, 405552, 4448907, -3818888, -6625325]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [23, 24, 59, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [57, 48, 70], [26, 22, 1], [0, 1]]
 g := ![![[50, 68, 12], [24, 51, 18], [2, 54, 10], [38, 58], [12, 1], []], ![[61, 54, 49, 44], [27, 40, 50, 51], [14, 63, 24, 53], [18, 38], [0, 58], [58, 1]], ![[16, 57, 17, 4], [31, 26, 6, 1], [38, 6, 4, 37], [28, 40], [63, 32], [56, 1]]]
 h' := ![![[57, 48, 70], [16, 12, 56], [25, 48, 36], [42, 20, 9], [8, 44, 49], [0, 0, 1], [0, 1]], ![[26, 22, 1], [20, 0, 13], [62, 37, 34], [28, 56, 36], [4, 46, 40], [69, 10, 22], [57, 48, 70]], ![[0, 1], [65, 59, 2], [44, 57, 1], [24, 66, 26], [61, 52, 53], [27, 61, 48], [26, 22, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [70, 49], []]
 b := ![[], [49, 10, 49], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [23, 24, 59, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1885653, -103270, 296090, -2095322, -2978726]
  a := ![-14, -5, 5, -16, -43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2366411, 170988, 2126438, -2095322, -2978726]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 357911 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![686137, 272571, -250957, 88028, 716148]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![686137, 272571, -250957, 88028, 716148]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![41, 34, 1, 0, 0], ![31, 31, 0, 1, 0], ![27, 64, 0, 0, 1]] where
  M :=![![![686137, 272571, -250957, 88028, 716148], ![-5377072, 235528, 812663, -725162, -1808256], ![11565400, -3847175, -122404, 1609470, -1468920], ![4507460, 991629, -1259835, 590181, 3423060], ![-1440856, -897096, 685002, -180020, -2024707]]]
  hmulB := by decide  
  f := ![![![19053687, 5852085, 2524503, -5436836, -9510372]], ![![54335632, 16728994, 7215385, -15523058, -27200544]], ![![39213025, 12062116, 5202849, -11197658, -19608708]], ![![32283731, 9933888, 4284763, -9220441, -16150080]], ![![56413955, 17362659, 7488883, -16113932, -28228735]]]
  g := ![![![-156190, -559961, -250957, 88028, 716148], ![459249, 1560752, 812663, -725162, -1808256], ![89454, 625801, -122404, 1609470, -1468920], ![-768416, -2725992, -1259835, 590181, 3423060], ![432701, 1563024, 685002, -180020, -2024707]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P1 : CertificateIrreducibleZModOfList' 71 2 2 6 [57, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [61, 70], [0, 1]]
 g := ![![[50, 5], [2, 57], [28, 20], [4], [29], [1]], ![[0, 66], [0, 14], [41, 51], [4], [29], [1]]]
 h' := ![![[61, 70], [28, 17], [37, 25], [5, 37], [34, 69], [14, 61], [0, 1]], ![[0, 1], [0, 54], [0, 46], [61, 34], [54, 2], [43, 10], [61, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [50, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N1 : CertifiedPrimeIdeal' SI71N1 71 where
  n := 2
  hpos := by decide
  P := [57, 10, 1]
  hirr := P71P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-74311, -27806, -38188, 233127, 414024]
  a := ![90, 27, -31, 89, 269]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-238228, -457097, -38188, 233127, 414024]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N1 B_one_repr
lemma NI71N1 : Nat.card (O ⧸ I71N1) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![19053687, 5852085, 2524503, -5436836, -9510372]] ![![686137, 272571, -250957, 88028, 716148]]
  ![![71, 0, 0, 0, 0]] where
 M := ![![![71, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0)
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0, 0, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0, 0, 0]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![0, 0, 0, 73, 0], ![0, 0, 0, 0, 73]] where
  M :=![![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![0, 0, 0, 73, 0], ![0, 0, 0, 0, 73]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 5 2 6 [71, 51, 29, 28, 43, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 26, 71, 43, 29], [70, 55, 34, 67, 10], [12, 25, 72, 55, 68], [65, 39, 42, 54, 39], [0, 1]]
 g := ![![[51, 20, 68, 37, 27], [8, 68, 53, 24], [16, 57, 58, 54], [35, 33, 69, 30, 1], [], []], ![[7, 40, 5, 62, 36, 1, 48, 60], [6, 6, 28, 3], [25, 66, 41, 16], [49, 9, 14, 67, 23, 30, 51, 26], [7, 70, 6, 67], [1, 43, 57, 38]], ![[47, 0, 42, 45, 42, 63, 49, 34], [29, 59, 8, 36], [71, 57, 14, 24], [66, 51, 0, 16, 47, 62, 61, 11], [57, 3, 6, 23], [37, 1, 33, 27]], ![[14, 54, 68, 71, 57, 53, 56, 34], [33, 50, 2, 67], [3, 65, 47, 65], [12, 13, 25, 29, 29, 49, 31, 34], [17, 72, 29, 48], [56, 13, 54, 25]], ![[25, 14, 56, 67, 65, 33, 14, 66], [64, 40, 24, 41], [55, 53, 31, 46], [13, 36, 72, 37, 72, 63], [67, 43, 46, 12], [18, 32, 56, 61]]]
 h' := ![![[29, 26, 71, 43, 29], [18, 23, 23, 38, 10], [41, 49, 54, 12, 30], [70, 33, 68, 6, 28], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[70, 55, 34, 67, 10], [31, 29, 30, 48, 49], [47, 71, 11, 71, 52], [56, 33, 19, 9, 4], [8, 72, 30, 36, 69], [40, 10, 58, 36, 33], [29, 26, 71, 43, 29]], ![[12, 25, 72, 55, 68], [52, 66, 16, 57, 23], [33, 36, 21, 8, 6], [57, 33, 57, 58, 43], [68, 30, 0, 21, 60], [10, 48, 11, 60, 60], [70, 55, 34, 67, 10]], ![[65, 39, 42, 54, 39], [17, 49, 25, 63, 16], [30, 71, 49, 47, 33], [30, 4, 35, 29, 49], [16, 40, 3, 70, 16], [37, 33, 28, 52, 11], [12, 25, 72, 55, 68]], ![[0, 1], [39, 52, 52, 13, 48], [35, 65, 11, 8, 25], [61, 43, 40, 44, 22], [60, 4, 40, 19], [27, 55, 48, 71, 42], [65, 39, 42, 54, 39]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36, 12, 38, 54], [], [], []]
 b := ![[], [0, 8, 67, 62, 51], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 5
  hpos := by decide
  P := [71, 51, 29, 28, 43, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6931501689839, 22403077967, 1488968343917, -9626290407678, -14910818067604]
  a := ![-37, -7, 14, -32, -110]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![94952077943, 306891479, 20396826629, -131866991886, -204257781748]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 2073071593 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def PBC73 : ContainsPrimesAboveP 73 ![I73N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![73, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 73 (by decide) 𝕀

instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![108463, 33342, 14380, -30960, -54189]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![108463, 33342, 14380, -30960, -54189]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![41, 63, 73, 1, 0], ![60, 58, 10, 0, 1]] where
  M :=![![![108463, 33342, 14380, -30960, -54189], ![309672, 95214, 41073, -88418, -154764], ![884440, 271855, 117286, -252470, -441960], ![97744, 30037, 12947, -27885, -48798], ![76102, 23398, 10100, -21734, -38053]]]
  hmulB := by decide  
  f := ![![![-353, 38, -26, 266, 309]], ![![-1408, 92, -185, 1422, 1956]], ![![-9960, 1045, -796, 7750, 9240]], ![![-10555, 1062, -902, 8477, 10317]], ![![-2590, 232, -258, 2246, 2861]]]
  g := ![![![58597, 64896, 35650, -30960, -54189], ![167350, 185340, 101813, -88418, -154764], ![477890, 529255, 290724, -252470, -441960], ![52771, 58444, 32108, -27885, -48798], ![41144, 45566, 25028, -21734, -38053]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [37, 28, 12, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 25, 46], [30, 53, 33], [0, 1]]
 g := ![![[78, 39, 62], [74, 69, 11], [47, 48, 72], [65, 10, 26], [67, 1], []], ![[38, 33, 12, 73], [3, 9, 56, 45], [46, 50, 33, 55], [34, 28, 20, 76], [19, 44], [55, 62]], ![[72, 42, 54, 58], [69, 37, 6, 27], [6, 53, 37, 54], [65, 61, 3, 34], [60, 72], [68, 62]]]
 h' := ![![[37, 25, 46], [27, 37, 33], [78, 29, 13], [44, 53, 25], [49, 62, 37], [0, 0, 1], [0, 1]], ![[30, 53, 33], [37, 75, 54], [77, 55, 48], [49, 73, 50], [58, 32, 73], [45, 70, 53], [37, 25, 46]], ![[0, 1], [28, 46, 71], [6, 74, 18], [23, 32, 4], [24, 64, 48], [43, 9, 25], [30, 53, 33]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 19], []]
 b := ![[], [36, 39, 70], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [37, 28, 12, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![24593765, -5895104, -2709712, 1368304, 18672864]
  a := ![28, -2, -10, 10, 84]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-14580741, -14874992, -3662336, 1368304, 18672864]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 493039 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-145, 41, 5, -20, 7]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![-145, 41, 5, -20, 7]] 
 ![![79, 0, 0, 0, 0], ![28, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![64, 0, 0, 1, 0], ![39, 0, 0, 0, 1]] where
  M :=![![![-145, 41, 5, -20, 7], ![-136, -133, 88, -16, -268], ![2080, 20, -369, 280, 880], ![-524, 206, -10, -73, 118], ![478, -112, -28, 66, 15]]]
  hmulB := by decide  
  f := ![![![1935, -533, -197, -18, 1273]], ![![556, -161, -60, 0, 384]], ![![710, -182, -67, -12, 442]], ![![1352, -382, -142, -5, 914]], ![![1205, -323, -119, -16, 774]]]
  g := ![![![-4, 41, 5, -20, 7], ![184, -133, 88, -16, -268], ![-614, 20, -369, 280, 880], ![-78, 206, -10, -73, 118], ![-13, -112, -28, 66, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1

def I79N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139251, -12357, 13941, -121134, -154619]] i)))

def SI79N2: IdealEqSpanCertificate' Table ![![139251, -12357, 13941, -121134, -154619]] 
 ![![79, 0, 0, 0, 0], ![32, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![46, 0, 0, 0, 1]] where
  M :=![![![139251, -12357, 13941, -121134, -154619], ![752416, -66797, 75292, -654364, -835132], ![4063600, -360620, 406799, -3534800, -4511840], ![1819344, -161506, 182068, -1582307, -2019458], ![780570, -69256, 78160, -679078, -866841]]]
  hmulB := by decide  
  f := ![![![-3349, -1743, 1987, -936, -5885]], ![![-808, -709, 732, -324, -2228]], ![![-1153, 329, 118, -232, -185]], ![![-638, -228, 270, -127, -776]], ![![-1824, -924, 1096, -534, -3245]]]
  g := ![![![105470, -12357, 13941, -121134, -154619], ![569700, -66797, 75292, -654364, -835132], ![3077677, -360620, 406799, -3534800, -4511840], ![1377598, -161506, 182068, -1582307, -2019458], ![591284, -69256, 78160, -679078, -866841]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N2 : Nat.card (O ⧸ I79N2) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N2)

lemma isPrimeI79N2 : Ideal.IsPrime I79N2 := prime_ideal_of_norm_prime hp79.out _ NI79N2
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![108463, 33342, 14380, -30960, -54189]] ![![-145, 41, 5, -20, 7]]
  ![![-30549, -8495, -2917, 7274, 11870]] where
 M := ![![![-30549, -8495, -2917, 7274, 11870]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI79N1 : IdealMulLeCertificate' Table 
  ![![-30549, -8495, -2917, 7274, 11870]] ![![139251, -12357, 13941, -121134, -154619]]
  ![![79, 0, 0, 0, 0]] where
 M := ![![![237, -316, 0, -632, -711]]]
 hmul := by decide  
 g := ![![![![3, -4, 0, -8, -9]]]]
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

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5644015, -500949, 564915, -4909120, -6265712]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![5644015, -500949, 564915, -4909120, -6265712]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![0, 0, 0, 83, 0], ![53, 5, 49, 4, 1]] where
  M :=![![![5644015, -500949, 564915, -4909120, -6265712], ![30489216, -2706242, 3051579, -26518754, -33846592], ![164697720, -14618235, 16484674, -143252410, -182838680], ![73725372, -6543879, 7379001, -64124649, -81844124], ![31640256, -2808276, 3166950, -27520652, -35125893]]]
  hmulB := by decide  
  f := ![![![-4987, -1503, -633, 1384, 2408]], ![![-13728, -4360, -1863, 4022, 6976]], ![![-39720, -12045, -5428, 11410, 20360]], ![![-4860, -1329, -519, 1197, 2060]], ![![-27733, -8410, -3752, 7932, 14099]]]
  g := ![![![4068997, 371417, 3705841, 242816, -6265712], ![21980224, 2006346, 20018489, 1311658, -33846592], ![118736720, 10838255, 108139518, 7085570, -182838680], ![53150168, 4851527, 48406519, 3171709, -81844124], ![22810995, 2082183, 20775129, 1361240, -35125893]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 4 2 6 [18, 4, 70, 64, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 6, 52, 68], [82, 68, 11, 1], [5, 8, 20, 14], [0, 1]]
 g := ![![[13, 41, 26, 33], [78, 1, 23, 12], [16, 71, 33], [46, 61, 21], [19, 1], []], ![[71, 80, 17, 61, 45, 21], [51, 77, 34, 23, 27, 11], [15, 15, 64], [26, 28, 12], [42, 32, 55, 53, 16, 10], [13, 59, 59]], ![[35, 51, 52, 46, 7, 4], [34, 0, 4, 55, 66, 23], [16, 59, 37], [78, 22, 70], [15, 75, 63, 62, 12, 21], [53, 41, 1]], ![[40, 21, 58, 48, 59, 15], [54, 76, 46, 57, 46, 6], [81, 0, 81], [76, 30, 33], [54, 55, 76, 48, 82, 56], [74, 51, 30]]]
 h' := ![![[15, 6, 52, 68], [7, 19, 74, 38], [73, 51, 63, 57], [19, 17, 51, 45], [73, 72, 77, 42], [0, 0, 1], [0, 1]], ![[82, 68, 11, 1], [48, 23, 54, 27], [74, 57, 0, 72], [57, 58, 18, 75], [44, 17, 60, 26], [74, 62, 52, 39], [15, 6, 52, 68]], ![[5, 8, 20, 14], [19, 2, 34, 2], [38, 43, 41, 43], [34, 77, 53, 55], [39, 9, 55, 53], [43, 76, 46, 42], [82, 68, 11, 1]], ![[0, 1], [71, 39, 4, 16], [62, 15, 62, 77], [21, 14, 44, 74], [71, 68, 57, 45], [21, 28, 67, 2], [5, 8, 20, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [6, 17, 60], []]
 b := ![[], [], [24, 29, 40, 23], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 4
  hpos := by decide
  P := [18, 4, 70, 64, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-370243368, 33877826, -36889693, 322718165, 411704810]
  a := ![10, 7, -2, 13, 17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-267356606, -24393328, -243499101, -15953025, 411704810]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 47458321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4987, -1503, -633, 1384, 2408]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-4987, -1503, -633, 1384, 2408]] 
 ![![83, 0, 0, 0, 0], ![39, 1, 0, 0, 0], ![56, 0, 1, 0, 0], ![36, 0, 0, 1, 0], ![78, 0, 0, 0, 1]] where
  M :=![![![-4987, -1503, -633, 1384, 2408], ![-13728, -4360, -1863, 4022, 6976], ![-39720, -12045, -5428, 11410, 20360], ![-4860, -1329, -519, 1197, 2060], ![-3168, -1050, -504, 1016, 1833]]]
  hmulB := by decide  
  f := ![![![5644015, -500949, 564915, -4909120, -6265712]], ![![3019347, -267991, 302208, -2626198, -3351920]], ![![5792320, -514113, 579758, -5038110, -6430344]], ![![3336264, -296121, 333927, -2901843, -3703732]], ![![5685222, -504606, 569040, -4944964, -6311463]]]
  g := ![![![-1790, -1503, -633, 1384, 2408], ![-5160, -4360, -1863, 4022, 6976], ![-15239, -12045, -5428, 11410, 20360], ![-1539, -1329, -519, 1197, 2060], ![-1368, -1050, -504, 1016, 1833]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![5644015, -500949, 564915, -4909120, -6265712]] ![![-4987, -1503, -633, 1384, 2408]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, -5, -7, 6, 10]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![59, -5, -7, 6, 10]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![70, 9, 67, 1, 0], ![44, 3, 57, 0, 1]] where
  M :=![![![59, -5, -7, 6, 10], ![-56, 40, -7, -26, 32], ![-360, -85, 124, -110, -440], ![336, -49, -27, 5, 28], ![-204, 20, 30, -36, -93]]]
  hmulB := by decide  
  f := ![![![595, 183, 79, -170, -298]], ![![1704, 522, 225, -486, -848]], ![![4840, 1495, 646, -1390, -2440]], ![![4290, 1324, 572, -1231, -2160]], ![![3456, 1067, 461, -992, -1741]]]
  g := ![![![-9, -1, -11, 6, 10], ![4, 2, -1, -26, 32], ![300, 25, 366, -110, -440], ![-14, -2, -22, 5, 28], ![72, 7, 87, -36, -93]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [46, 38, 29, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [68, 42, 74], [81, 46, 15], [0, 1]]
 g := ![![[14, 86, 67], [49, 87], [11, 42], [77, 44, 5], [2, 60, 1], []], ![[42, 6, 70, 6], [40, 67], [43, 71], [56, 28, 87, 35], [54, 83, 80, 33], [47, 47]], ![[43, 51, 52, 54], [40, 16], [26, 49], [85, 60, 8, 15], [39, 65, 40, 27], [17, 47]]]
 h' := ![![[68, 42, 74], [76, 18, 44], [85, 88, 49], [18, 43, 65], [86, 12, 19], [0, 0, 1], [0, 1]], ![[81, 46, 15], [69, 52, 63], [60, 64, 44], [13, 54, 31], [65, 22, 71], [59, 73, 46], [68, 42, 74]], ![[0, 1], [24, 19, 71], [66, 26, 85], [85, 81, 82], [54, 55, 88], [83, 16, 42], [81, 46, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [74, 77], []]
 b := ![[], [1, 46, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [46, 38, 29, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![22164, -5520, -2070, 444, 14628]
  a := ![2, -1, -1, 1, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7332, -600, -9726, 444, 14628]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 704969 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![595, 183, 79, -170, -298]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![595, 183, 79, -170, -298]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![52, 42, 1, 0, 0], ![13, 34, 0, 1, 0], ![65, 41, 0, 0, 1]] where
  M :=![![![595, 183, 79, -170, -298], ![1704, 522, 225, -486, -848], ![4840, 1495, 646, -1390, -2440], ![544, 163, 71, -155, -268], ![412, 130, 56, -120, -213]]]
  hmulB := by decide  
  f := ![![![59, -5, -7, 6, 10]], ![![-56, 40, -7, -26, 32]], ![![4, 15, -6, -10, 16]], ![![-9, 14, -4, -9, 14]], ![![15, 15, -8, -8, 21]]]
  g := ![![![203, 167, 79, -170, -298], ![578, 476, 225, -486, -848], ![1662, 1367, 646, -1390, -2440], ![183, 151, 71, -155, -268], ![145, 119, 56, -120, -213]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P1 : CertificateIrreducibleZModOfList' 89 2 2 6 [15, 25, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [64, 88], [0, 1]]
 g := ![![[61, 9], [44], [17], [0, 8], [77, 2], [1]], ![[14, 80], [44], [17], [67, 81], [27, 87], [1]]]
 h' := ![![[64, 88], [18, 3], [12, 20], [0, 62], [2, 50], [74, 64], [0, 1]], ![[0, 1], [32, 86], [46, 69], [52, 27], [87, 39], [76, 25], [64, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [86]]
 b := ![[], [48, 43]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N1 : CertifiedPrimeIdeal' SI89N1 89 where
  n := 2
  hpos := by decide
  P := [15, 25, 1]
  hirr := P89P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-18549, -8969, -12825, 73990, 134730]
  a := ![51, 13, -17, 50, 150]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-101921, -84381, -12825, 73990, 134730]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N1 B_one_repr
lemma NI89N1 : Nat.card (O ⧸ I89N1) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![59, -5, -7, 6, 10]] ![![595, 183, 79, -170, -298]]
  ![![89, 0, 0, 0, 0]] where
 M := ![![![89, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0, 0, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0, 0, 0]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![0, 0, 0, 97, 0], ![0, 0, 0, 0, 97]] where
  M :=![![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![0, 0, 0, 97, 0], ![0, 0, 0, 0, 97]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 5 2 6 [25, 15, 61, 18, 81, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [85, 36, 60, 72, 70], [58, 6, 54, 50, 38], [61, 93, 80, 74, 88], [6, 58, 0, 95, 95], [0, 1]]
 g := ![![[16, 85, 67, 69, 32], [46, 16, 75, 96], [12, 76, 22, 62], [88, 89, 70, 93], [16, 1], []], ![[63, 26, 54, 46, 35, 29, 43, 95], [68, 51, 49, 53], [49, 14, 58, 75], [45, 78, 70, 64], [84, 8, 94, 70], [31, 32, 93, 73, 1, 92, 64, 8]], ![[93, 11, 44, 50, 84, 32, 37, 67], [67, 38, 67, 72], [21, 20, 64, 8], [18, 69, 45, 22], [82, 12, 68, 1], [22, 19, 93, 0, 13, 0, 4, 67]], ![[36, 87, 11, 28, 43, 80, 87, 32], [70, 39, 7, 27], [96, 22, 86, 9], [6, 25, 18, 50], [23, 88, 71, 86], [43, 38, 79, 92, 30, 57, 13, 47]], ![[18, 66, 58, 66, 88, 3, 38, 62], [38, 14, 65, 93], [63, 51, 1, 54], [94, 25, 95, 27], [34, 21, 66, 32], [92, 73, 95, 44, 94, 16, 42, 89]]]
 h' := ![![[85, 36, 60, 72, 70], [49, 9, 46, 36, 41], [61, 75, 28, 66, 22], [78, 2, 2, 0, 16], [85, 26, 76, 39, 44], [0, 0, 0, 1], [0, 1]], ![[58, 6, 54, 50, 38], [58, 77, 89, 56, 91], [20, 69, 90, 86, 76], [88, 76, 63, 25, 47], [7, 89, 72, 96, 89], [19, 28, 79, 27, 78], [85, 36, 60, 72, 70]], ![[61, 93, 80, 74, 88], [96, 76, 74, 0, 59], [92, 20, 59, 59, 13], [36, 83, 80, 15, 69], [96, 28, 81, 12, 64], [77, 92, 6, 26, 1], [58, 6, 54, 50, 38]], ![[6, 58, 0, 95, 95], [66, 21, 32, 14, 42], [78, 84, 78, 1, 30], [76, 43, 40, 42, 94], [56, 57, 53, 43, 27], [90, 22, 49, 21, 59], [61, 93, 80, 74, 88]], ![[0, 1], [47, 11, 50, 88, 58], [30, 43, 36, 79, 53], [76, 87, 9, 15, 65], [1, 91, 9, 4, 67], [50, 52, 60, 22, 56], [6, 58, 0, 95, 95]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [95, 36, 84, 40], [], [], []]
 b := ![[], [20, 50, 3, 60, 41], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 5
  hpos := by decide
  P := [25, 15, 61, 18, 81, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1105106172483, 6061748929, -225499544387, 1480251180844, 2270070802563]
  a := ![24, 5, -9, 21, 71]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-11392847139, 62492257, -2324737571, 15260321452, 23402791779]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 8587340257 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def PBC97 : ContainsPrimesAboveP 97 ![I97N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![97, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 97 (by decide) 𝕀

instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-36885, -11357, -4933, 10576, 18558]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![-36885, -11357, -4933, 10576, 18558]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![0, 0, 0, 101, 0], ![94, 60, 46, 5, 1]] where
  M :=![![![-36885, -11357, -4933, 10576, 18558], ![-106160, -32416, -13951, 30090, 52680], ![-301080, -93145, -39916, 86210, 150360], ![-32724, -10201, -4545, 9595, 16968], ![-26244, -8044, -3366, 7376, 12767]]]
  hmulB := by decide  
  f := ![![![-1217, 107, -123, 1064, 1362]], ![![-6640, 594, -659, 5750, 7320]], ![![-35560, 3135, -3586, 31050, 39720]], ![![-16036, 1431, -1595, 13903, 17712]], ![![-22134, 1957, -2225, 19295, 24659]]]
  g := ![![![-17637, -11137, -8501, -814, 18558], ![-50080, -31616, -24131, -2310, 52680], ![-142920, -90245, -68876, -6590, 150360], ![-16116, -10181, -7773, -745, 16968], ![-12142, -7664, -5848, -559, 12767]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 4 2 6 [79, 49, 6, 99, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [35, 56, 35, 46], [60, 57, 73, 46], [8, 88, 94, 9], [0, 1]]
 g := ![![[98, 29, 72, 19], [16, 24, 19], [31, 39, 60, 31], [88, 4, 84], [99, 2, 1], []], ![[60, 90, 71, 10, 36, 8], [30, 56, 4], [56, 15, 53, 65, 88, 26], [18, 7, 9], [41, 65, 96], [56, 44, 66, 61, 25, 73]], ![[22, 81, 20, 38, 97, 28], [55, 92, 97], [35, 10, 31, 86, 28, 18], [79, 63, 1], [30, 44, 13], [53, 50, 59, 62, 61, 73]], ![[35, 18, 70, 57, 44, 14], [49, 99, 9], [71, 9, 85, 2, 83, 19], [26, 3, 85], [81, 90, 37], [75, 13, 68, 71, 60, 22]]]
 h' := ![![[35, 56, 35, 46], [68, 42, 68, 76], [76, 91, 28, 25], [34, 46, 54, 43], [57, 41, 37, 36], [0, 0, 0, 1], [0, 1]], ![[60, 57, 73, 46], [41, 65, 76, 47], [47, 0, 89, 99], [46, 28, 95, 36], [85, 90, 15, 3], [71, 4, 42, 55], [35, 56, 35, 46]], ![[8, 88, 94, 9], [76, 41, 80, 56], [52, 69, 48, 81], [70, 84, 33, 81], [7, 32, 81, 1], [16, 23, 69, 66], [60, 57, 73, 46]], ![[0, 1], [63, 54, 79, 23], [55, 42, 37, 98], [100, 44, 20, 42], [29, 39, 69, 61], [41, 74, 91, 80], [8, 88, 94, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [93, 40, 12], []]
 b := ![[], [], [56, 43, 73, 70], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 4
  hpos := by decide
  P := [79, 49, 6, 99, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-39036563, 3422925, -3913336, 34198847, 43747654]
  a := ![6, 3, -2, 7, 14]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-41102139, -25954815, -19963420, -1827123, 43747654]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 104060401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1217, 107, -123, 1064, 1362]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![-1217, 107, -123, 1064, 1362]] 
 ![![101, 0, 0, 0, 0], ![45, 1, 0, 0, 0], ![96, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![21, 0, 0, 0, 1]] where
  M :=![![![-1217, 107, -123, 1064, 1362], ![-6640, 594, -659, 5750, 7320], ![-35560, 3135, -3586, 31050, 39720], ![-16036, 1431, -1595, 13903, 17712], ![-6796, 594, -692, 5964, 7651]]]
  hmulB := by decide  
  f := ![![![-36885, -11357, -4933, 10576, 18558]], ![![-17485, -5381, -2336, 5010, 8790]], ![![-38040, -11717, -5084, 10906, 19128]], ![![-324, -101, -45, 95, 168]], ![![-7929, -2441, -1059, 2272, 3985]]]
  g := ![![![-226, 107, -123, 1064, 1362], ![-1226, 594, -659, 5750, 7320], ![-6599, 3135, -3586, 31050, 39720], ![-2963, 1431, -1595, 13903, 17712], ![-1265, 594, -692, 5964, 7651]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![-36885, -11357, -4933, 10576, 18558]] ![![-1217, 107, -123, 1064, 1362]]
  ![![101, 0, 0, 0, 0]] where
 M := ![![![101, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0, 0, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0, 0, 0]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![0, 0, 0, 103, 0], ![0, 0, 0, 0, 103]] where
  M :=![![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![0, 0, 0, 103, 0], ![0, 0, 0, 0, 103]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 5 2 6 [56, 54, 83, 20, 72, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [64, 92, 61, 47, 47], [11, 72, 77, 67, 53], [39, 101, 46, 97, 75], [20, 43, 22, 98, 31], [0, 1]]
 g := ![![[43, 3, 76, 79, 100], [86, 53, 101, 69, 81], [4, 33, 61, 65, 49], [47, 35, 91, 93], [31, 1], []], ![[45, 26, 86, 31, 96, 79, 95, 22], [91, 95, 36, 72, 95, 25, 39, 45], [79, 31, 60, 62, 4, 56, 58, 86], [69, 5, 35, 56], [74, 55], [0, 56, 13, 59, 60, 68, 69, 102]], ![[11, 20, 43, 92, 84, 22, 43, 102], [12, 23, 25, 55, 96, 50, 99, 101], [10, 60, 36, 47, 67, 26, 71, 94], [75, 32, 27, 25], [3, 71, 84, 1], [13, 100, 25, 89, 78, 102, 29, 42]], ![[17, 96, 102, 54, 51, 13, 49, 11], [62, 84, 34, 87, 17, 75, 6, 27], [46, 45, 73, 14, 99, 41, 102, 10], [37, 43, 84, 41], [24, 49, 5, 83], [69, 7, 16, 91, 75, 101, 8, 90]], ![[95, 20, 71, 33, 41, 74, 10, 88], [86, 52, 61, 21, 63, 56, 49, 70], [44, 29, 31, 79, 69, 28, 82, 62], [66, 39, 28, 58], [66, 46, 42, 50], [63, 61, 76, 72, 89, 13, 28, 24]]]
 h' := ![![[64, 92, 61, 47, 47], [25, 25, 72, 91, 10], [85, 101, 38, 67, 94], [65, 46, 45, 45, 96], [15, 21, 51, 18, 14], [0, 0, 0, 1], [0, 1]], ![[11, 72, 77, 67, 53], [17, 34, 27, 75, 92], [66, 46, 45, 60, 89], [3, 49, 73, 19, 79], [57, 69, 35, 61, 46], [9, 25, 50, 63], [64, 92, 61, 47, 47]], ![[39, 101, 46, 97, 75], [32, 92, 13, 95, 58], [8, 86, 100, 51, 62], [79, 55, 33, 78, 71], [57, 96, 35, 90, 5], [88, 58, 79, 78, 1], [11, 72, 77, 67, 53]], ![[20, 43, 22, 98, 31], [74, 22, 79, 92, 92], [86, 0, 49, 89, 20], [51, 79, 46, 50, 25], [28, 1, 45, 75, 12], [41, 43, 43, 21, 86], [39, 101, 46, 97, 75]], ![[0, 1], [67, 33, 15, 59, 57], [62, 76, 77, 42, 44], [61, 80, 9, 14, 38], [7, 19, 40, 65, 26], [43, 80, 34, 43, 16], [20, 43, 22, 98, 31]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58, 96, 70, 76], [], [], []]
 b := ![[], [41, 55, 0, 13, 97], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 5
  hpos := by decide
  P := [56, 54, 83, 20, 72, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![16637390090673250, -1378185776565834, 1788640517511564, -15029031694993006, -19590405564326648]
  a := ![-115, -39, 38, -140, -352]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![161528059132750, -13380444432678, 17365441917588, -145912929077602, -190198112275016]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 11592740743 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def PBC103 : ContainsPrimesAboveP 103 ![I103N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![103, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 103 (by decide) 𝕀



lemma PB1271I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB1271I2 : PrimesBelowBoundCertificateInterval O 61 103 1271 where
  m := 9
  g := ![3, 2, 1, 3, 2, 2, 1, 2, 1]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB1271I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0, I67N1, I67N2]
    · exact ![I71N0, I71N1]
    · exact ![I73N0]
    · exact ![I79N0, I79N1, I79N2]
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0]
    · exact ![I101N0, I101N1]
    · exact ![I103N0]
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
    · exact ![4489, 4489, 67]
    · exact ![357911, 5041]
    · exact ![2073071593]
    · exact ![493039, 79, 79]
    · exact ![47458321, 83]
    · exact ![704969, 7921]
    · exact ![8587340257]
    · exact ![104060401, 101]
    · exact ![11592740743]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
      exact NI67N2
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
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
      exact NI89N1
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
  β := ![I67N2, I79N1, I79N2, I83N1, I101N1]
  Il := ![[I67N2], [], [], [I79N1, I79N2], [I83N1], [], [], [I101N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
