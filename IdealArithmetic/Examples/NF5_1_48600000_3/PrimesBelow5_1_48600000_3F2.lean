
import IdealArithmetic.Examples.NF5_1_48600000_3.RI5_1_48600000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![115, 357, 351, 24, 102]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![115, 357, 351, 24, 102]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![0, 0, 67, 0, 0], ![26, 30, 18, 1, 0], ![18, 26, 13, 0, 1]] where
  M :=![![![115, 357, 351, 24, 102], ![204, 625, 606, 42, 174], ![348, 1074, 1057, 84, 300], ![126, 387, 387, 31, 126], ![168, 510, 474, 6, 157]]]
  hmulB := by decide  
  f := ![![![349, 399, -315, 66, -120]], ![![-240, -251, 204, -42, 78]], ![![156, 150, -125, 24, -48]], ![![68, 81, -63, 13, -24]], ![![30, 38, -29, 6, -11]]]
  g := ![![![-35, -45, -21, 24, 102], ![-60, -77, -36, 42, 174], ![-108, -138, -65, 84, 300], ![-44, -57, -27, 31, 126], ![-42, -56, -25, 6, 157]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [31, 59, 22, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 58, 35], [11, 8, 32], [0, 1]]
 g := ![![[27, 44, 17], [0, 35, 26], [], [12, 60], [45, 1], []], ![[51, 15, 33, 37], [7, 55, 43, 47], [54, 26], [35, 6], [2, 64], [24, 19]], ![[33, 65, 13, 63], [52, 31, 58, 18], [44, 26], [66, 9], [22, 14], [27, 19]]]
 h' := ![![[34, 58, 35], [0, 51, 33], [59, 53, 19], [40, 35], [12, 61, 23], [0, 0, 1], [0, 1]], ![[11, 8, 32], [54, 12, 39], [41, 50, 64], [24, 20, 19], [38, 29, 41], [10, 63, 8], [34, 58, 35]], ![[0, 1], [48, 4, 62], [36, 31, 51], [23, 12, 48], [27, 44, 3], [21, 4, 58], [11, 8, 32]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64, 32], []]
 b := ![[], [54, 53, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [31, 59, 22, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1715565, -2698060, 3929394, 11386392, -13097392]
  a := ![0, -1, -4, 5, -19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-925503, -56084, -459098, 11386392, -13097392]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 300763 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 7, 16, 0, 5]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![-1, 7, 16, 0, 5]] 
 ![![67, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![18, 0, 1, 0, 0], ![62, 0, 0, 1, 0], ![53, 0, 0, 0, 1]] where
  M :=![![![-1, 7, 16, 0, 5], ![10, 24, 18, 2, 5], ![10, 35, 37, 2, 11], ![6, 15, 12, 1, 3], ![6, 17, 16, 2, 4]]]
  hmulB := by decide  
  f := ![![![117, 137, -106, 20, -41]], ![![11, 13, -10, 2, -4]], ![![32, 37, -29, 6, -11]], ![![108, 127, -98, 17, -37]], ![![93, 110, -84, 14, -33]]]
  g := ![![![-9, 7, 16, 0, 5], ![-13, 24, 18, 2, 5], ![-24, 35, 37, 2, 11], ![-8, 15, 12, 1, 3], ![-11, 17, 16, 2, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![129, 52, -65, 10, -25]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![129, 52, -65, 10, -25]] 
 ![![67, 0, 0, 0, 0], ![25, 1, 0, 0, 0], ![45, 0, 1, 0, 0], ![18, 0, 0, 1, 0], ![63, 0, 0, 0, 1]] where
  M :=![![![129, 52, -65, 10, -25], ![-50, 4, 12, 0, 5], ![10, -25, 11, -6, 5], ![0, 30, -15, 5, -9], ![-6, 5, -2, 8, -4]]]
  hmulB := by decide  
  f := ![![![-7721, -23752, -23173, -1644, -6701]], ![![-3081, -9478, -9247, -656, -2674]], ![![-5533, -17021, -16606, -1178, -4802]], ![![-2202, -6774, -6609, -469, -1911]], ![![-7419, -22823, -22267, -1580, -6439]]]
  g := ![![![47, 52, -65, 10, -25], ![-15, 4, 12, 0, 5], ![-1, -25, 11, -6, 5], ![6, 30, -15, 5, -9], ![1, 5, -2, 8, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![115, 357, 351, 24, 102]] ![![-1, 7, 16, 0, 5]]
  ![![7721, 23752, 23173, 1644, 6701]] where
 M := ![![![7721, 23752, 23173, 1644, 6701]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![7721, 23752, 23173, 1644, 6701]] ![![129, 52, -65, 10, -25]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![203719439, 626664009, 611411838, 43362672, 176805113]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![203719439, 626664009, 611411838, 43362672, 176805113]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![17, 48, 54, 1, 0], ![62, 61, 43, 0, 1]] where
  M :=![![![203719439, 626664009, 611411838, 43362672, 176805113], ![353610226, 1087745004, 1061270734, 75267654, 306893129], ![613786258, 1888075871, 1842122609, 130647386, 532696091], ![225802962, 694595421, 677689890, 48063257, 195971079], ![281182694, 864949733, 843898004, 59851102, 244034336]]]
  hmulB := by decide  
  f := ![![![-2463, -2121, 1852, -356, 695]], ![![1390, 1012, -964, 246, -373]], ![![-746, -475, 421, -182, 365]], ![![-207, -174, 106, -63, 188]], ![![-1404, -1266, 1043, -206, 498]]]
  g := ![![![-161906521, -172392340, -131447779, 43362672, 176805113], ![-281032590, -299233567, -228163199, 75267654, 306893129], ![-487808126, -519400848, -396038988, 130647386, 532696091], ![-179457455, -191079954, -145696935, 48063257, 195971079], ![-223470632, -237943629, -181430112, 59851102, 244034336]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [50, 30, 65, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [58, 35, 69], [19, 35, 2], [0, 1]]
 g := ![![[67, 9, 19], [30, 53, 1], [31, 65, 2], [12, 36], [6, 1], []], ![[11, 43, 50, 62], [8, 66, 68, 67], [58, 14, 21, 66], [7, 38], [10, 18], [26, 4]], ![[20, 68, 14, 3], [35, 34, 6, 29], [24, 67, 34, 6], [48, 20], [64, 18], [22, 4]]]
 h' := ![![[58, 35, 69], [62, 2, 27], [12, 59, 1], [11, 17, 12], [55, 54, 6], [0, 0, 1], [0, 1]], ![[19, 35, 2], [29, 18, 18], [31, 33, 59], [63, 67, 31], [22, 64, 31], [5, 27, 35], [58, 35, 69]], ![[0, 1], [27, 51, 26], [39, 50, 11], [57, 58, 28], [55, 24, 34], [42, 44, 35], [19, 35, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40, 65], []]
 b := ![[], [50, 58, 68], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [50, 30, 65, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-726790, -1822760, 578120, 1484640, 124200]
  a := ![3, -64, 1, -3, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-474170, -1136080, -1196240, 1484640, 124200]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 357911 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1513623, 4656075, 4542752, 322182, 1313651]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![1513623, 4656075, 4542752, 322182, 1313651]] 
 ![![71, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![46, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![67, 0, 0, 0, 1]] where
  M :=![![![1513623, 4656075, 4542752, 322182, 1313651], ![2627302, 8081878, 7885176, 559234, 2280197], ![4560394, 14028287, 13686857, 970702, 3957899], ![1677702, 5160801, 5035194, 357107, 1456053], ![2089170, 6426523, 6270110, 444690, 1813160]]]
  hmulB := by decide  
  f := ![![![-3535, -4119, 3254, -706, 1205]], ![![-215, -255, 200, -40, 72]], ![![-2316, -2699, 2127, -458, 797]], ![![-170, -189, 160, -69, 67]], ![![-3317, -3850, 3062, -680, 1107]]]
  g := ![![![-4507559, 4656075, 4542752, 322182, 1313651], ![-7824089, 8081878, 7885176, 559234, 2280197], ![-13580824, 14028287, 13686857, 970702, 3957899], ![-4996186, 5160801, 5035194, 357107, 1456053], ![-6221535, 6426523, 6270110, 444690, 1813160]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2847, 8758, 8545, 606, 2471]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![2847, 8758, 8545, 606, 2471]] 
 ![![71, 0, 0, 0, 0], ![30, 1, 0, 0, 0], ![23, 0, 1, 0, 0], ![34, 0, 0, 1, 0], ![14, 0, 0, 0, 1]] where
  M :=![![![2847, 8758, 8545, 606, 2471], ![4942, 15202, 14832, 1052, 4289], ![8578, 26387, 25745, 1826, 7445], ![3156, 9708, 9471, 671, 2739], ![3930, 12089, 11794, 836, 3410]]]
  hmulB := by decide  
  f := ![![![1229, 2686, -1799, 428, -685]], ![![500, 1104, -738, 176, -281]], ![![415, 893, -600, 142, -228]], ![![574, 1268, -847, 201, -323]], ![![236, 521, -348, 84, -134]]]
  g := ![![![-7206, 8758, 8545, 606, 2471], ![-12508, 15202, 14832, 1052, 4289], ![-21711, 26387, 25745, 1826, 7445], ![-7987, 9708, 9471, 671, 2739], ![-9946, 12089, 11794, 836, 3410]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![203719439, 626664009, 611411838, 43362672, 176805113]] ![![1513623, 4656075, 4542752, 322182, 1313651]]
  ![![5185194489601341, 15950244039564704, 15562036260550676, 1103693830085154, 4500154247640620]] where
 M := ![![![5185194489601341, 15950244039564704, 15562036260550676, 1103693830085154, 4500154247640620]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![5185194489601341, 15950244039564704, 15562036260550676, 1103693830085154, 4500154247640620]] ![![2847, 8758, 8545, 606, 2471]]
  ![![71, 0, 0, 0, 0]] where
 M := ![![![248248365719403866347, 763640018438735992510, 745054033497754268007, 52840870313100712284, 215451115614355462893]]]
 hmul := by decide  
 g := ![![![![3496455855202871357, 10755493217446985810, 10493718781658510817, 744237610043672004, 3034522755131767083]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1, I71N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
    exact isPrimeI71N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0 ⊙ MulI71N1)
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10845, -31109, -28304, -2264, -8099]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![-10845, -31109, -28304, -2264, -8099]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![0, 0, 0, 73, 0], ![8, 52, 5, 18, 1]] where
  M :=![![![-10845, -31109, -28304, -2264, -8099], ![-16198, -51340, -51314, -3486, -14891], ![-29782, -90653, -87763, -6310, -25349], ![-10458, -32937, -32652, -2251, -9465], ![-13282, -41219, -40476, -2838, -11716]]]
  hmulB := by decide  
  f := ![![![11, 23, -14, -44, 29]], ![![58, 156, -20, -114, -103]], ![![-206, -457, 239, 806, -445]], ![![-342, -987, -6, 365, 1209]], ![![-48, -144, -11, 26, 219]]]
  g := ![![![739, 5343, 167, 1966, -8099], ![1410, 9904, 317, 3624, -14891], ![2370, 16815, 534, 6164, -25349], ![894, 6291, 201, 2303, -9465], ![1102, 7781, 248, 2850, -11716]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 4 2 6 [4, 50, 3, 37, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 17, 31, 40], [42, 20, 4, 28], [47, 35, 38, 5], [0, 1]]
 g := ![![[68, 42, 48, 69], [16, 64, 48], [61, 6, 2], [56, 34, 12, 55], [1], []], ![[9, 16, 58, 32, 2, 5], [0, 67, 67], [65, 53, 72], [5, 0, 36, 26, 71, 39], [35, 66, 41], [39, 1, 67]], ![[58, 46, 11, 60, 44, 63], [26, 70, 38], [17, 13, 38], [70, 51, 40, 15, 2, 44], [11, 22, 36], [36, 51, 54]], ![[10, 0, 30, 50, 60, 21], [49], [27, 6, 24], [35, 15, 39, 64, 25, 17], [41, 70, 69], [57, 39, 25]]]
 h' := ![![[20, 17, 31, 40], [9, 39, 55, 19], [0, 65, 69, 62], [68, 0, 17, 41], [69, 23, 70, 36], [0, 0, 1], [0, 1]], ![[42, 20, 4, 28], [37, 42, 37, 8], [57, 4, 30, 40], [68, 33, 70, 46], [47, 59, 25, 18], [25, 40, 72, 48], [20, 17, 31, 40]], ![[47, 35, 38, 5], [65, 38, 57, 35], [13, 51, 40, 44], [64, 16, 66, 29], [6, 72, 35, 42], [14, 41, 52, 6], [42, 20, 4, 28]], ![[0, 1], [7, 27, 70, 11], [35, 26, 7], [17, 24, 66, 30], [9, 65, 16, 50], [10, 65, 21, 19], [47, 35, 38, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [69, 66, 44], []]
 b := ![[], [], [23, 35, 9, 61], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 4
  hpos := by decide
  P := [4, 50, 3, 37, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![125254427, 247414005, -198461310, -617643006, 527218803]
  a := ![1, -3, -2, 2, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-56061589, -372163887, -38829525, -138460020, 527218803]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 28398241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11, -23, 14, 44, -29]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-11, -23, 14, 44, -29]] 
 ![![73, 0, 0, 0, 0], ![18, 1, 0, 0, 0], ![41, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  M :=![![![-11, -23, 14, 44, -29], ![-58, -156, 20, 114, 103], ![206, 457, -239, -806, 445], ![342, 987, 6, -365, -1209], ![-578, -1243, 738, 2422, -1574]]]
  hmulB := by decide  
  f := ![![![10845, 31109, 28304, 2264, 8099]], ![![2896, 8374, 7682, 606, 2201]], ![![6499, 18714, 17099, 1358, 4896]], ![![1926, 5565, 5100, 403, 1461]], ![![1519, 4400, 4044, 318, 1159]]]
  g := ![![![-6, -23, 14, 44, -29], ![-5, -156, 20, 114, 103], ![102, 457, -239, -806, 445], ![-33, 987, 6, -365, -1209], ![-320, -1243, 738, 2422, -1574]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![-10845, -31109, -28304, -2264, -8099]] ![![-11, -23, 14, 44, -29]]
  ![![73, 0, 0, 0, 0]] where
 M := ![![![-73, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1443, 891, -895, 164, -344]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![1443, 891, -895, 164, -344]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![74, 72, 1, 0, 0], ![64, 16, 0, 1, 0], ![43, 43, 0, 0, 1]] where
  M :=![![![1443, 891, -895, 164, -344], ![-688, -277, 340, -54, 148], ![296, 52, -85, -100, -14], ![-162, 87, 33, 107, -150], ![-208, -246, 112, 322, -43]]]
  hmulB := by decide  
  f := ![![![-15361087, -47252439, -46102377, -3269682, -13331662]], ![![-26663324, -82019397, -80023154, -5675418, -23140708]], ![![-39275458, -120815746, -117875251, -8359972, -34086594]], ![![-18060114, -55554951, -54202817, -3844183, -15674108]], ![![-23142427, -71188720, -69456081, -4925978, -20084973]]]
  g := ![![![911, 981, -895, 164, -344], ![-364, -383, 340, -54, 148], ![172, 106, -85, -100, -14], ![-38, 31, 33, 107, -150], ![-345, -147, 112, 322, -43]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [47, 68, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 78], [0, 1]]
 g := ![![[67, 11], [69, 22], [27, 52], [18, 45], [42], [1]], ![[30, 68], [74, 57], [46, 27], [39, 34], [42], [1]]]
 h' := ![![[11, 78], [75, 66], [74, 41], [23, 62], [77, 60], [32, 11], [0, 1]], ![[0, 1], [11, 13], [51, 38], [73, 17], [26, 19], [74, 68], [11, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [47, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [47, 68, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3142, 7104, -4116, -15925, 16365]
  a := ![1, 19, 3, -7, 19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![7889, -1841, -4116, -15925, 16365]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![121, 232, -165, -476, 363]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![121, 232, -165, -476, 363]] 
 ![![79, 0, 0, 0, 0], ![17, 1, 0, 0, 0], ![27, 0, 1, 0, 0], ![73, 0, 0, 1, 0], ![30, 0, 0, 0, 1]] where
  M :=![![![121, 232, -165, -476, 363], ![726, 1936, -296, -1556, -1065], ![-2130, -4599, 2705, 8910, -5733], ![-4668, -13098, 567, 6539, 13365], ![5798, 11987, -8254, -26352, 19904]]]
  hmulB := by decide  
  f := ![![![-998908037, -3072753892, -2997967057, -212622426, -866937585]], ![![-236902681, -728739394, -711002827, -50425886, -205604352]], ![![-379495275, -1167370311, -1138958038, -80777412, -329358366]], ![![-937056683, -2882492146, -2812336036, -199457065, -813257706]], ![![-396784540, -1220554041, -1190847344, -84457516, -344363464]]]
  g := ![![![310, 232, -165, -476, 363], ![1536, 1936, -296, -1556, -1065], ![-6018, -4599, 2705, 8910, -5733], ![-8552, -13098, 567, 6539, 13365], ![17107, 11987, -8254, -26352, 19904]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1

def I79N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2159, 4952, -2205, -7720, 3221]] i)))

def SI79N2: IdealEqSpanCertificate' Table ![![2159, 4952, -2205, -7720, 3221]] 
 ![![79, 0, 0, 0, 0], ![19, 1, 0, 0, 0], ![34, 0, 1, 0, 0], ![55, 0, 0, 1, 0], ![57, 0, 0, 0, 1]] where
  M :=![![![2159, 4952, -2205, -7720, 3221], ![6442, 18264, -474, -8296, -19939], ![-39878, -93253, 37729, 135278, -44827], ![-24888, -85380, -24213, -30707, 202917], ![118686, 272979, -120312, -421976, 172210]]]
  hmulB := by decide  
  f := ![![![42482057757, 130679608876, 127499040519, 9042512310, 36869554801]], ![![11150610215, 34300536714, 33465707145, 2373461538, 9677451050]], ![![19903596800, 61225712279, 59735559649, 4236577242, 17274039719]], ![![30172156449, 92812961800, 90554017410, 6422290033, 26185972018]], ![![31393834569, 96570981711, 94220572101, 6682330154, 27246248539]]]
  g := ![![![2836, 4952, -2205, -7720, 3221], ![16055, 18264, -474, -8296, -19939], ![-56152, -93253, 37729, 135278, -44827], ![-94390, -85380, -24213, -30707, 202917], ![157157, 272979, -120312, -421976, 172210]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N2 : Nat.card (O ⧸ I79N2) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N2)

lemma isPrimeI79N2 : Ideal.IsPrime I79N2 := prime_ideal_of_norm_prime hp79.out _ NI79N2

def I79N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6135, -18871, -18408, -1306, -5323]] i)))

def SI79N3: IdealEqSpanCertificate' Table ![![-6135, -18871, -18408, -1306, -5323]] 
 ![![79, 0, 0, 0, 0], ![50, 1, 0, 0, 0], ![28, 0, 1, 0, 0], ![76, 0, 0, 1, 0], ![48, 0, 0, 0, 1]] where
  M :=![![![-6135, -18871, -18408, -1306, -5323], ![-10646, -32750, -31956, -2266, -9241], ![-18482, -56851, -55465, -3934, -16039], ![-6798, -20913, -20406, -1447, -5901], ![-8466, -26043, -25410, -1802, -7348]]]
  hmulB := by decide  
  f := ![![![199, 187, -126, -34, -77]], ![![124, 116, -78, -18, -51]], ![![66, 53, -43, -2, -19]], ![![202, 205, -132, -71, -59]], ![![138, 159, -84, -58, -70]]]
  g := ![![![22881, -18871, -18408, -1306, -5323], ![39714, -32750, -31956, -2266, -9241], ![68936, -56851, -55465, -3934, -16039], ![25360, -20913, -20406, -1447, -5901], ![31580, -26043, -25410, -1802, -7348]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N3 : Nat.card (O ⧸ I79N3) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N3)

lemma isPrimeI79N3 : Ideal.IsPrime I79N3 := prime_ideal_of_norm_prime hp79.out _ NI79N3
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![1443, 891, -895, 164, -344]] ![![121, 232, -165, -476, 363]]
  ![![-32245, -95743, 9558, 89770, 50813]] where
 M := ![![![-32245, -95743, 9558, 89770, 50813]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI79N1 : IdealMulLeCertificate' Table 
  ![![-32245, -95743, 9558, 89770, 50813]] ![![2159, 4952, -2205, -7720, 3221]]
  ![![2729048673, 3406679761, -7809918477, -21862231426, 28343067886]] where
 M := ![![![2729048673, 3406679761, -7809918477, -21862231426, 28343067886]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI79N2 : IdealMulLeCertificate' Table 
  ![![2729048673, 3406679761, -7809918477, -21862231426, 28343067886]] ![![-6135, -18871, -18408, -1306, -5323]]
  ![![79, 0, 0, 0, 0]] where
 M := ![![![-276541475, -635488166, 281407401, 985926004, -406486679]]]
 hmul := by decide  
 g := ![![![![-3500525, -8044154, 3562119, 12480076, -5145401]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1, I79N2, I79N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
    exact isPrimeI79N2
    exact isPrimeI79N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0 ⊙ MulI79N1 ⊙ MulI79N2)
instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![284752685, 875931429, 854612420, 60610992, 247132679]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![284752685, 875931429, 854612420, 60610992, 247132679]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![0, 0, 0, 83, 0], ![59, 62, 65, 25, 1]] where
  M :=![![![284752685, 875931429, 854612420, 60610992, 247132679], ![494265358, 1520416080, 1483411170, 105206782, 428965655], ![857931310, 2639093633, 2574861595, 182614846, 744586001], ![315620346, 970883841, 947253816, 67181323, 273922269], ![393028410, 1208999791, 1179574340, 83658006, 341103592]]]
  hmulB := by decide  
  f := ![![![-585, -69, 206, -20, 77]], ![![154, -200, 60, -10, 17]], ![![34, 239, -157, 38, -13]], ![![-30, -135, 126, -175, 57]], ![![-283, -52, 107, -45, 73]]]
  g := ![![![-172241872, -174051743, -183241105, -73707301, 247132679], ![-298972389, -302113910, -318064535, -127938971, 428965655], ![-518947503, -524400463, -552087090, -222072713, 744586001], ![-190913175, -192919239, -203104743, -81697294, 273922269], ![-237735946, -240234011, -252917580, -101734118, 341103592]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 4 2 6 [37, 28, 82, 8, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [44, 44, 44, 51], [17, 27, 30, 11], [14, 11, 9, 21], [0, 1]]
 g := ![![[19, 75, 25, 21], [42, 50, 22, 11], [11, 49, 17], [27, 32, 75], [75, 1], []], ![[53, 77, 52, 79, 57, 31], [23, 19, 28, 48, 66, 10], [52, 38, 64], [4, 6, 27], [30, 24, 37, 40, 16, 78], [62, 31, 28]], ![[76, 50, 22, 68, 0, 27], [16, 5, 20, 62, 73, 17], [78, 36, 51], [66, 33, 9], [44, 80, 81, 48, 39, 75], [12, 24, 38]], ![[66, 17, 39, 1, 26, 40], [30, 45, 10, 8, 23, 49], [75, 19, 11], [0, 9, 75], [77, 25, 80, 0, 6, 21], [39, 4, 26]]]
 h' := ![![[44, 44, 44, 51], [23, 23, 27, 42], [71, 64, 21, 54], [48, 34, 53, 73], [47, 21, 47, 65], [0, 0, 1], [0, 1]], ![[17, 27, 30, 11], [54, 66, 48, 57], [14, 12, 33, 77], [19, 80, 59, 75], [82, 42, 22, 39], [57, 76, 65, 56], [44, 44, 44, 51]], ![[14, 11, 9, 21], [33, 17, 4, 33], [44, 2, 26, 49], [78, 30, 63, 47], [14, 1, 24, 80], [11, 26, 15, 28], [17, 27, 30, 11]], ![[0, 1], [25, 60, 4, 34], [2, 5, 3, 69], [11, 22, 74, 54], [29, 19, 73, 65], [81, 64, 2, 82], [14, 11, 9, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [7, 12, 53], []]
 b := ![[], [], [19, 70, 3, 48], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 4
  hpos := by decide
  P := [37, 28, 82, 8, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6703712862, 15548298948, -6567633119, -23285118451, 8625418519]
  a := ![-1, 0, -2, 9, -20]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6050553973, -6255754810, -6833973938, -2878561222, 8625418519]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 47458321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-585, -69, 206, -20, 77]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-585, -69, 206, -20, 77]] 
 ![![83, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![34, 0, 1, 0, 0], ![30, 0, 0, 1, 0], ![33, 0, 0, 0, 1]] where
  M :=![![![-585, -69, 206, -20, 77], ![154, -200, 60, -10, 17], ![34, 239, -157, 38, -13], ![-30, -135, 126, -175, 57], ![18, -5, 62, -30, -118]]]
  hmulB := by decide  
  f := ![![![284752685, 875931429, 854612420, 60610992, 247132679]], ![![29970291, 92192001, 89948170, 6379322, 26010776]], ![![126982200, 390611593, 381104625, 27028778, 110205989]], ![![106725312, 328299117, 320308752, 22717001, 92625333]], ![![117950205, 362828156, 353997400, 25106274, 102367253]]]
  g := ![![![-109, -69, 206, -20, 77], ![-9, -200, 60, -10, 17], ![36, 239, -157, 38, -13], ![0, -135, 126, -175, 57], ![33, -5, 62, -30, -118]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![284752685, 875931429, 854612420, 60610992, 247132679]] ![![-585, -69, 206, -20, 77]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-27599041, -84897766, -82831463, -5874590, -23952801]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![-27599041, -84897766, -82831463, -5874590, -23952801]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![0, 0, 0, 89, 0], ![48, 26, 1, 38, 1]] where
  M :=![![![-27599041, -84897766, -82831463, -5874590, -23952801], ![-47905602, -147363046, -143776428, -10196940, -41576571], ![-83153142, -255788457, -249562903, -17699550, -72167391], ![-30590820, -94100820, -91810533, -6511405, -26549325], ![-38093430, -117179695, -114327698, -8108372, -33060730]]]
  hmulB := by decide  
  f := ![![![259, 206, -185, 40, -75]], ![![-150, -116, 96, 0, 45]], ![![90, 75, -65, -78, 45]], ![![0, 120, 15, -83, -117]], ![![96, 128, -65, -12, -79]]]
  g := ![![![12608263, 6043540, -661558, 10161032, -23952801], ![21885054, 10490200, -1148313, 17637222, -41576571], ![37987434, 18208581, -1993208, 30614172, -72167391], ![13975020, 6698670, -733272, 11262505, -26549325], ![17402490, 8341565, -913112, 14024712, -33060730]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 4 2 6 [38, 33, 23, 3, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 44, 41, 84], [36, 4, 86, 53], [49, 40, 51, 41], [0, 1]]
 g := ![![[7, 18, 44, 78], [27, 88, 42], [63, 4, 11], [63, 46, 6, 18], [86, 1], []], ![[12, 60, 21, 50, 74, 44], [66, 60, 22], [67, 58, 39], [38, 60, 6, 14, 7, 49], [17, 25, 84, 2], [74, 49, 25]], ![[47, 38, 44, 67, 9, 87], [28, 6, 2], [46, 83, 32], [25, 82, 72, 78, 19, 71], [35, 79, 45, 54, 42, 57], [64, 66, 50]], ![[15, 28, 1, 68, 68, 19], [58, 32, 78], [4, 13, 84], [47, 30, 79, 48, 52, 14], [78, 11, 18, 70, 45, 76], [61, 29, 79]]]
 h' := ![![[1, 44, 41, 84], [43, 8, 8, 73], [1, 30, 23, 24], [9, 2, 33, 10], [25, 61, 36, 75], [0, 0, 1], [0, 1]], ![[36, 4, 86, 53], [74, 33, 45, 86], [1, 65, 77, 17], [12, 68, 83, 67], [11, 35, 42, 50], [37, 56, 63], [1, 44, 41, 84]], ![[49, 40, 51, 41], [2, 29, 41, 70], [40, 27, 14, 64], [50, 55, 4, 78], [39, 70, 10, 32], [21, 29, 35, 76], [36, 4, 86, 53]], ![[0, 1], [39, 19, 84, 38], [75, 56, 64, 73], [82, 53, 58, 23], [46, 12, 1, 21], [83, 4, 79, 13], [49, 40, 51, 41]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [30, 58, 11], []]
 b := ![[], [], [45, 88, 88, 72], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 4
  hpos := by decide
  P := [38, 33, 23, 3, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-928289890, -2252238032, 735456014, 2804165838, -350860542]
  a := ![0, 0, -6, -6, -10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![178797934, 77192540, 12205804, 181313106, -350860542]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 62742241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![259, 206, -185, 40, -75]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![259, 206, -185, 40, -75]] 
 ![![89, 0, 0, 0, 0], ![63, 1, 0, 0, 0], ![36, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![17, 0, 0, 0, 1]] where
  M :=![![![259, 206, -185, 40, -75], ![-150, -116, 96, 0, 45], ![90, 75, -65, -78, 45], ![0, 120, 15, -83, -117], ![-78, -115, 94, 244, -200]]]
  hmulB := by decide  
  f := ![![![-27599041, -84897766, -82831463, -5874590, -23952801]], ![![-20074665, -61751936, -60248973, -4272990, -17422506]], ![![-12097962, -37214697, -36308939, -2575110, -10499643]], ![![-1894225, -5826850, -5685032, -403195, -1643970]], ![![-5699743, -17533053, -17106321, -1213218, -4946723]]]
  g := ![![![-56, 206, -185, 40, -75], ![33, -116, 96, 0, 45], ![-30, 75, -65, -78, 45], ![-64, 120, 15, -83, -117], ![67, -115, 94, 244, -200]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![-27599041, -84897766, -82831463, -5874590, -23952801]] ![![259, 206, -185, 40, -75]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![171, -124, 18, -14, 4]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![171, -124, 18, -14, 4]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![40, 0, 1, 0, 0], ![77, 20, 0, 1, 0], ![11, 39, 0, 0, 1]] where
  M :=![![![171, -124, 18, -14, 4], ![8, 191, -110, 40, -38], ![-76, -182, 119, -72, 82], ![120, 258, -132, -19, -108], ![8, 32, -10, 128, -127]]]
  hmulB := by decide  
  f := ![![![-573301, -1763540, -1720618, -122030, -497560]], ![![-995120, -3061101, -2986598, -211816, -863650]], ![![-254220, -782010, -762977, -54112, -220634]], ![![-666825, -2051230, -2001306, -141937, -578728]], ![![-473271, -1455835, -1420402, -100738, -410745]]]
  g := ![![![5, 0, 18, -14, 4], ![18, 9, -110, 40, -38], ![-2, -20, 119, -72, 82], ![83, 50, -132, -19, -108], ![-83, 25, -10, 128, -127]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [9, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [64, 96], [0, 1]]
 g := ![![[36, 54], [91], [9], [24], [72], [64, 1]], ![[0, 43], [91], [9], [24], [72], [31, 96]]]
 h' := ![![[64, 96], [86, 32], [41, 24], [5, 3], [67, 11], [6, 13], [0, 1]], ![[0, 1], [0, 65], [25, 73], [3, 94], [92, 86], [62, 84], [64, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [37, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [9, 33, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2321, 2775, -3715, -10356, 11090]
  a := ![13, -1, -2, 7, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![8519, -2295, -3715, -10356, 11090]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-189397, -582599, -568411, -40314, -164370]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![-189397, -582599, -568411, -40314, -164370]] 
 ![![97, 0, 0, 0, 0], ![38, 1, 0, 0, 0], ![11, 0, 1, 0, 0], ![28, 0, 0, 1, 0], ![52, 0, 0, 0, 1]] where
  M :=![![![-189397, -582599, -568411, -40314, -164370], ![-328740, -1011247, -986640, -69974, -285312], ![-570624, -1755300, -1712575, -121460, -495234], ![-209922, -645747, -630033, -44683, -182190], ![-261408, -804122, -784552, -55642, -226873]]]
  hmulB := by decide  
  f := ![![![47, -139, 13, 648, -408]], ![![10, -75, 8, 266, -144]], ![![37, 55, -32, -40, 6]], ![![50, 71, 13, 167, -288]], ![![-64, -272, 110, 694, -409]]]
  g := ![![![390494, -582599, -568411, -40314, -164370], ![677806, -1011247, -986640, -69974, -285312], ![1176517, -1755300, -1712575, -121460, -495234], ![432823, -645747, -630033, -44683, -182190], ![538976, -804122, -784552, -55642, -226873]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1

def I97N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-39905, -122754, -119768, -8494, -34634]] i)))

def SI97N2: IdealEqSpanCertificate' Table ![![-39905, -122754, -119768, -8494, -34634]] 
 ![![97, 0, 0, 0, 0], ![75, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![59, 0, 0, 1, 0], ![84, 0, 0, 0, 1]] where
  M :=![![![-39905, -122754, -119768, -8494, -34634], ![-69268, -213075, -207888, -14744, -60116], ![-120232, -369848, -360847, -25592, -104348], ![-44232, -136062, -132750, -9415, -38388], ![-55080, -169432, -165308, -11724, -47803]]]
  hmulB := by decide  
  f := ![![![-969, -1038, 860, -214, 302]], ![![-743, -797, 660, -162, 230]], ![![-17, -22, 13, 2, 10]], ![![-579, -612, 514, -153, 190]], ![![-828, -872, 740, -204, 245]]]
  g := ![![![130895, -122754, -119768, -8494, -34634], ![227205, -213075, -207888, -14744, -60116], ![394375, -369848, -360847, -25592, -104348], ![145085, -136062, -132750, -9415, -38388], ![180668, -169432, -165308, -11724, -47803]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N2 : Nat.card (O ⧸ I97N2) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N2)

lemma isPrimeI97N2 : Ideal.IsPrime I97N2 := prime_ideal_of_norm_prime hp97.out _ NI97N2

def I97N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-27, -75, 1, 32, 86]] i)))

def SI97N3: IdealEqSpanCertificate' Table ![![-27, -75, 1, 32, 86]] 
 ![![97, 0, 0, 0, 0], ![81, 1, 0, 0, 0], ![35, 0, 1, 0, 0], ![20, 0, 0, 1, 0], ![23, 0, 0, 0, 1]] where
  M :=![![![-27, -75, 1, 32, 86], ![172, 403, -160, -578, 182], ![364, 1082, 61, -256, -1552], ![-1734, -4239, 1317, 5101, -384], ![-1412, -4044, 32, 1646, 4717]]]
  hmulB := by decide  
  f := ![![![1278625, 3933597, 3837921, 272186, 1109836]], ![![1090601, 3355146, 3273539, 232160, 946630]], ![![501079, 1541521, 1504024, 106666, 434928]], ![![278246, 855999, 835179, 59231, 241514]], ![![321375, 988681, 964633, 68412, 278949]]]
  g := ![![![35, -75, 1, 32, 86], ![-201, 403, -160, -578, 182], ![-501, 1082, 61, -256, -1552], ![2086, -4239, 1317, 5101, -384], ![1893, -4044, 32, 1646, 4717]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N3 : Nat.card (O ⧸ I97N3) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N3)

lemma isPrimeI97N3 : Ideal.IsPrime I97N3 := prime_ideal_of_norm_prime hp97.out _ NI97N3
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![171, -124, 18, -14, 4]] ![![-189397, -582599, -568411, -40314, -164370]]
  ![![-1083, -1231, 983, -204, 374]] where
 M := ![![![-1083, -1231, 983, -204, 374]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI97N1 : IdealMulLeCertificate' Table 
  ![![-1083, -1231, 983, -204, 374]] ![![-39905, -122754, -119768, -8494, -34634]]
  ![![-1278625, -3933597, -3837921, -272186, -1109836]] where
 M := ![![![-1278625, -3933597, -3837921, -272186, -1109836]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI97N2 : IdealMulLeCertificate' Table 
  ![![-1278625, -3933597, -3837921, -272186, -1109836]] ![![-27, -75, 1, 32, 86]]
  ![![97, 0, 0, 0, 0]] where
 M := ![![![-97, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC97 : ContainsPrimesAboveP 97 ![I97N0, I97N1, I97N2, I97N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
    exact isPrimeI97N1
    exact isPrimeI97N2
    exact isPrimeI97N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 97 (by decide) (𝕀 ⊙ MulI97N0 ⊙ MulI97N1 ⊙ MulI97N2)
instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3519553, -10826448, -10562752, -749158, -3054478]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![-3519553, -10826448, -10562752, -749158, -3054478]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![12, 26, 9, 1, 0], ![37, 0, 31, 0, 1]] where
  M :=![![![-3519553, -10826448, -10562752, -749158, -3054478], ![-6108956, -18791943, -18334722, -1300320, -5301952], ![-10603904, -32618716, -31824713, -2257092, -9202912], ![-3900960, -11999874, -11707902, -830339, -3385638], ![-4857732, -14942966, -14579314, -1033992, -4215977]]]
  hmulB := by decide  
  f := ![![![-141, -288, 224, 714, -598]], ![![-1196, -3131, 534, 2608, 1544]], ![![3088, 6524, -4141, -13412, 9368]], ![![28, -44, -219, -559, 962]], ![![815, 1734, -1065, -3466, 2337]]]
  g := ![![![1173129, 85660, 899688, -749158, -3054478], ![2036308, 148677, 1561670, -1300320, -5301952], ![3534544, 258076, 2710687, -2257092, -9202912], ![1300314, 94940, 997227, -830339, -3385638], ![1619221, 118226, 1241801, -1033992, -4215977]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [46, 66, 47, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [84, 96, 81], [71, 4, 20], [0, 1]]
 g := ![![[86, 45, 9], [83, 16], [4, 10, 82], [94, 100], [48, 88], [1]], ![[71, 65, 48, 36], [44, 1], [61, 26, 42, 30], [88, 49], [19, 37], [52, 68, 37, 80]], ![[15, 90, 92, 22], [6, 9], [75, 8, 75, 88], [28, 9], [72, 70], [77, 99, 76, 21]]]
 h' := ![![[84, 96, 81], [41, 78, 3], [18, 85, 97], [100, 15, 48], [9, 68, 10], [55, 35, 54], [0, 1]], ![[71, 4, 20], [73, 2, 68], [28, 96, 1], [60, 36, 94], [13, 24, 94], [68, 13, 21], [84, 96, 81]], ![[0, 1], [49, 21, 30], [27, 21, 3], [50, 50, 60], [5, 9, 98], [61, 53, 26], [71, 4, 20]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [79, 77], []]
 b := ![[], [83, 58, 19], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [46, 66, 47, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![170086, 340710, -261078, -819734, 677028]
  a := ![-1, -3, 1, -3, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-148942, 214394, -137340, -819734, 677028]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 1030301 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![141, 288, -224, -714, 598]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![141, 288, -224, -714, 598]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![50, 84, 1, 0, 0], ![97, 91, 0, 1, 0], ![63, 70, 0, 0, 1]] where
  M :=![![![141, 288, -224, -714, 598], ![1196, 3131, -534, -2608, -1544], ![-3088, -6524, 4141, 13412, -9368], ![-7824, -21702, 1422, 12127, 20118], ![8196, 16454, -12518, -39288, 32245]]]
  hmulB := by decide  
  f := ![![![3519553, 10826448, 10562752, 749158, 3054478]], ![![6108956, 18791943, 18334722, 1300320, 5301952]], ![![6928058, 21311528, 20792861, 1474672, 6012780]], ![![8922897, 27447843, 26779748, 1899285, 7744036]], ![![6477391, 19925200, 19440230, 1378746, 5621631]]]
  g := ![![![425, 418, -224, -714, 598], ![3744, 3895, -534, -2608, -1544], ![-9118, -9100, 4141, 13412, -9368], ![-24977, -26267, 1422, 12127, 20118], ![23897, 23624, -12518, -39288, 32245]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P1 : CertificateIrreducibleZModOfList' 101 2 2 6 [78, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [87, 100], [0, 1]]
 g := ![![[96, 79], [4], [25, 87], [96], [87], [87, 1]], ![[0, 22], [4], [19, 14], [96], [87], [73, 100]]]
 h' := ![![[87, 100], [43, 68], [70, 99], [93, 17], [39, 55], [82, 17], [0, 1]], ![[0, 1], [0, 33], [98, 2], [57, 84], [77, 46], [46, 84], [87, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [75, 54]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N1 : CertifiedPrimeIdeal' SI101N1 101 where
  n := 2
  hpos := by decide
  P := [78, 14, 1]
  hirr := P101P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1759, 2878, -3044, -9639, 10319]
  a := ![3, 0, 3, -7, 16]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![4345, 4093, -3044, -9639, 10319]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N1 B_one_repr
lemma NI101N1 : Nat.card (O ⧸ I101N1) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![-3519553, -10826448, -10562752, -749158, -3054478]] ![![141, 288, -224, -714, 598]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 21, 9, -8, -2]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![7, 21, 9, -8, -2]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![44, 27, 99, 1, 0], ![78, 36, 63, 0, 1]] where
  M :=![![![7, 21, 9, -8, -2], ![-4, -3, 32, 46, -26], ![-52, -134, 55, 128, 112], ![138, 321, -123, -473, 192], ![220, 580, -80, -466, -281]]]
  hmulB := by decide  
  f := ![![![-3, 435, -233, 66, -88]], ![![-176, -443, 290, -70, 110]], ![![220, 374, -263, 60, -100]], ![![162, 426, -274, 67, -104]], ![![70, 402, -235, 62, -89]]]
  g := ![![![5, 3, 9, -8, -2], ![0, -3, -28, 46, -26], ![-140, -74, -191, 128, 112], ![58, 60, 336, -473, 192], ![414, 226, 619, -466, -281]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [58, 25, 65, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [97, 57, 74], [44, 45, 29], [0, 1]]
 g := ![![[96, 42, 52], [5, 42, 9], [25, 29, 64], [60, 19], [30, 2], [1]], ![[85, 38, 75, 77], [84, 89, 55, 53], [86, 8, 87, 22], [75, 61], [94, 30], [30, 31, 35, 22]], ![[85, 62, 53, 79], [60, 34, 47, 61], [24, 63, 2, 17], [59, 79], [97, 1], [57, 86, 17, 81]]]
 h' := ![![[97, 57, 74], [19, 78, 84], [95, 50, 100], [83, 88, 8], [79, 77, 88], [45, 78, 38], [0, 1]], ![[44, 45, 29], [60, 24, 76], [38, 43, 63], [40, 4, 74], [8, 36, 79], [1, 3, 66], [97, 57, 74]], ![[0, 1], [43, 1, 46], [33, 10, 43], [99, 11, 21], [88, 93, 39], [96, 22, 102], [44, 45, 29]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 5], []]
 b := ![[], [46, 61, 57], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [58, 25, 65, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![944561, 2039491, -1187813, -3920473, 2506115]
  a := ![1, 1, 1, -5, 11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-213899, 171574, 2223823, -3920473, 2506115]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 1092727 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![207, 140, -127, 24, -49]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![207, 140, -127, 24, -49]] 
 ![![103, 0, 0, 0, 0], ![54, 1, 0, 0, 0], ![71, 0, 1, 0, 0], ![56, 0, 0, 1, 0], ![25, 0, 0, 0, 1]] where
  M :=![![![207, 140, -127, 24, -49], ![-98, -38, 62, -8, 23], ![46, 17, 1, 2, -1], ![-24, 12, 9, 1, 3], ![-14, 5, 12, 0, 4]]]
  hmulB := by decide  
  f := ![![![37, 88, -31, -122, 31]], ![![20, 48, -16, -64, 13]], ![![19, 45, -16, -64, 18]], ![![20, 44, -23, -81, 47]], ![![29, 69, -25, -94, 23]]]
  g := ![![![15, 140, -127, 24, -49], ![-25, -38, 62, -8, 23], ![-10, 17, 1, 2, -1], ![-14, 12, 9, 1, 3], ![-12, 5, 12, 0, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1

def I103N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, -11, 8, -2, 3]] i)))

def SI103N2: IdealEqSpanCertificate' Table ![![-7, -11, 8, -2, 3]] 
 ![![103, 0, 0, 0, 0], ![58, 1, 0, 0, 0], ![35, 0, 1, 0, 0], ![49, 0, 0, 1, 0], ![81, 0, 0, 0, 1]] where
  M :=![![![-7, -11, 8, -2, 3], ![6, 8, -6, 2, -3], ![-6, -9, 5, 2, 3], ![6, 9, -6, -7, 3], ![6, 13, -4, -10, -4]]]
  hmulB := by decide  
  f := ![![![-25, -229, -326, -10, -99]], ![![-16, -134, -188, -6, -57]], ![![-11, -86, -119, -4, -36]], ![![-13, -112, -158, -5, -48]], ![![-21, -184, -260, -8, -79]]]
  g := ![![![2, -11, 8, -2, 3], ![-1, 8, -6, 2, -3], ![0, -9, 5, 2, 3], ![-2, 9, -6, -7, 3], ![2, 13, -4, -10, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N2 : Nat.card (O ⧸ I103N2) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N2)

lemma isPrimeI103N2 : Ideal.IsPrime I103N2 := prime_ideal_of_norm_prime hp103.out _ NI103N2
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![7, 21, 9, -8, -2]] ![![207, 140, -127, 24, -49]]
  ![![25, 229, 326, 10, 99]] where
 M := ![![![25, 229, 326, 10, 99]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI103N1 : IdealMulLeCertificate' Table 
  ![![25, 229, 326, 10, 99]] ![![-7, -11, 8, -2, 3]]
  ![![103, 0, 0, 0, 0]] where
 M := ![![![-103, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC103 : ContainsPrimesAboveP 103 ![I103N0, I103N1, I103N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N1
    exact isPrimeI103N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 103 (by decide) (𝕀 ⊙ MulI103N0 ⊙ MulI103N1)


lemma PB434I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB434I2 : PrimesBelowBoundCertificateInterval O 61 103 434 where
  m := 9
  g := ![3, 3, 2, 4, 2, 2, 4, 2, 3]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB434I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0, I67N1, I67N2]
    · exact ![I71N0, I71N1, I71N2]
    · exact ![I73N0, I73N1]
    · exact ![I79N0, I79N1, I79N2, I79N3]
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1, I97N2, I97N3]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1, I103N2]
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
    · exact ![300763, 67, 67]
    · exact ![357911, 71, 71]
    · exact ![28398241, 73]
    · exact ![6241, 79, 79, 79]
    · exact ![47458321, 83]
    · exact ![62742241, 89]
    · exact ![9409, 97, 97, 97]
    · exact ![1030301, 10201]
    · exact ![1092727, 103, 103]
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
      exact NI71N2
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
      exact NI79N2
      exact NI79N3
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
      exact NI97N1
      exact NI97N2
      exact NI97N3
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
      exact NI103N2
  β := ![I67N1, I67N2, I71N1, I71N2, I73N1, I79N1, I79N2, I79N3, I83N1, I89N1, I97N1, I97N2, I97N3, I103N1, I103N2]
  Il := ![[I67N1, I67N2], [I71N1, I71N2], [I73N1], [I79N1, I79N2, I79N3], [I83N1], [I89N1], [I97N1, I97N2, I97N3], [], [I103N1, I103N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
