
import IdealArithmetic.Examples.NF5_3_1125000000_2.RI5_3_1125000000_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0, 0, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0, 0, 0]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![0, 0, 67, 0, 0], ![0, 0, 0, 67, 0], ![0, 0, 0, 0, 67]] where
  M :=![![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![0, 0, 67, 0, 0], ![0, 0, 0, 67, 0], ![0, 0, 0, 0, 67]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 5 2 6 [19, 29, 8, 29, 44, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [64, 60, 22, 63, 62], [29, 19, 20, 41, 66], [33, 11, 8, 54, 3], [31, 43, 17, 43, 3], [0, 1]]
 g := ![![[46, 23, 10, 22, 62], [26, 10, 15, 3, 37], [8, 22, 45, 29], [38, 31, 23, 1], [], []], ![[56, 5, 62, 38, 7, 14, 55, 55], [37, 44, 51, 29, 64, 19, 47, 65], [3, 20, 52, 14], [42, 26, 34, 6], [11, 3, 21, 6], [5, 17, 12, 25]], ![[22, 50, 26, 22, 58, 1, 3, 20], [62, 40, 28, 21, 15, 34, 20, 18], [27, 31, 12, 59], [56, 58, 37, 37], [66, 47, 25, 17], [58, 54, 8, 1]], ![[39, 15, 61, 24, 56, 66, 61, 44], [33, 2, 45, 64, 46, 56, 54, 20], [13, 26, 15, 10], [37, 64, 12, 47], [48, 42, 22, 36], [26, 42, 62, 9]], ![[50, 46, 14, 25, 27, 0, 44, 66], [22, 52, 19, 52, 6, 35, 7, 11], [9, 50, 7, 56], [34, 65, 53, 47], [48, 36, 58, 62], [60, 57, 63, 9]]]
 h' := ![![[64, 60, 22, 63, 62], [42, 30, 62, 31, 53], [6, 9, 17, 57, 29], [15, 51, 35, 41, 30], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[29, 19, 20, 41, 66], [44, 37, 42, 31, 49], [35, 37, 58, 29, 56], [62, 30, 59, 15, 58], [18, 0, 48, 65, 26], [48, 43, 27, 19, 41], [64, 60, 22, 63, 62]], ![[33, 11, 8, 54, 3], [65, 66, 0, 33, 28], [37, 65, 8, 15, 60], [9, 24, 17, 46, 40], [1, 35, 42, 16, 29], [7, 2, 9, 36, 34], [29, 19, 20, 41, 66]], ![[31, 43, 17, 43, 3], [59, 19, 60, 5, 29], [13, 65, 42, 5, 37], [27, 62, 19, 62, 55], [23, 38, 63, 49, 39], [59, 45, 55, 11, 6], [33, 11, 8, 54, 3]], ![[0, 1], [25, 49, 37, 34, 42], [59, 25, 9, 28, 19], [30, 34, 4, 37, 18], [41, 61, 48, 4, 39], [22, 44, 42, 1, 53], [31, 43, 17, 43, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62, 64, 38, 21], [], [], []]
 b := ![[], [35, 18, 5, 47, 31], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 5
  hpos := by decide
  P := [19, 29, 8, 29, 44, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-60896987303621, -5795708010277, 48844409558864, -103215943928180, -64826070998629]
  a := ![0, -7, 2, -8, -11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-908910258263, -86503104631, 729021038192, -1540536476540, -967553298487]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 1350125107 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def PBC67 : ContainsPrimesAboveP 67 ![I67N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![67, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 67 (by decide) 𝕀

instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![719, -1218, 1004, 28, -176]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![719, -1218, 1004, 28, -176]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![0, 0, 0, 71, 0], ![6, 40, 54, 66, 1]] where
  M :=![![![719, -1218, 1004, 28, -176], ![-1760, 3011, -2492, -48, 464], ![2320, -3798, 3059, 244, -560], ![-1920, 3388, -2796, -33, 816], ![5040, -7722, 5884, 1196, -1361]]]
  hmulB := by decide  
  f := ![![![-2551, 1086, 2116, -276, -336]], ![![-3360, 1365, 2724, -352, -432]], ![![-2160, 842, 1717, -220, -272]], ![![320, -172, -300, 41, 48]], ![![-3446, 1338, 2734, -350, -433]]]
  g := ![![![25, 82, 148, 164, -176], ![-64, -219, -388, -432, 464], ![80, 262, 469, 524, -560], ![-96, -412, -660, -759, 816], ![186, 658, 1118, 1282, -1361]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 4 2 6 [10, 44, 48, 58, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [43, 65, 8, 51], [8, 69, 24, 34], [33, 7, 39, 57], [0, 1]]
 g := ![![[17, 16, 3, 40], [65, 24, 16, 19], [58, 5, 43, 18], [60, 26, 27], [1], []], ![[65, 60, 4, 5, 43, 59], [6, 52, 5, 21, 41, 21], [65, 26, 30, 31, 64, 51], [20, 54, 27], [22, 25, 32], [27, 52, 45]], ![[23, 40, 44, 44, 18, 52], [48, 57, 57, 36, 40, 13], [50, 52, 60, 30, 68, 21], [23, 55, 25], [67, 49, 49], [7, 46, 20]], ![[59, 13, 46, 20, 19, 25], [48, 33, 39, 39, 38, 4], [25, 14, 42, 46, 37, 20], [44, 6, 25], [19, 68, 48], [53, 36, 54]]]
 h' := ![![[43, 65, 8, 51], [60, 26, 31, 18], [59, 34, 24, 44], [68, 39, 22, 36], [61, 27, 23, 13], [0, 0, 1], [0, 1]], ![[8, 69, 24, 34], [15, 22, 67, 10], [62, 2, 44, 40], [17, 48, 15, 70], [69, 59, 36, 58], [17, 48, 27, 23], [43, 65, 8, 51]], ![[33, 7, 39, 57], [33, 29, 69, 29], [12, 33, 1, 21], [8, 63, 15, 46], [5, 56, 44, 5], [65, 52, 29, 7], [8, 69, 24, 34]], ![[0, 1], [30, 65, 46, 14], [68, 2, 2, 37], [10, 63, 19, 61], [33, 0, 39, 66], [62, 42, 14, 41], [33, 7, 39, 57]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [13, 46, 12], []]
 b := ![[], [], [46, 48, 31, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 4
  hpos := by decide
  P := [10, 44, 48, 58, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![78632282066541, -10494038940649, -43389547970595, 120437233915989, 59076718342910]
  a := ![3, -62, -1, -63, -58]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3884901802689, -33430461586719, -45542708992785, -53220086996001, 59076718342910]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 25411681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2551, -1086, -2116, 276, 336]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![2551, -1086, -2116, 276, 336]] 
 ![![71, 0, 0, 0, 0], ![22, 1, 0, 0, 0], ![42, 0, 1, 0, 0], ![24, 0, 0, 1, 0], ![8, 0, 0, 0, 1]] where
  M :=![![![2551, -1086, -2116, 276, 336], ![3360, -1365, -2724, 352, 432], ![2160, -842, -1717, 220, 272], ![-320, 172, 300, -41, -48], ![-560, 234, 460, -60, -73]]]
  hmulB := by decide  
  f := ![![![-719, 1218, -1004, -28, 176]], ![![-198, 335, -276, -8, 48]], ![![-458, 774, -637, -20, 112]], ![![-216, 364, -300, -9, 48]], ![![-152, 246, -196, -20, 39]]]
  g := ![![![1493, -1086, -2116, 276, 336], ![1914, -1365, -2724, 352, 432], ![1202, -842, -1717, 220, 272], ![-216, 172, 300, -41, -48], ![-324, 234, 460, -60, -73]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![719, -1218, 1004, 28, -176]] ![![2551, -1086, -2116, 276, 336]]
  ![![71, 0, 0, 0, 0]] where
 M := ![![![-71, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8749, -717, 2976, -164, -436]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![-8749, -717, 2976, -164, -436]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![0, 0, 0, 73, 0], ![42, 43, 28, 64, 1]] where
  M :=![![![-8749, -717, 2976, -164, -436], ![-4360, -3049, -1106, 392, 216], ![1080, -3097, -3441, 582, 568], ![5020, -1062, -3126, 353, 488], ![1430, 303, -312, -4, 41]]]
  hmulB := by decide  
  f := ![![![3, 3, -6, 8, 4]], ![![40, -15, -10, 52, 24]], ![![120, -17, -67, 186, 80]], ![![380, -60, -198, 573, 280]], ![![412, -68, -212, 620, 297]]]
  g := ![![![131, 247, 208, 380, -436], ![-184, -169, -98, -184, 216], ![-312, -377, -265, -490, 568], ![-212, -302, -230, -423, 488], ![-4, -20, -20, -36, 41]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 4 2 6 [44, 43, 51, 57, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 4, 65, 26], [12, 46, 64, 8], [55, 22, 17, 39], [0, 1]]
 g := ![![[36, 58, 70, 49], [68, 5, 35], [65, 12, 55], [26, 72, 55, 37], [1], []], ![[50, 11, 28, 6, 29, 29], [16, 26, 49], [35, 16, 49], [72, 68, 34, 33, 17, 40], [71, 9, 18], [66, 34, 19]], ![[68, 2, 58, 19, 45, 23], [65, 66, 9], [49, 38, 8], [40, 11, 27, 45, 31, 54], [36, 9, 55], [26, 4, 64]], ![[28, 3, 27, 36, 38, 51], [3, 26, 65], [59, 48, 35], [1, 4, 33, 49, 29, 63], [3, 63, 50], [29, 39, 61]]]
 h' := ![![[22, 4, 65, 26], [4, 31, 51, 66], [52, 20, 23, 53], [24, 59, 8, 37], [29, 30, 22, 16], [0, 0, 1], [0, 1]], ![[12, 46, 64, 8], [1, 21, 25, 18], [62, 12, 2, 66], [54, 28, 39, 7], [63, 62, 43, 43], [62, 3, 59, 23], [22, 4, 65, 26]], ![[55, 22, 17, 39], [48, 56, 10, 42], [34, 17, 60, 3], [0, 47, 68, 9], [68, 62, 66, 68], [22, 29, 68, 36], [12, 46, 64, 8]], ![[0, 1], [16, 38, 60, 20], [41, 24, 61, 24], [70, 12, 31, 20], [23, 65, 15, 19], [70, 41, 18, 14], [55, 22, 17, 39]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [56, 40, 33], []]
 b := ![[], [], [32, 68, 21, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 4
  hpos := by decide
  P := [44, 43, 51, 57, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![12038953681, -1275478177, -7005705186, 18676002491, 9498651485]
  a := ![1, -6, 1, -7, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5300060393, -5612568384, -3739286942, -8071749213, 9498651485]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 28398241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, -3, 6, -8, -4]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-3, -3, 6, -8, -4]] 
 ![![73, 0, 0, 0, 0], ![38, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![48, 0, 0, 1, 0], ![16, 0, 0, 0, 1]] where
  M :=![![![-3, -3, 6, -8, -4], ![-40, 15, 10, -52, -24], ![-120, 17, 67, -186, -80], ![-380, 60, 198, -573, -280], ![-550, 129, 246, -808, -321]]]
  hmulB := by decide  
  f := ![![![8749, 717, -2976, 164, 436]], ![![4614, 415, -1534, 80, 224]], ![![944, 121, -279, 10, 40]], ![![5684, 486, -1914, 103, 280]], ![![1898, 153, -648, 36, 95]]]
  g := ![![![7, -3, 6, -8, -4], ![30, 15, 10, -52, -24], ![122, 17, 67, -186, -80], ![380, 60, 198, -573, -280], ![500, 129, 246, -808, -321]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![-8749, -717, 2976, -164, -436]] ![![-3, -3, 6, -8, -4]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-576854, 164520, 400390, -48133, -62911]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![-576854, 164520, 400390, -48133, -62911]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![0, 0, 0, 79, 0], ![73, 16, 52, 33, 1]] where
  M :=![![![-576854, 164520, 400390, -48133, -62911], ![-629110, 167647, 425306, -50418, -66710], ![-333550, 81165, 218065, -25372, -34126], ![143925, -47497, -106116, 13146, 16737], ![117660, -32757, -80884, 9676, 12701]]]
  hmulB := by decide  
  f := ![![![-466, 546, -272, -369, 315]], ![![3150, -3681, 1830, 2498, -2106]], ![![-10530, 12359, -6179, -8308, 7102]], ![![33935, -39679, 19752, 26876, -22665]], ![![6433, -7486, 3706, 5119, -4243]]]
  g := ![![![50831, 14824, 46478, 25670, -62911], ![53680, 15633, 49294, 27228, -66710], ![27312, 7939, 25223, 13934, -34126], ![-13644, -3991, -12360, -6825, 16737], ![-10247, -2987, -9384, -5183, 12701]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 4 2 6 [54, 23, 11, 41, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 22, 18, 43], [24, 31, 0, 10], [54, 25, 61, 26], [0, 1]]
 g := ![![[30, 48, 55, 46], [9, 71, 78, 26], [45, 46, 62, 31], [3, 27, 0, 22], [1], []], ![[46, 59, 7, 30, 75, 43], [12, 73, 8, 74, 10, 69], [33, 41, 17, 18, 9, 60], [28, 52, 28, 50, 14, 56], [32, 68, 51], [9, 78, 32]], ![[4, 15, 69, 1], [28, 38, 56, 50, 31, 73], [59, 67, 18, 69, 70, 62], [39, 34, 74, 38, 15, 16], [11, 67, 67], [61, 8, 21]], ![[25, 78, 36, 78, 48, 51], [20, 68, 48, 49, 44, 44], [53, 14, 62, 11, 15, 44], [44, 31, 12, 20, 61, 16], [22, 40, 38], [36, 25, 44]]]
 h' := ![![[39, 22, 18, 43], [67, 33, 61, 58], [19, 52, 24, 37], [75, 46, 13, 30], [25, 56, 68, 38], [0, 0, 1], [0, 1]], ![[24, 31, 0, 10], [44, 18, 23, 1], [65, 51, 15, 30], [16, 5, 34, 50], [74, 60, 44, 4], [8, 62, 5, 50], [39, 22, 18, 43]], ![[54, 25, 61, 26], [30, 42, 18], [59, 2, 55, 49], [39, 39, 66, 41], [35, 9, 11, 7], [47, 48, 78, 15], [24, 31, 0, 10]], ![[0, 1], [74, 65, 56, 20], [6, 53, 64, 42], [27, 68, 45, 37], [20, 33, 35, 30], [24, 48, 74, 14], [54, 25, 61, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [20, 10, 4], []]
 b := ![[], [], [11, 17, 30, 47], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 4
  hpos := by decide
  P := [54, 23, 11, 41, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2948394415510, 698653456698, -2822489012250, 5295862795856, 3711342551302]
  a := ![1, 25, -3, 24, 33]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3392146985184, -742820599546, -2478636730126, -1483271410090, 3711342551302]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 38950081 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-466, 546, -272, -369, 315]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![-466, 546, -272, -369, 315]] 
 ![![79, 0, 0, 0, 0], ![28, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![23, 0, 0, 1, 0], ![52, 0, 0, 0, 1]] where
  M :=![![![-466, 546, -272, -369, 315], ![3150, -3681, 1830, 2498, -2106], ![-10530, 12359, -6179, -8308, 7102], ![33935, -39679, 19752, 26876, -22665], ![-80470, 94383, -47158, -63522, 54145]]]
  hmulB := by decide  
  f := ![![![-576854, 164520, 400390, -48133, -62911]], ![![-212418, 60433, 147294, -17698, -23142]], ![![-26128, 7275, 17965, -2149, -2821]], ![![-166123, 47297, 115226, -13847, -18104]], ![![-378212, 107877, 262524, -31560, -41249]]]
  g := ![![![-289, 546, -272, -369, 315], ![1934, -3681, 1830, 2498, -2106], ![-6535, 12359, -6179, -8308, 7102], ![20837, -39679, 19752, 26876, -22665], ![-49826, 94383, -47158, -63522, 54145]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![-576854, 164520, 400390, -48133, -62911]] ![![-466, 546, -272, -369, 315]]
  ![![79, 0, 0, 0, 0]] where
 M := ![![![79, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2058, -565, 320, 31, -39]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-2058, -565, 320, 31, -39]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![33, 42, 42, 1, 0], ![79, 50, 72, 0, 1]] where
  M :=![![![-2058, -565, 320, 31, -39], ![-390, -1403, -1192, 234, 202], ![1010, -1264, -1637, 254, 266], ![1525, -289, -922, 96, 141], ![290, 166, 46, -28, -13]]]
  hmulB := by decide  
  f := ![![![194, -229, 116, 151, -129]], ![![-1290, 1515, -760, -1014, 862]], ![![4310, -5056, 2529, 3398, -2890]], ![![1439, -1688, 844, 1135, -966]], ![![3542, -4155, 2078, 2793, -2376]]]
  g := ![![![0, 1, 22, 31, -39], ![-290, -257, -308, 234, 202], ![-342, -304, -379, 254, 266], ![-154, -137, -182, 96, 141], ![27, 24, 26, -28, -13]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [24, 5, 30, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 0, 3], [40, 82, 80], [0, 1]]
 g := ![![[79, 66, 38], [61, 65, 68], [27, 12], [49, 4], [65, 53, 1], []], ![[21, 31, 18, 75], [52, 37, 66, 27], [50, 77], [22, 26], [74, 39, 78, 3], [62, 9]], ![[6, 76, 27, 58], [42, 69, 48, 73], [32, 64], [56, 31], [37, 55], [68, 9]]]
 h' := ![![[13, 0, 3], [30, 81, 72], [28, 20, 63], [26, 58, 57], [17, 63, 2], [0, 0, 1], [0, 1]], ![[40, 82, 80], [71, 59, 5], [25, 62, 80], [48, 64, 34], [24, 27, 21], [9, 55, 82], [13, 0, 3]], ![[0, 1], [53, 26, 6], [57, 1, 23], [24, 44, 75], [66, 76, 60], [51, 28], [40, 82, 80]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 46], []]
 b := ![[], [31, 50, 40], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [24, 5, 30, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![59345108, -121436390, 91516612, 9832046, -110939472]
  a := ![-1, -7, 5, -5, -18]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![102398866, 60392666, 92364008, 9832046, -110939472]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 571787 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-53, 53, -20, -50, 28]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-53, 53, -20, -50, 28]] 
 ![![83, 0, 0, 0, 0], ![11, 1, 0, 0, 0], ![64, 0, 1, 0, 0], ![16, 0, 0, 1, 0], ![16, 0, 0, 0, 1]] where
  M :=![![![-53, 53, -20, -50, 28], ![280, -369, 206, 196, -256], ![-1280, 1335, -565, -1134, 648], ![3100, -4140, 2366, 2091, -2788], ![-9300, 10213, -4684, -7846, 5331]]]
  hmulB := by decide  
  f := ![![![-263431, 167439, 271786, -38242, -43612]], ![![-40167, 25048, 40976, -5746, -6572]], ![![-207088, 131055, 213105, -29962, -34192]], ![![-50972, 32134, 52334, -7353, -8396]], ![![-50012, 31821, 51630, -7266, -8285]]]
  g := ![![![12, 53, -20, -50, 28], ![-95, -369, 206, 196, -256], ![337, 1335, -565, -1134, 648], ![-1104, -4140, 2366, 2091, -2788], ![2631, 10213, -4684, -7846, 5331]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1

def I83N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![102, -66, -106, 15, 17]] i)))

def SI83N2: IdealEqSpanCertificate' Table ![![102, -66, -106, 15, 17]] 
 ![![83, 0, 0, 0, 0], ![71, 1, 0, 0, 0], ![11, 0, 1, 0, 0], ![72, 0, 0, 1, 0], ![67, 0, 0, 0, 1]] where
  M :=![![![102, -66, -106, 15, 17], ![170, -93, -162, 22, 26], ![130, -65, -115, 16, 18], ![5, 7, 0, -2, 1], ![-20, 9, 28, 0, -7]]]
  hmulB := by decide  
  f := ![![![74, -36, -8, 95, 39]], ![![68, -31, -10, 89, 37]], ![![28, -9, -9, 39, 17]], ![![121, -41, -36, 168, 73]], ![![136, -45, -42, 189, 82]]]
  g := ![![![45, -66, -106, 15, 17], ![63, -93, -162, 22, 26], ![44, -65, -115, 16, 18], ![-5, 7, 0, -2, 1], ![-6, 9, 28, 0, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N2 : Nat.card (O ⧸ I83N2) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N2)

lemma isPrimeI83N2 : Ideal.IsPrime I83N2 := prime_ideal_of_norm_prime hp83.out _ NI83N2
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-2058, -565, 320, 31, -39]] ![![-53, 53, -20, -50, 28]]
  ![![74, -36, -8, 95, 39]] where
 M := ![![![74, -36, -8, 95, 39]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI83N1 : IdealMulLeCertificate' Table 
  ![![74, -36, -8, 95, 39]] ![![102, -66, -106, 15, 17]]
  ![![83, 0, 0, 0, 0]] where
 M := ![![![83, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0, 0, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0, 0, 0]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![0, 0, 0, 89, 0], ![0, 0, 0, 0, 89]] where
  M :=![![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![0, 0, 0, 89, 0], ![0, 0, 0, 0, 89]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 5 2 6 [84, 65, 30, 61, 4, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [49, 73, 63, 23, 41], [69, 47, 88, 6, 30], [49, 26, 30, 64, 54], [7, 31, 86, 85, 53], [0, 1]]
 g := ![![[81, 37, 39, 14, 40], [69, 14, 31, 79], [2, 8, 71, 87], [49, 3, 43, 68, 16], [1], []], ![[40, 68, 35, 34, 51, 55, 54, 13], [21, 17, 47, 5], [12, 76, 77, 67], [23, 51, 43, 72, 43, 47, 23, 41], [3, 11, 28, 66, 51, 50, 33, 19], [0, 25, 57, 79]], ![[76, 37, 87, 45, 31, 50, 22, 83], [47, 40, 16, 39], [19, 87, 64, 18], [7, 84, 85, 64, 55, 53, 24, 86], [37, 59, 82, 74, 80, 59, 8, 3], [78, 44, 53, 10]], ![[57, 44, 60, 1, 64, 37, 83, 66], [22, 42, 31, 17], [16, 57, 37, 8], [41, 71, 36, 59, 37, 51, 62, 26], [53, 51, 88, 42, 71, 65, 3, 7], [17, 35, 54, 68]], ![[59, 51, 11, 12, 41, 88, 52, 36], [75, 12, 42, 57], [17, 88, 0, 10], [0, 72, 47, 71, 3, 83, 10, 68], [88, 10, 8, 83, 79, 58, 5, 9], [44, 34, 88, 50]]]
 h' := ![![[49, 73, 63, 23, 41], [76, 69, 19, 3, 29], [49, 73, 70, 14, 41], [67, 59, 36, 82, 40], [5, 24, 59, 28, 85], [0, 0, 1], [0, 1]], ![[69, 47, 88, 6, 30], [36, 67, 43, 26, 3], [51, 42, 72, 24, 70], [76, 72, 11, 11, 44], [33, 49, 1, 87, 88], [87, 70, 17, 5, 38], [49, 73, 63, 23, 41]], ![[49, 26, 30, 64, 54], [56, 20, 22, 81, 58], [55, 14, 39, 12, 22], [82, 69, 49, 43, 14], [79, 25, 71, 35, 13], [78, 34, 73, 72, 3], [69, 47, 88, 6, 30]], ![[7, 31, 86, 85, 53], [74, 43, 2, 40, 33], [63, 63, 62, 76, 27], [61, 14, 74, 71, 50], [71, 86, 71, 78, 42], [83, 16, 33, 83, 31], [49, 26, 30, 64, 54]], ![[0, 1], [21, 68, 3, 28, 55], [64, 75, 24, 52, 18], [54, 53, 8, 60, 30], [23, 83, 65, 39, 39], [2, 58, 54, 18, 17], [7, 31, 86, 85, 53]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 86, 48, 59], [], [], []]
 b := ![[], [53, 25, 62, 23, 55], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 5
  hpos := by decide
  P := [84, 65, 30, 61, 4, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1769997160847116, 2073869660096580, -1034974938485010, -1398660611340430, 1187731900525900]
  a := ![0, -4, -2, -14, 12]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-19887608548844, 23301906293220, -11628931893090, -15715287767870, 13345302253100]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![108036, -184155, 152438, 3033, -26543]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![108036, -184155, 152438, 3033, -26543]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![0, 0, 0, 97, 0], ![16, 18, 7, 34, 1]] where
  M :=![![![108036, -184155, 152438, 3033, -26543], ![-265430, 452341, -374376, -7574, 65218], ![326090, -555740, 459915, 9358, -80366], ![-269115, 457471, -377910, -9136, 66473], ![596500, -1015428, 839404, 18930, -148401]]]
  hmulB := by decide  
  f := ![![![-71268, 22451, 51514, -6321, -8115]], ![![-81150, 24409, 57544, -6994, -9054]], ![![-45270, 12892, 31403, -3774, -4934]], ![![15905, -5643, -12106, 1522, 1913]], ![![-24354, 7138, 17089, -2066, -2687]]]
  g := ![![![5492, 3027, 3487, 9335, -26543], ![-13494, -7439, -8566, -22938, 65218], ![16618, 9184, 10541, 28266, -80366], ![-13739, -7619, -8693, -23394, 66473], ![30628, 17070, 19363, 52212, -148401]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 4 2 6 [73, 45, 36, 91, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 33, 81, 7], [10, 37, 69, 58], [93, 26, 44, 32], [0, 1]]
 g := ![![[0, 78, 36, 48], [80, 77, 31], [39, 47, 89], [93, 49, 27], [0, 6, 1], []], ![[57, 35, 19, 93, 90, 57], [54, 5, 16], [51, 6, 86], [35, 14, 27], [41, 50, 6], [60, 16, 81, 92, 94, 52]], ![[96, 23, 49, 17, 59, 68], [73, 17, 18], [39, 50, 73], [81, 39, 73], [89, 45, 36], [3, 1, 48, 92, 61, 45]], ![[47, 54, 82, 9, 42, 44], [74, 30, 35], [90, 44, 85], [57, 9, 24], [35, 0, 75], [32, 71, 13, 36, 36, 79]]]
 h' := ![![[0, 33, 81, 7], [2, 27, 8, 57], [64, 48, 19, 15], [1, 95, 20, 63], [0, 47, 45, 30], [0, 0, 0, 1], [0, 1]], ![[10, 37, 69, 58], [11, 9, 17, 64], [48, 9, 25, 4], [52, 73, 52, 38], [45, 62, 4, 30], [82, 12, 34, 43], [0, 33, 81, 7]], ![[93, 26, 44, 32], [14, 41, 44, 57], [69, 83, 7, 42], [54, 58, 0, 48], [27, 71, 11, 48], [5, 28, 10, 6], [10, 37, 69, 58]], ![[0, 1], [31, 20, 28, 16], [1, 54, 46, 36], [13, 65, 25, 45], [10, 14, 37, 86], [25, 57, 53, 47], [93, 26, 44, 32]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [55, 70, 3], []]
 b := ![[], [], [6, 25, 3, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 4
  hpos := by decide
  P := [73, 45, 36, 91, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-31594167705, 104810578260, -92686002290, 23447596429, 114074186258]
  a := ![13, -7, 4, -6, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-19142073689, -20087884272, -9187683568, -39743038519, 114074186258]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 88529281 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-71268, 22451, 51514, -6321, -8115]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![-71268, 22451, 51514, -6321, -8115]] 
 ![![97, 0, 0, 0, 0], ![60, 1, 0, 0, 0], ![43, 0, 1, 0, 0], ![38, 0, 0, 1, 0], ![33, 0, 0, 0, 1]] where
  M :=![![![-71268, 22451, 51514, -6321, -8115], ![-81150, 24409, 57544, -6994, -9054], ![-45270, 12892, 31403, -3774, -4934], ![15905, -5643, -12106, 1522, 1913], ![14770, -4574, -10600, 1296, 1669]]]
  hmulB := by decide  
  f := ![![![108036, -184155, 152438, 3033, -26543]], ![![64090, -109247, 90432, 1798, -15746]], ![![51254, -87365, 72317, 1441, -12595]], ![![39549, -67427, 55822, 1094, -9713]], ![![42904, -73119, 60514, 1227, -10560]]]
  g := ![![![-32221, 22451, 51514, -6321, -8115], ![-35624, 24409, 57544, -6994, -9054], ![-19205, 12892, 31403, -3774, -4934], ![7774, -5643, -12106, 1522, 1913], ![6605, -4574, -10600, 1296, 1669]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![108036, -184155, 152438, 3033, -26543]] ![![-71268, 22451, 51514, -6321, -8115]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, -128, 64, 86, -74]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![109, -128, 64, 86, -74]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![82, 24, 1, 0, 0], ![52, 21, 0, 1, 0], ![63, 66, 0, 0, 1]] where
  M :=![![![109, -128, 64, 86, -74], ![-740, 863, -428, -588, 492], ![2460, -2894, 1451, 1936, -1668], ![-7970, 9298, -4616, -6327, 5294], ![18820, -22102, 11060, 14836, -12701]]]
  hmulB := by decide  
  f := ![![![2229, 280, -680, 26, 98]], ![![980, 915, 508, -132, -92]], ![![2038, 454, -421, -12, 56]], ![![1338, 337, -236, -15, 30]], ![![2027, 772, -92, -70, 1]]]
  g := ![![![-49, 14, 64, 86, -74], ![336, -89, -428, -588, 492], ![-1110, 314, 1451, 1936, -1668], ![3624, -955, -4616, -6327, 5294], ![-8509, 2368, 11060, 14836, -12701]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [6, 88, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [13, 100], [0, 1]]
 g := ![![[82, 17], [36], [52, 20], [1], [6], [13, 1]], ![[0, 84], [36], [9, 81], [1], [6], [26, 100]]]
 h' := ![![[13, 100], [67, 57], [92, 6], [37, 90], [89, 1], [23, 62], [0, 1]], ![[0, 1], [0, 44], [69, 95], [96, 11], [1, 100], [21, 39], [13, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55]]
 b := ![[], [99, 78]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [6, 88, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2716, 3045, -1653, -2235, 2148]
  a := ![-1, -1, -1, -2, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1126, -516, -1653, -2235, 2148]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3874, 993, 1606, -5577, -2309]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![-3874, 993, 1606, -5577, -2309]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![100, 94, 1, 0, 0], ![94, 52, 0, 1, 0], ![29, 25, 0, 0, 1]] where
  M :=![![![-3874, 993, 1606, -5577, -2309], ![-23090, 2741, 13140, -35650, -17690], ![-88450, 21290, 38391, -128650, -53610], ![-256505, 32585, 143370, -394094, -194845], ![-391540, 108630, 154280, -559350, -217209]]]
  hmulB := by decide  
  f := ![![![-8465474, 1859327, 5340994, -608583, -833741]], ![![-8337410, 1494541, 4935820, -540070, -766850]], ![![-16179190, 3236264, 9901991, -1107230, -1542290]], ![![-12145521, 2492445, 7494026, -842286, -1167939]], ![![-4477906, 900408, 2745106, -307277, -427618]]]
  g := ![![![4225, 1958, 1606, -5577, -2309], ![25020, 10531, 13140, -35650, -17690], ![96240, 43986, 38391, -128650, -53610], ![278236, 118018, 143370, -394094, -194845], ![426321, 199235, 154280, -559350, -217209]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P1 : CertificateIrreducibleZModOfList' 101 2 2 6 [44, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [100, 100], [0, 1]]
 g := ![![[62, 21], [80], [69, 77], [24], [31], [100, 1]], ![[41, 80], [80], [93, 24], [24], [31], [99, 100]]]
 h' := ![![[100, 100], [51, 83], [95, 79], [100, 28], [67, 23], [44, 58], [0, 1]], ![[0, 1], [69, 18], [16, 22], [72, 73], [44, 78], [87, 43], [100, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41]]
 b := ![[], [86, 71]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N1 : CertifiedPrimeIdeal' SI101N1 101 where
  n := 2
  hpos := by decide
  P := [44, 1, 1]
  hirr := P101P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-29064, 44058, -27726, -16180, 33972]
  a := ![3, 3, 0, -1, 14]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![32468, 26162, -27726, -16180, 33972]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N1 B_one_repr
lemma NI101N1 : Nat.card (O ⧸ I101N1) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, -148, 134, -24, -34]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![71, -148, 134, -24, -34]] 
 ![![101, 0, 0, 0, 0], ![67, 1, 0, 0, 0], ![28, 0, 1, 0, 0], ![89, 0, 0, 1, 0], ![36, 0, 0, 0, 1]] where
  M :=![![![71, -148, 134, -24, -34], ![-340, 395, -248, -188, -28], ![-140, -384, 583, -604, -348], ![-1570, 638, 344, -2015, -846], ![-1230, -542, 1570, -2574, -1329]]]
  hmulB := by decide  
  f := ![![![212791, -107104, -192418, 25932, 30690]], ![![144197, -72461, -130278, 17552, 20778]], ![![61088, -30608, -55105, 7420, 8788]], ![![187389, -94254, -169386, 22825, 27016]], ![![75366, -37942, -68158, 9186, 10871]]]
  g := ![![![95, -148, 134, -24, -34], ![-21, 395, -248, -188, -28], ![748, -384, 583, -604, -348], ![1543, 638, 344, -2015, -846], ![2654, -542, 1570, -2574, -1329]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![109, -128, 64, 86, -74]] ![![-3874, 993, 1606, -5577, -2309]]
  ![![3786984, -4116361, 1863258, 3221523, -2101605]] where
 M := ![![![3786984, -4116361, 1863258, 3221523, -2101605]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![3786984, -4116361, 1863258, 3221523, -2101605]] ![![71, -148, 134, -24, -34]]
  ![![101, 0, 0, 0, 0]] where
 M := ![![![-1065234476, 292474285, 423276860, -1524257155, -594288545]]]
 hmul := by decide  
 g := ![![![![-10546876, 2895785, 4190860, -15091655, -5884045]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0, 0, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0, 0, 0]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![0, 0, 0, 103, 0], ![0, 0, 0, 0, 103]] where
  M :=![![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![0, 0, 0, 103, 0], ![0, 0, 0, 0, 103]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 5 2 6 [50, 66, 45, 102, 4, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [13, 75, 39, 53], [74, 34, 59, 73, 36], [83, 14, 19, 10, 12], [32, 82, 89, 70, 55], [0, 1]]
 g := ![![[43, 53, 63, 65, 98], [68, 94, 72, 90, 92], [99, 94, 23, 23, 9], [16, 35, 62, 83], [99, 1], []], ![[41, 16, 83, 6, 1, 95, 75], [41, 27, 96, 29, 75, 54, 75], [1, 44, 50, 80, 29, 60, 99], [84, 0, 9, 7], [65, 45, 11, 32], [71, 64, 85, 18, 42]], ![[20, 34, 45, 96, 92, 77, 34, 14], [42, 16, 17, 93, 6, 89, 72, 61], [65, 78, 8, 95, 51, 4, 0, 30], [74, 58, 47, 1], [11, 6, 1, 63], [38, 41, 101, 20, 41, 1, 71, 100]], ![[15, 63, 39, 20, 10, 83, 18, 77], [11, 0, 44, 96, 95, 93, 12, 39], [51, 66, 57, 102, 88, 14, 68, 35], [88, 73, 6, 46], [49, 102, 66, 9], [92, 96, 55, 49, 84, 8, 86, 80]], ![[16, 1, 46, 76, 2, 40, 8, 59], [89, 51, 71, 87, 30, 84, 73, 14], [39, 45, 81, 63, 87, 7, 6, 55], [14, 17, 38, 66], [3, 76, 70, 14], [1, 84, 75, 59, 101, 7, 32, 30]]]
 h' := ![![[13, 75, 39, 53], [102, 15, 52, 64, 43], [97, 91, 39, 17, 68], [60, 85, 85, 27, 3], [97, 8, 11, 54, 17], [0, 0, 0, 1], [0, 1]], ![[74, 34, 59, 73, 36], [10, 64, 27, 56, 87], [0, 8, 48, 44, 16], [83, 45, 41, 17, 13], [36, 39, 1, 44, 25], [89, 63, 55, 34, 49], [13, 75, 39, 53]], ![[83, 14, 19, 10, 12], [63, 33, 46, 1, 82], [0, 48, 100, 33, 99], [66, 48, 53, 18, 11], [26, 8, 42, 77, 1], [79, 60, 91, 102, 28], [74, 34, 59, 73, 36]], ![[32, 82, 89, 70, 55], [41, 58, 5, 50, 18], [26, 44, 16, 86, 21], [97, 25, 33, 4, 75], [45, 47, 95, 59, 47], [69, 57, 80, 17, 3], [83, 14, 19, 10, 12]], ![[0, 1], [5, 36, 76, 35, 79], [62, 15, 3, 26, 2], [87, 3, 97, 37, 1], [13, 1, 57, 75, 13], [67, 26, 83, 52, 23], [32, 82, 89, 70, 55]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35, 25, 22], [], [], []]
 b := ![[], [16, 55, 51, 100, 54], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 5
  hpos := by decide
  P := [50, 66, 45, 102, 4, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-24381621356247, 54638636292442, -42796703999328, -647735625067, 52077791961379]
  a := ![1, 5, -3, 4, 11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-236714770449, 530472197014, -415501980576, -6288695389, 505609630693]
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



lemma PB1640I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB1640I2 : PrimesBelowBoundCertificateInterval O 61 103 1640 where
  m := 9
  g := ![1, 2, 2, 2, 3, 1, 2, 3, 1]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB1640I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1]
    · exact ![I79N0, I79N1]
    · exact ![I83N0, I83N1, I83N2]
    · exact ![I89N0]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1, I101N2]
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
    · exact ![1350125107]
    · exact ![25411681, 71]
    · exact ![28398241, 73]
    · exact ![38950081, 79]
    · exact ![571787, 83, 83]
    · exact ![5584059449]
    · exact ![88529281, 97]
    · exact ![10201, 10201, 101]
    · exact ![11592740743]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
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
  β := ![I71N1, I73N1, I79N1, I83N1, I83N2, I97N1, I101N2]
  Il := ![[], [I71N1], [I73N1], [I79N1], [I83N1, I83N2], [], [I97N1], [I101N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
