
import IdealArithmetic.Examples.NF5_3_1822500000_2.RI5_3_1822500000_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 5, 14, 11, 38]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![19, 5, 14, 11, 38]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![0, 0, 67, 0, 0], ![45, 15, 10, 1, 0], ![58, 24, 1, 0, 1]] where
  M :=![![![19, 5, 14, 11, 38], ![-120, -59, -66, -44, -162], ![720, 282, 455, 326, 1148], ![-4080, -1788, -2324, -1613, -5892], ![1128, 507, 630, 433, 1593]]]
  hmulB := by decide  
  f := ![![![-71, 7, -4, -9, -28]], ![![24, -35, -6, -6, -22]], ![![96, 78, 33, 46, 152]], ![![-33, 6, 0, -2, -6]], ![![-50, -5, -5, -9, -29]]]
  g := ![![![-40, -16, -2, 11, 38], ![168, 67, 8, -44, -162], ![-1202, -480, -59, 326, 1148], ![6123, 2445, 294, -1613, -5892], ![-1653, -660, -79, 433, 1593]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [41, 12, 24, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [45, 35, 30], [65, 31, 37], [0, 1]]
 g := ![![[61, 53, 10], [17, 22, 36], [30, 25], [41, 47], [43, 1], []], ![[5, 20, 35, 5], [26, 9, 20, 12], [1, 19], [53, 29], [49, 23], [64, 29]], ![[5, 6, 43, 1], [50, 47, 31, 54], [21, 59], [29, 4], [52, 19], [57, 29]]]
 h' := ![![[45, 35, 30], [40, 15, 12], [60, 18, 6], [33, 4, 62], [46, 46, 28], [0, 0, 1], [0, 1]], ![[65, 31, 37], [26, 34, 18], [23, 16, 56], [59, 4, 32], [17, 40, 37], [4, 54, 31], [45, 35, 30]], ![[0, 1], [20, 18, 37], [29, 33, 5], [32, 59, 40], [22, 48, 2], [12, 13, 35], [65, 31, 37]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 53], []]
 b := ![[], [25, 38, 63], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [41, 12, 24, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3266979763, -410525757, -4251056481, -3180419096, -9243492249]
  a := ![-180, -61, -183, -126, -395]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![10089170597, 4017008577, 549203384, -3180419096, -9243492249]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 300763 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-71, 7, -4, -9, -28]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![-71, 7, -4, -9, -28]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![40, 57, 1, 0, 0], ![65, 7, 0, 1, 0], ![19, 42, 0, 0, 1]] where
  M :=![![![-71, 7, -4, -9, -28], ![24, -35, -6, -6, -22], ![96, 78, 33, 46, 152], ![-336, -168, -60, -99, -332], ![96, 21, 8, 17, 57]]]
  hmulB := by decide  
  f := ![![![19, 5, 14, 11, 38]], ![![-120, -59, -66, -44, -162]], ![![-80, -43, -41, -26, -98]], ![![-55, -28, -28, -18, -68]], ![![-53, -28, -28, -18, -67]]]
  g := ![![![18, 22, -4, -9, -28], ![16, 19, -6, -6, -22], ![-106, -127, 33, 46, 152], ![221, 267, -60, -99, -332], ![-36, -44, 8, 17, 57]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P1 : CertificateIrreducibleZModOfList' 67 2 2 6 [16, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [60, 66], [0, 1]]
 g := ![![[13, 21], [20, 22], [25], [24], [49], [1]], ![[0, 46], [0, 45], [25], [24], [49], [1]]]
 h' := ![![[60, 66], [15, 50], [26, 42], [15, 5], [8, 15], [51, 60], [0, 1]], ![[0, 1], [0, 17], [0, 25], [47, 62], [37, 52], [33, 7], [60, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [63, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N1 : CertifiedPrimeIdeal' SI67N1 67 where
  n := 2
  hpos := by decide
  P := [16, 7, 1]
  hirr := P67P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1146, -48, 1931, 1445, 4032]
  a := ![-5, -4, -5, -4, -11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3681, -4322, 1931, 1445, 4032]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N1 B_one_repr
lemma NI67N1 : Nat.card (O ⧸ I67N1) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![19, 5, 14, 11, 38]] ![![-71, 7, -4, -9, -28]]
  ![![67, 0, 0, 0, 0]] where
 M := ![![![67, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 13, -28, -15, -36]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![17, 13, -28, -15, -36]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![0, 0, 0, 71, 0], ![37, 45, 56, 30, 1]] where
  M :=![![![17, 13, -28, -15, -36], ![-216, -19, -254, -202, -570], ![-864, 66, -1655, -1234, -3416], ![-6864, 264, -11448, -8699, -24172], ![2304, -105, 3940, 2983, 8281]]]
  hmulB := by decide  
  f := ![![![-17, -5, -2, -3, -10]], ![![24, 1, 6, 8, 26]], ![![-48, -18, -13, -10, -36]], ![![144, 36, 80, 63, 220]], ![![29, -1, 26, 22, 75]]]
  g := ![![![19, 23, 28, 15, -36], ![294, 361, 446, 238, -570], ![1768, 2166, 2671, 1426, -3416], ![12500, 15324, 18904, 10091, -24172], ![-4283, -5250, -6476, -3457, 8281]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 4 2 6 [37, 17, 44, 25, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [45, 60, 53, 2], [15, 70, 4, 51], [57, 11, 14, 18], [0, 1]]
 g := ![![[41, 32, 21, 25], [49, 65, 21, 30], [47, 12, 17, 18], [2, 65, 57], [1], []], ![[17, 37, 21, 47, 34, 6], [53, 25, 20, 2, 51, 40], [25, 26, 14, 9, 13, 37], [35, 32, 54], [36, 22, 9], [2, 41, 4]], ![[70, 67, 15, 53, 48, 17], [29, 41, 17, 6, 15, 61], [16, 37, 52, 50, 16, 21], [53, 66, 4], [59, 30, 50], [26, 64, 45]], ![[48, 3, 47, 33, 43, 25], [18, 6, 7, 47, 49, 4], [59, 46, 51, 36, 58, 37], [33, 41, 20], [0, 16, 64], [14, 1, 40]]]
 h' := ![![[45, 60, 53, 2], [33, 46, 49, 66], [36, 40, 42, 32], [17, 26, 30, 35], [34, 54, 27, 46], [0, 0, 1], [0, 1]], ![[15, 70, 4, 51], [47, 1, 11, 28], [48, 2, 34, 37], [3, 56, 9, 57], [37, 20, 47, 57], [34, 15, 53, 3], [45, 60, 53, 2]], ![[57, 11, 14, 18], [66, 25, 58, 38], [25, 31, 64, 6], [47, 45, 42, 31], [37, 17, 6, 2], [44, 0, 58, 60], [15, 70, 4, 51]], ![[0, 1], [54, 70, 24, 10], [11, 69, 2, 67], [65, 15, 61, 19], [24, 51, 62, 37], [33, 56, 30, 8], [57, 11, 14, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [64, 55, 67], []]
 b := ![[], [], [41, 15, 68, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 4
  hpos := by decide
  P := [37, 17, 44, 25, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![138937302723832, 14559436843650, 187680903252958, 140689088374539, 406083947280124]
  a := ![319, 126, 324, 221, 700]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-209664348544236, -257172087193830, -317648171048366, -169603230000411, 406083947280124]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 25411681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17, -5, -2, -3, -10]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-17, -5, -2, -3, -10]] 
 ![![71, 0, 0, 0, 0], ![67, 1, 0, 0, 0], ![55, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![19, 0, 0, 0, 1]] where
  M :=![![![-17, -5, -2, -3, -10], ![24, 1, 6, 8, 26], ![-48, -18, -13, -10, -36], ![144, 36, 80, 63, 220], ![-24, -3, -22, -17, -59]]]
  hmulB := by decide  
  f := ![![![17, 13, -28, -15, -36]], ![![13, 12, -30, -17, -42]], ![![1, 11, -45, -29, -76]], ![![-95, 5, -164, -124, -344]], ![![37, 2, 48, 38, 107]]]
  g := ![![![9, -5, -2, -3, -10], ![-13, 1, 6, 8, 26], ![37, -18, -13, -10, -36], ![-159, 36, 80, 63, 220], ![37, -3, -22, -17, -59]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![17, 13, -28, -15, -36]] ![![-17, -5, -2, -3, -10]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-581, -38, -830, -648, -1820]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![-581, -38, -830, -648, -1820]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![0, 0, 0, 73, 0], ![59, 7, 53, 31, 1]] where
  M :=![![![-581, -38, -830, -648, -1820], ![-2976, 247, -5482, -4110, -11384], ![-22704, 840, -37951, -28838, -80180], ![-152016, 6804, -260194, -196971, -547404], ![52704, -2262, 89808, 68030, 189091]]]
  hmulB := by decide  
  f := ![![![2155, 8966, -2922, -4744, -14412]], ![![4320, 18007, -5870, -9530, -28952]], ![![8688, 36168, -11787, -19138, -58140]], ![![17424, 72636, -23686, -38447, -116804]], ![![15713, 65453, -21337, -34639, -105233]]]
  g := ![![![1463, 174, 1310, 764, -1820], ![9160, 1095, 8190, 4778, -11384], ![64492, 7700, 57693, 33654, -80180], ![440340, 52584, 393866, 229761, -547404], ![-152105, -18163, -136055, -79367, 189091]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 4 2 6 [65, 8, 70, 5, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [55, 5, 70, 22], [11, 13, 64, 41], [2, 54, 12, 10], [0, 1]]
 g := ![![[16, 6, 17, 48], [24, 53, 65], [10, 3, 69], [60, 63, 64, 25], [1], []], ![[66, 54, 25, 35, 36, 15], [8, 31, 3], [19, 35, 23], [6, 11, 49, 59, 47, 10], [5, 58, 3], [60, 3, 46]], ![[21, 47, 11, 67, 12, 61], [6, 1, 25], [45, 20, 1], [53, 35, 20, 51, 50, 41], [72, 67, 16], [2, 55, 2]], ![[9, 20, 52, 59, 64, 11], [52, 63, 18], [60, 3, 12], [50, 1, 31, 1, 52, 68], [46, 68, 70], [50, 32, 27]]]
 h' := ![![[55, 5, 70, 22], [42, 67, 15, 11], [19, 36, 56, 49], [42, 15, 60, 54], [8, 65, 3, 68], [0, 0, 1], [0, 1]], ![[11, 13, 64, 41], [7, 55, 21, 71], [4, 66, 58, 52], [12, 40, 56, 60], [41, 28, 16, 10], [1, 21, 0, 52], [55, 5, 70, 22]], ![[2, 54, 12, 10], [29, 61, 7, 51], [45, 36, 2, 68], [59, 2, 49, 1], [0, 28, 5, 1], [64, 53, 64, 4], [11, 13, 64, 41]], ![[0, 1], [57, 36, 30, 13], [15, 8, 30, 50], [51, 16, 54, 31], [64, 25, 49, 67], [39, 72, 8, 17], [2, 54, 12, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [2, 49, 60], []]
 b := ![[], [], [48, 15, 58, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 4
  hpos := by decide
  P := [65, 8, 70, 5, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![297426060690741, 41743119866411, 376626714569894, 281356896296481, 821967705208004]
  a := ![-391, -131, -396, -270, -858]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-660255733514815, -78246997487529, -591611803581566, -345200574865091, 821967705208004]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 28398241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2155, 8966, -2922, -4744, -14412]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![2155, 8966, -2922, -4744, -14412]] 
 ![![73, 0, 0, 0, 0], ![43, 1, 0, 0, 0], ![49, 0, 1, 0, 0], ![10, 0, 0, 1, 0], ![25, 0, 0, 0, 1]] where
  M :=![![![2155, 8966, -2922, -4744, -14412], ![4320, 18007, -5870, -9530, -28952], ![8688, 36168, -11787, -19138, -58140], ![17424, 72636, -23686, -38447, -116804], ![-10944, -45594, 14864, 24130, 73307]]]
  hmulB := by decide  
  f := ![![![-581, -38, -830, -648, -1820]], ![![-383, -19, -564, -438, -1228]], ![![-701, -14, -1077, -830, -2320]], ![![-2162, 88, -3678, -2787, -7748]], ![![523, -44, 946, 710, 1967]]]
  g := ![![![2295, 8966, -2922, -4744, -14412], ![4613, 18007, -5870, -9530, -28952], ![9259, 36168, -11787, -19138, -58140], ![18620, 72636, -23686, -38447, -116804], ![-11681, -45594, 14864, 24130, 73307]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![-581, -38, -830, -648, -1820]] ![![2155, 8966, -2922, -4744, -14412]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1639, -74, 2798, 2120, 5890]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![1639, -74, 2798, 2120, 5890]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![4, 71, 1, 0, 0], ![32, 19, 0, 1, 0], ![6, 62, 0, 0, 1]] where
  M :=![![![1639, -74, 2798, 2120, 5890], ![11280, -491, 19216, 14558, 40460], ![77136, -3468, 131663, 99756, 277164], ![530496, -23196, 903948, 684839, 1903248], ![-183000, 8022, -311874, -236280, -656635]]]
  hmulB := by decide  
  f := ![![![-1079, -250, -350, -540, -1738]], ![![2832, 1603, 304, 458, 1580]], ![![2428, 1423, 239, 358, 1248]], ![![368, 347, -60, -95, -276]], ![![2130, 1220, 218, 328, 1137]]]
  g := ![![![-1427, -7648, 2798, 2120, 5890], ![-9800, -52531, 19216, 14558, 40460], ![-67148, -359887, 131663, 99756, 277164], ![-461008, -2471099, 903948, 684839, 1903248], ![159054, 852554, -311874, -236280, -656635]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [61, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [73, 78], [0, 1]]
 g := ![![[26, 19], [42, 32], [32, 16], [43, 26], [36], [1]], ![[70, 60], [8, 47], [15, 63], [45, 53], [36], [1]]]
 h' := ![![[73, 78], [45, 63], [23, 36], [63, 75], [24, 42], [18, 73], [0, 1]], ![[0, 1], [62, 16], [44, 43], [8, 4], [9, 37], [54, 6], [73, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38]]
 b := ![[], [57, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [61, 6, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1840189, 718224, 1246748, 884652, 3043712]
  a := ![216, 72, 220, 140, 474]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-629341, -3712904, 1246748, 884652, 3043712]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-23695, -98700, 32171, 52231, 158676]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![-23695, -98700, 32171, 52231, 158676]] 
 ![![79, 0, 0, 0, 0], ![50, 1, 0, 0, 0], ![28, 0, 1, 0, 0], ![22, 0, 0, 1, 0], ![21, 0, 0, 0, 1]] where
  M :=![![![-23695, -98700, 32171, 52231, 158676], ![-47592, -198235, 64615, 104905, 318698], ![-95592, -398154, 129776, 210697, 640090], ![-191976, -799674, 260657, 423186, 1285626], ![120504, 501942, -163608, -265624, -806957]]]
  hmulB := by decide  
  f := ![![![-1249, 36, -2227, -1681, -4676]], ![![-902, 29, -1601, -1209, -3362]], ![![-1228, 42, -2116, -1601, -4454]], ![![-5602, 270, -9647, -7308, -20290]], ![![1485, -78, 2525, 1915, 5315]]]
  g := ![![![-5959, -98700, 32171, 52231, 158676], ![-11970, -198235, 64615, 104905, 318698], ![-24036, -398154, 129776, 210697, 640090], ![-48290, -799674, 260657, 423186, 1285626], ![30307, 501942, -163608, -265624, -806957]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1

def I79N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-77, 171, 47, 56, 192]] i)))

def SI79N2: IdealEqSpanCertificate' Table ![![-77, 171, 47, 56, 192]] 
 ![![79, 0, 0, 0, 0], ![50, 1, 0, 0, 0], ![28, 0, 1, 0, 0], ![22, 0, 0, 1, 0], ![64, 0, 0, 0, 1]] where
  M :=![![![-77, 171, 47, 56, 192], ![-576, -461, -157, -225, -752], ![1848, 792, 410, 625, 2050], ![-4200, -1602, -733, -1140, -3750], ![648, 147, 54, 95, 313]]]
  hmulB := by decide  
  f := ![![![-14195, -5943, -8581, -6024, -21542]], ![![-7930, -3317, -4801, -3371, -12048]], ![![-11300, -4728, -6838, -4801, -17162]], ![![32746, 13836, 19495, 13660, 49130]], ![![-21680, -9117, -13010, -9125, -32721]]]
  g := ![![![-297, 171, 47, 56, 192], ![1012, -461, -157, -225, -752], ![-2458, 792, 410, 625, 2050], ![4576, -1602, -733, -1140, -3750], ![-384, 147, 54, 95, 313]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N2 : Nat.card (O ⧸ I79N2) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N2)

lemma isPrimeI79N2 : Ideal.IsPrime I79N2 := prime_ideal_of_norm_prime hp79.out _ NI79N2

def I79N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![557, -23, 940, 713, 1982]] i)))

def SI79N3: IdealEqSpanCertificate' Table ![![557, -23, 940, 713, 1982]] 
 ![![79, 0, 0, 0, 0], ![66, 1, 0, 0, 0], ![68, 0, 1, 0, 0], ![15, 0, 0, 1, 0], ![20, 0, 0, 0, 1]] where
  M :=![![![557, -23, 940, 713, 1982], ![3768, -169, 6440, 4878, 13554], ![25920, -1146, 44183, 33476, 93024], ![177696, -7872, 303050, 229599, 638008], ![-61320, 2715, -104566, -79223, -220145]]]
  hmulB := by decide  
  f := ![![![-1885, -7225, 2302, 3749, 11376]], ![![-1614, -6217, 1984, 3230, 9802]], ![![-1724, -6590, 2095, 3416, 10364]], ![![-477, -2085, 708, 1124, 3424]], ![![-380, -1373, 424, 699, 2117]]]
  g := ![![![-1420, -23, 940, 713, 1982], ![-9712, -169, 6440, 4878, 13554], ![-66652, -1146, 44183, 33476, 93024], ![-457143, -7872, 303050, 229599, 638008], ![157737, 2715, -104566, -79223, -220145]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N3 : Nat.card (O ⧸ I79N3) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N3)

lemma isPrimeI79N3 : Ideal.IsPrime I79N3 := prime_ideal_of_norm_prime hp79.out _ NI79N3
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![1639, -74, 2798, 2120, 5890]] ![![-23695, -98700, 32171, 52231, 158676]]
  ![![-1273, -5302, 1727, 2805, 8522]] where
 M := ![![![-1273, -5302, 1727, 2805, 8522]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI79N1 : IdealMulLeCertificate' Table 
  ![![-1273, -5302, 1727, 2805, 8522]] ![![-77, 171, 47, 56, 192]]
  ![![84725, 353447, -115224, -187073, -568326]] where
 M := ![![![84725, 353447, -115224, -187073, -568326]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI79N2 : IdealMulLeCertificate' Table 
  ![![84725, 353447, -115224, -187073, -568326]] ![![557, -23, 940, 713, 1982]]
  ![![79, 0, 0, 0, 0]] where
 M := ![![![553, -948, 2054, 1738, 4898]]]
 hmul := by decide  
 g := ![![![![7, -12, 26, 22, 62]]]]
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

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7369, 478, -530, -1088, -3414]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-7369, 478, -530, -1088, -3414]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![0, 0, 0, 83, 0], ![21, 32, 18, 31, 1]] where
  M :=![![![-7369, 478, -530, -1088, -3414], ![3600, -2755, -424, -306, -1204], ![6864, 7092, 2599, 3540, 11852], ![-29568, -14844, -7084, -10033, -33280], ![9480, 1806, 1462, 2232, 7293]]]
  hmulB := by decide  
  f := ![![![-3083, -12842, 4186, 6796, 20646]], ![![-6192, -25793, 8408, 13650, 41468]], ![![-12432, -51804, 16893, 27420, 83300]], ![![-24960, -104052, 33956, 55093, 167360]], ![![-14997, -62504, 20390, 33089, 100519]]]
  g := ![![![775, 1322, 734, 1262, -3414], ![348, 431, 256, 446, -1204], ![-2916, -4484, -2539, -4384, 11852], ![8064, 12652, 7132, 12309, -33280], ![-1731, -2790, -1564, -2697, 7293]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 4 2 6 [57, 53, 23, 40, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [58, 7, 24, 82], [78, 46, 39, 78], [73, 29, 20, 6], [0, 1]]
 g := ![![[15, 25, 67, 7], [63, 47, 34, 44], [4, 9, 33], [41], [43, 1], []], ![[10, 44, 64, 39, 27, 58], [53, 63, 77, 6, 79, 53], [77, 10, 37], [42, 5, 21], [74, 43, 0, 37, 10, 57], [75, 78, 1]], ![[62, 44, 47, 0, 82, 3], [11, 65, 67, 70, 48, 27], [62, 6, 23], [56, 30, 40], [67, 4, 56, 64, 43, 28], [61, 21, 25]], ![[11, 40, 55, 77, 33, 45], [52, 60, 30, 2, 0, 2], [56, 29, 31], [50, 59, 44], [16, 67, 37, 48, 1, 52], [29, 45, 36]]]
 h' := ![![[58, 7, 24, 82], [61, 69, 54, 67], [51, 37, 77, 58], [14, 45, 12, 45], [39, 71, 37], [0, 0, 1], [0, 1]], ![[78, 46, 39, 78], [49, 74, 66, 5], [50, 7, 38, 69], [17, 54, 6, 55], [81, 2, 15, 42], [2, 27, 71, 21], [58, 7, 24, 82]], ![[73, 29, 20, 6], [3, 77, 23, 4], [17, 12, 29, 71], [56, 74, 32, 43], [29, 39, 79, 66], [34, 7, 26, 54], [78, 46, 39, 78]], ![[0, 1], [26, 29, 23, 7], [45, 27, 22, 51], [0, 76, 33, 23], [51, 54, 35, 58], [24, 49, 68, 8], [73, 29, 20, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [11, 19, 51], []]
 b := ![[], [], [9, 49, 0, 60], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 4
  hpos := by decide
  P := [57, 53, 23, 40, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2518773546429288, 46081231424998, 3920466050251287, 2958826713329117, 8337185549782410]
  a := ![619, 214, 629, 437, 1358]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2079061722879534, -3213781401947134, -1760829805371471, -3078240064215971, 8337185549782410]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 47458321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3083, -12842, 4186, 6796, 20646]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-3083, -12842, 4186, 6796, 20646]] 
 ![![83, 0, 0, 0, 0], ![49, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![38, 0, 0, 1, 0], ![82, 0, 0, 0, 1]] where
  M :=![![![-3083, -12842, 4186, 6796, 20646], ![-6192, -25793, 8408, 13650, 41468], ![-12432, -51804, 16893, 27420, 83300], ![-24960, -104052, 33956, 55093, 167360], ![15672, 65310, -21302, -34572, -105025]]]
  hmulB := by decide  
  f := ![![![-7369, 478, -530, -1088, -3414]], ![![-4307, 249, -318, -646, -2030]], ![![-450, 120, -7, -36, -104]], ![![-3730, 40, -328, -619, -1964]], ![![-7166, 494, -506, -1048, -3285]]]
  g := ![![![-16267, -12842, 4186, 6796, 20646], ![-32673, -25793, 8408, 13650, 41468], ![-65638, -51804, 16893, 27420, 83300], ![-131894, -104052, 33956, 55093, 167360], ![82760, 65310, -21302, -34572, -105025]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-7369, 478, -530, -1088, -3414]] ![![-3083, -12842, 4186, 6796, 20646]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1469, -2969, -416, 547, 1994]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![-1469, -2969, -416, 547, 1994]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![17, 61, 20, 1, 0], ![47, 29, 1, 0, 1]] where
  M :=![![![-1469, -2969, -416, 547, 1994], ![-8472, -6287, -8900, -4970, -13274], ![-39264, -8286, -63795, -45016, -121560], ![-323712, -25608, -498574, -369635, -1034528], ![111240, 14973, 168446, 122911, 342401]]]
  hmulB := by decide  
  f := ![![![-117973, 63871, 6402, 1169, 8968]], ![![-131064, -170629, -57056, -78636, -263698]], ![![666960, 354954, 153997, 230312, 760412]], ![![18779, -32278, -6892, -7502, -26474]], ![![-93979, -17373, -13029, -21652, -70171]]]
  g := ![![![-1174, -1058, -150, 547, 1994], ![7864, 7661, 1166, -4970, -13274], ![72352, 70370, 10765, -45016, -121560], ![613291, 590151, 89086, -369635, -1034528], ![-203046, -195643, -29575, 122911, 342401]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [45, 2, 86, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [82, 63, 56], [10, 25, 33], [0, 1]]
 g := ![![[14, 77, 73], [37, 84], [14, 49], [84, 70, 10], [7, 3, 1], []], ![[63, 10, 66, 58], [52, 68], [50, 1], [61, 30, 8, 7], [7, 42, 41, 23], [88, 21]], ![[53, 38, 67, 26], [59, 55], [68, 36], [23, 27, 81, 52], [50, 71, 18, 58], [22, 21]]]
 h' := ![![[82, 63, 56], [21, 25, 47], [66, 84, 66], [47, 54, 82], [41, 29, 59], [0, 0, 1], [0, 1]], ![[10, 25, 33], [81, 83, 83], [75, 8, 35], [79, 68, 1], [44, 62, 73], [5, 44, 25], [82, 63, 56]], ![[0, 1], [4, 70, 48], [16, 86, 77], [53, 56, 6], [64, 87, 46], [0, 45, 63], [10, 25, 33]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59, 26], []]
 b := ![[], [74, 13, 79], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [45, 2, 86, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![67925510, 26069212, 46747781, 33294796, 113776740]
  a := ![41, 10, 42, 27, 90]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-65680818, -59600436, -8235111, 33294796, 113776740]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 704969 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 28, 46, 44, 132]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![73, 28, 46, 44, 132]] 
 ![![89, 0, 0, 0, 0], ![32, 1, 0, 0, 0], ![44, 0, 1, 0, 0], ![16, 0, 0, 1, 0], ![83, 0, 0, 0, 1]] where
  M :=![![![73, 28, 46, 44, 132], ![0, -59, 204, 134, 352], ![1200, 48, 1627, 1272, 3572], ![5856, -420, 10748, 8075, 22376], ![-2160, 96, -3734, -2826, -7851]]]
  hmulB := by decide  
  f := ![![![4145, 16612, -5282, -8676, -26316]], ![![1568, 6341, -2028, -3322, -10080]], ![![2300, 8992, -2813, -4656, -14108]], ![![688, 4316, -1692, -2533, -7784]], ![![3755, 14596, -4548, -7542, -22847]]]
  g := ![![![-163, 28, 46, 44, 132], ![-432, -59, 204, 134, 352], ![-4368, 48, 1627, 1272, 3572], ![-27416, -420, 10748, 8075, 22376], ![9617, 96, -3734, -2826, -7851]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1

def I89N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, 3, -51, -36, -98]] i)))

def SI89N2: IdealEqSpanCertificate' Table ![![-7, 3, -51, -36, -98]] 
 ![![89, 0, 0, 0, 0], ![37, 1, 0, 0, 0], ![55, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![49, 0, 0, 0, 1]] where
  M :=![![![-7, 3, -51, -36, -98], ![-240, 11, -371, -283, -788], ![-1464, 60, -2524, -1913, -5314], ![-10200, 450, -17367, -13150, -36554], ![3504, -153, 5990, 4535, 12605]]]
  hmulB := by decide  
  f := ![![![105145, 437967, -142757, -231772, -704116]], ![![46085, 191960, -62570, -101585, -308612]], ![![69743, 290505, -94691, -153735, -467042]], ![![23748, 98922, -32245, -52350, -159038]], ![![51881, 216102, -70439, -114361, -347425]]]
  g := ![![![89, 3, -51, -36, -98], ![694, 11, -371, -283, -788], ![4702, 60, -2524, -1913, -5314], ![32329, 450, -17367, -13150, -36554], ![-11150, -153, 5990, 4535, 12605]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N2 : Nat.card (O ⧸ I89N2) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N2)

lemma isPrimeI89N2 : Ideal.IsPrime I89N2 := prime_ideal_of_norm_prime hp89.out _ NI89N2
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![-1469, -2969, -416, 547, 1994]] ![![73, 28, 46, 44, 132]]
  ![![-1710245, 75755, -2916522, -2209653, -6140170]] where
 M := ![![![-1710245, 75755, -2916522, -2209653, -6140170]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![-1710245, 75755, -2916522, -2209653, -6140170]] ![![-7, 3, -51, -36, -98]]
  ![![89, 0, 0, 0, 0]] where
 M := ![![![5286883643, -234186590, 9015844269, 6830702741, 18981119890]]]
 hmul := by decide  
 g := ![![![![59403187, -2631310, 101301621, 76749469, 213271010]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-367, -153, -220, -155, -558]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-367, -153, -220, -155, -558]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![0, 0, 0, 97, 0], ![13, 30, 7, 38, 1]] where
  M :=![![![-367, -153, -220, -155, -558], ![2232, 935, 1366, 958, 3410], ![-12864, -5466, -7561, -5294, -19136], ![78096, 32304, 48200, 33915, 120348], ![-21768, -8979, -13512, -9511, -33677]]]
  hmulB := by decide  
  f := ![![![-7, -33, -10, -13, -44]], ![![120, 77, 30, 44, 146]], ![![-336, -138, -69, -106, -348]], ![![720, 252, 128, 199, 652]], ![![293, 108, 53, 82, 269]]]
  g := ![![![71, 171, 38, 217, -558], ![-434, -1045, -232, -1326, 3410], ![2432, 5862, 1303, 7442, -19136], ![-15324, -36888, -8188, -46797, 120348], ![4289, 10323, 2291, 13095, -33677]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 4 2 6 [9, 44, 71, 38, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [44, 75, 82, 83], [6, 96, 54, 31], [9, 22, 58, 80], [0, 1]]
 g := ![![[49, 61, 83, 18], [3, 19, 36], [93, 25, 62], [85, 12, 75], [15, 59, 1], []], ![[42, 67, 34, 86, 65, 46], [94, 52, 72], [43, 63, 50], [89], [17, 2, 85], [76, 56, 43, 14, 4, 69]], ![[3, 29, 96, 65, 2, 2], [37, 89, 43], [7, 39, 27], [72, 24, 50], [50, 22, 44], [3, 38, 29, 6, 26, 12]], ![[61, 37, 12, 31, 90, 78], [54, 87, 36], [83, 79, 91], [57, 29, 12], [16, 1, 27], [13, 46, 14, 51, 9, 34]]]
 h' := ![![[44, 75, 82, 83], [8, 49, 38, 42], [36, 48, 59, 6], [0, 47, 35, 16], [59, 70, 16, 47], [0, 0, 0, 1], [0, 1]], ![[6, 96, 54, 31], [74, 54, 19, 58], [12, 89, 55, 13], [37, 79, 13, 27], [16, 43, 34], [13, 5, 46, 52], [44, 75, 82, 83]], ![[9, 22, 58, 80], [43, 48, 8, 85], [52, 49, 80, 72], [42, 50, 42, 30], [60, 27, 47, 70], [92, 0, 18, 74], [6, 96, 54, 31]], ![[0, 1], [35, 43, 32, 9], [91, 8, 0, 6], [81, 18, 7, 24], [77, 54, 0, 77], [30, 92, 33, 67], [9, 22, 58, 80]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [78, 68, 45], []]
 b := ![[], [], [61, 90, 45, 58], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 4
  hpos := by decide
  P := [9, 44, 71, 38, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![567727898365995, 90352366408224, 693528825286406, 517053095699868, 1521193489479098]
  a := ![453, 153, 463, 312, 994]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-198018427472807, -469540745546028, -102627068052240, -590601025819648, 1521193489479098]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 88529281 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 33, 10, 13, 44]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![7, 33, 10, 13, 44]] 
 ![![97, 0, 0, 0, 0], ![60, 1, 0, 0, 0], ![86, 0, 1, 0, 0], ![78, 0, 0, 1, 0], ![25, 0, 0, 0, 1]] where
  M :=![![![7, 33, 10, 13, 44], ![-120, -77, -30, -44, -146], ![336, 138, 69, 106, 348], ![-720, -252, -128, -199, -652], ![96, 15, 10, 17, 55]]]
  hmulB := by decide  
  f := ![![![367, 153, 220, 155, 558]], ![![204, 85, 122, 86, 310]], ![![458, 192, 273, 192, 692]], ![![-510, -210, -320, -225, -792]], ![![319, 132, 196, 138, 491]]]
  g := ![![![-51, 33, 10, 13, 44], ![146, -77, -30, -44, -146], ![-318, 138, 69, 106, 348], ![590, -252, -128, -199, -652], ![-45, 15, 10, 17, 55]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-367, -153, -220, -155, -558]] ![![7, 33, 10, 13, 44]]
  ![![97, 0, 0, 0, 0]] where
 M := ![![![-97, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6143, 2614, 3675, 2567, 9210]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![6143, 2614, 3675, 2567, 9210]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![44, 84, 1, 0, 0], ![41, 58, 0, 1, 0], ![52, 23, 0, 0, 1]] where
  M :=![![![6143, 2614, 3675, 2567, 9210], ![-36216, -15139, -21825, -15335, -54914], ![213816, 89970, 128428, 90049, 322770], ![-1262952, -529938, -760163, -533442, -1910758], ![350736, 147060, 211192, 148238, 530915]]]
  hmulB := by decide  
  f := ![![![-58325, -37358, -15145, -22231, -73654]], ![![167064, 71017, 33821, 51769, 170202]], ![![109996, 41578, 20892, 32371, 106194]], ![![78847, 27546, 14376, 22457, 73564]], ![![7508, -3069, -143, 255, 557]]]
  g := ![![![-7324, -6602, 3675, 2567, 9210], ![43647, 39313, -21825, -15335, -54914], ![-256565, -231134, 128428, 90049, 322770], ![1518958, 1368424, -760163, -533442, -1910758], ![-422050, -380217, 211192, 148238, 530915]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [3, 99, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 100], [0, 1]]
 g := ![![[33, 84], [71], [17, 5], [100], [1], [2, 1]], ![[100, 17], [71], [27, 96], [100], [1], [4, 100]]]
 h' := ![![[2, 100], [65, 65], [50, 77], [82, 45], [33, 91], [95, 1], [0, 1]], ![[0, 1], [94, 36], [2, 24], [71, 56], [13, 10], [97, 100], [2, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [25, 76]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [3, 99, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1532401, 382068, 1550933, 1140953, 3498584]
  a := ![247, 84, 250, 171, 542]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2924892, -2738010, 1550933, 1140953, 3498584]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2059, 443, 302, 495, 1608]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![2059, 443, 302, 495, 1608]] 
 ![![101, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![85, 0, 1, 0, 0], ![64, 0, 0, 1, 0], ![25, 0, 0, 0, 1]] where
  M :=![![![2059, 443, 302, 495, 1608], ![-2952, -533, -406, -676, -2190], ![3888, 534, 489, 834, 2692], ![-4560, -324, -500, -883, -2828], ![-816, -267, -142, -225, -737]]]
  hmulB := by decide  
  f := ![![![1607, 6911, -2296, -3695, -11238]], ![![100, 413, -134, -218, -662]], ![![1399, 6085, -2035, -3265, -9934]], ![![1264, 4984, -1572, -2591, -7852]], ![![283, 1348, -472, -742, -2265]]]
  g := ![![![-963, 443, 302, 495, 1608], ![1304, -533, -406, -676, -2190], ![-1589, 534, 489, 834, 2692], ![1648, -324, -500, -883, -2828], ![447, -267, -142, -225, -737]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3071, -70, -5113, -3813, -10554]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![-3071, -70, -5113, -3813, -10554]] 
 ![![101, 0, 0, 0, 0], ![33, 1, 0, 0, 0], ![22, 0, 1, 0, 0], ![82, 0, 0, 1, 0], ![79, 0, 0, 0, 1]] where
  M :=![![![-3071, -70, -5113, -3813, -10554], ![-21240, 403, -35677, -26899, -74754], ![-142632, 5970, -243882, -184563, -512342], ![-992328, 38934, -1683263, -1274560, -3543854], ![342048, -13128, 580352, 439314, 1221265]]]
  hmulB := by decide  
  f := ![![![11939765, 1320758, 1419851, 2457529, 7910910]], ![![3773193, 428785, 451728, 780398, 2512912]], ![![2700814, 264970, 312200, 544721, 1751198]], ![![9699034, 1146130, 1172841, 2020558, 6509234]], ![![9255055, 1013614, 1097891, 1901579, 6120591]]]
  g := ![![![12457, -70, -5113, -3813, -10554], ![87739, 403, -35677, -26899, -74754], ![600346, 5970, -243882, -184563, -512342], ![4150822, 38934, -1683263, -1274560, -3543854], ![-1430655, -13128, 580352, 439314, 1221265]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2

def I101N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-25, -1, -26, -21, -66]] i)))

def SI101N3: IdealEqSpanCertificate' Table ![![-25, -1, -26, -21, -66]] 
 ![![101, 0, 0, 0, 0], ![81, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![80, 0, 0, 1, 0], ![67, 0, 0, 0, 1]] where
  M :=![![![-25, -1, -26, -21, -66], ![72, 65, -16, -20, -18], ![-1008, -246, -981, -728, -2260], ![1824, 1860, -1410, -1221, -2024], ![-360, -543, 656, 545, 1137]]]
  hmulB := by decide  
  f := ![![![-89621, -13069, -11496, -19491, -62956]], ![![-70809, -10390, -9100, -15421, -49814]], ![![-4612, -482, -541, -940, -3024]], ![![-70352, -10672, -9134, -15437, -49888]], ![![-58915, -8534, -7542, -12794, -41321]]]
  g := ![![![62, -1, -26, -21, -66], ![-23, 65, -16, -20, -18], ![2302, -246, -981, -728, -2260], ![892, 1860, -1410, -1221, -2024], ![-780, -543, 656, 545, 1137]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N3 : Nat.card (O ⧸ I101N3) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N3)

lemma isPrimeI101N3 : Ideal.IsPrime I101N3 := prime_ideal_of_norm_prime hp101.out _ NI101N3
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![6143, 2614, 3675, 2567, 9210]] ![![2059, 443, 302, 495, 1608]]
  ![![-571, -241, -343, -240, -862]] where
 M := ![![![-571, -241, -343, -240, -862]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![-571, -241, -343, -240, -862]] ![![-3071, -70, -5113, -3813, -10554]]
  ![![-891499, -132687, -1111098, -829277, -2430116]] where
 M := ![![![-891499, -132687, -1111098, -829277, -2430116]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI101N2 : IdealMulLeCertificate' Table 
  ![![-891499, -132687, -1111098, -829277, -2430116]] ![![-25, -1, -26, -21, -66]]
  ![![101, 0, 0, 0, 0]] where
 M := ![![![494961307, 42694720, 690413578, 518388560, 1487723536]]]
 hmul := by decide  
 g := ![![![![4900607, 422720, 6835778, 5132560, 14729936]]]]
 hle2 := by decide  


def PBC101 : ContainsPrimesAboveP 101 ![I101N0, I101N1, I101N2, I101N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
    exact isPrimeI101N1
    exact isPrimeI101N2
    exact isPrimeI101N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 101 (by decide) (𝕀 ⊙ MulI101N0 ⊙ MulI101N1 ⊙ MulI101N2)
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


def P103P0 : CertificateIrreducibleZModOfList' 103 5 2 6 [49, 47, 67, 10, 86, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [16, 65, 83, 90, 66], [0, 48, 67, 99, 72], [92, 50, 91, 25, 26], [12, 42, 68, 95, 42], [0, 1]]
 g := ![![[27, 6, 85, 41, 7], [48, 0, 14, 19, 68], [20, 87, 3, 13, 38], [43, 6, 62, 76], [17, 1], []], ![[66, 42, 58, 94, 48, 73, 22, 97], [89, 14, 86, 73, 24, 35, 93, 55], [50, 99, 80, 1, 59, 18, 90, 64], [70, 53, 94, 79], [2, 41, 38, 66], [17, 58, 81, 93, 84, 61, 45, 23]], ![[78, 89, 19, 86, 80, 55, 23, 50], [91, 63, 27, 92, 96, 13, 36, 79], [54, 12, 30, 77, 95, 8, 70, 82], [73, 79, 69, 28], [36, 66, 28, 4], [36, 18, 73, 99, 12, 57, 8, 79]], ![[79, 14, 43, 45, 65, 21, 54, 49], [37, 28, 69, 21, 34, 30, 6, 28], [44, 66, 97, 74, 80, 43, 68, 82], [17, 27, 21, 63], [70, 81, 52, 52], [16, 51, 55, 90, 66, 79, 13, 66]], ![[69, 66, 58, 23, 93, 27, 70, 101], [75, 74, 101, 49, 53, 54, 92, 21], [55, 96, 90, 20, 51, 101, 14, 42], [12, 90, 94, 81], [92, 24, 48, 16], [0, 36, 37, 37, 71, 53, 9, 31]]]
 h' := ![![[16, 65, 83, 90, 66], [17, 38, 102, 51, 78], [50, 73, 74, 32, 45], [34, 74, 67, 61, 48], [94, 79, 50, 72, 73], [0, 0, 0, 1], [0, 1]], ![[0, 48, 67, 99, 72], [3, 90, 58, 61, 50], [12, 102, 82, 1, 11], [48, 81, 5, 37, 39], [64, 8, 53, 86, 64], [70, 32, 77, 10, 90], [16, 65, 83, 90, 66]], ![[92, 50, 91, 25, 26], [73, 73, 76, 33, 85], [32, 9, 54, 46, 31], [56, 90, 77, 77, 2], [53, 95, 51, 67, 50], [90, 1, 66, 10, 101], [0, 48, 67, 99, 72]], ![[12, 42, 68, 95, 42], [70, 51, 52, 2, 89], [20, 79, 43, 17, 100], [40, 102, 8, 62, 15], [7, 100, 10, 7, 28], [48, 67, 92, 54, 19], [92, 50, 91, 25, 26]], ![[0, 1], [16, 57, 21, 59, 7], [14, 46, 56, 7, 19], [32, 65, 49, 72, 102], [38, 27, 42, 77, 94], [80, 3, 74, 28, 99], [12, 42, 68, 95, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [100, 45, 47, 82], [], [], []]
 b := ![[], [35, 40, 0, 37, 5], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 5
  hpos := by decide
  P := [49, 47, 67, 10, 86, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![376655582536767953, -7042225029308612, 619393121980526654, 468572598819977473, 1309113526082601037]
  a := ![232, 80, 235, 164, 509]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3656850315890951, -68371116789404, 6013525456121618, 4549248532232791, 12709840059054379]
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



lemma PB2088I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB2088I2 : PrimesBelowBoundCertificateInterval O 61 103 2088 where
  m := 9
  g := ![2, 2, 2, 4, 2, 3, 2, 4, 1]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB2088I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1]
    · exact ![I79N0, I79N1, I79N2, I79N3]
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1, I89N2]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1, I101N2, I101N3]
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
    · exact ![300763, 4489]
    · exact ![25411681, 71]
    · exact ![28398241, 73]
    · exact ![6241, 79, 79, 79]
    · exact ![47458321, 83]
    · exact ![704969, 89, 89]
    · exact ![88529281, 97]
    · exact ![10201, 101, 101, 101]
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
      exact NI89N2
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
      exact NI101N2
      exact NI101N3
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
  β := ![I71N1, I73N1, I79N1, I79N2, I79N3, I83N1, I89N1, I89N2, I97N1, I101N1, I101N2, I101N3]
  Il := ![[], [I71N1], [I73N1], [I79N1, I79N2, I79N3], [I83N1], [I89N1, I89N2], [I97N1], [I101N1, I101N2, I101N3], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
