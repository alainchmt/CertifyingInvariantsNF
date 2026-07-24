
import IdealArithmetic.Examples.NF5_1_364500000_3.RI5_1_364500000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-85, -473, 696, -772, 164]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![-85, -473, 696, -772, 164]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![0, 0, 67, 0, 0], ![0, 0, 0, 67, 0], ![53, 49, 50, 10, 1]] where
  M :=![![![-85, -473, 696, -772, 164], ![-984, -1849, 1466, 1392, -772], ![2316, 6031, -6405, 1466, 696], ![-1596, -6340, 8045, -7101, 1119], ![-4398, -4305, -794, 17556, -6405]]]
  hmulB := by decide  
  f := ![![![-3916951, 1210741, -14894, 83360, -233280]], ![![1399680, -432645, 5322, -29788, 83360]], ![![-250080, 77301, -951, 5322, -14894]], ![![-655158, 202512, -2491, 13943, -39019]], ![![-2359487, 729325, -8972, 50214, -140523]]]
  g := ![![![-131, -127, -112, -36, 164], ![596, 537, 598, 136, -772], ![-516, -419, -615, -82, 696], ![-909, -913, -715, -273, 1119], ![5001, 4620, 4768, 1218, -6405]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 4 2 6 [49, 11, 13, 16, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [57, 36, 29, 37], [28, 60, 37, 37], [33, 37, 1, 60], [0, 1]]
 g := ![![[59, 33, 6, 56], [12, 46, 56, 14], [12, 31, 49], [61, 5, 55], [1], []], ![[36, 15, 10, 51, 43, 29], [51, 12, 22, 18, 15, 22], [5, 36, 6], [18, 33, 1], [28, 38, 55], [1, 7, 29]], ![[16, 34, 14, 53, 43, 19], [28, 26, 54, 12, 0, 65], [42, 26, 33], [37, 17, 29], [19, 56, 56], [2, 63, 29]], ![[9, 61, 36, 16, 35, 15], [21, 23, 29, 10, 31, 47], [12, 62, 14], [58, 34, 24], [0, 5, 17], [23, 6, 49]]]
 h' := ![![[57, 36, 29, 37], [15, 6, 1, 49], [39, 60, 44, 58], [15, 28, 63, 7], [18, 56, 54, 51], [0, 0, 1], [0, 1]], ![[28, 60, 37, 37], [14, 3, 52, 29], [12, 57, 27, 54], [49, 0, 49, 41], [23, 38, 58, 1], [51, 65, 9, 51], [57, 36, 29, 37]], ![[33, 37, 1, 60], [25, 35, 3, 22], [58, 18, 11, 64], [21, 29, 21, 10], [62, 54, 27, 30], [16, 50, 48, 49], [28, 60, 37, 37]], ![[0, 1], [49, 23, 11, 34], [16, 66, 52, 25], [1, 10, 1, 9], [37, 53, 62, 52], [29, 19, 9, 34], [33, 37, 1, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [40, 23, 31], []]
 b := ![[], [], [9, 16, 52, 39], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 4
  hpos := by decide
  P := [49, 11, 13, 16, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![34465, 102918, 161163, -50767, 138444]
  a := ![0, -2, -1, -3, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-109001, -99714, -100911, -21421, 138444]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 20151121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3916951, -1210741, 14894, -83360, 233280]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![3916951, -1210741, 14894, -83360, 233280]] 
 ![![67, 0, 0, 0, 0], ![57, 1, 0, 0, 0], ![17, 0, 1, 0, 0], ![23, 0, 0, 1, 0], ![46, 0, 0, 0, 1]] where
  M :=![![![3916951, -1210741, 14894, -83360, 233280], ![-1399680, 432645, -5322, 29788, -83360], ![250080, -77301, 951, -5322, 14894], ![655158, -202512, 2491, -13943, 39019], ![15966, -4937, 60, -340, 951]]]
  hmulB := by decide  
  f := ![![![85, 473, -696, 772, -164]], ![![87, 430, -614, 636, -128]], ![![-13, 30, -81, 174, -52]], ![![53, 257, -359, 371, -73]], ![![124, 389, -466, 268, -17]]]
  g := ![![![953170, -1210741, 14894, -83360, 233280], ![-340605, 432645, -5322, 29788, -83360], ![60856, -77301, 951, -5322, 14894], ![159430, -202512, 2491, -13943, 39019], ![3887, -4937, 60, -340, 951]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![-85, -473, 696, -772, 164]] ![![3916951, -1210741, 14894, -83360, 233280]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -11, -27, -20, -5]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![1, -11, -27, -20, -5]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![44, 3, 1, 0, 0], ![10, 49, 0, 1, 0], ![63, 3, 0, 0, 1]] where
  M :=![![![1, -11, -27, -20, -5], ![30, 49, -52, -54, -20], ![60, 139, -24, -52, -27], ![66, 196, 56, 3, -16], ![156, 501, 205, 60, -24]]]
  hmulB := by decide  
  f := ![![![-403, 129, -7, 14, -25]], ![![150, -35, -6, -14, 14]], ![![-244, 78, -4, 8, -15]], ![![46, -5, -6, -7, 6]], ![![-351, 113, -6, 10, -21]]]
  g := ![![![24, 15, -27, -20, -5], ![58, 41, -52, -54, -20], ![47, 40, -24, -52, -27], ![-20, -1, 56, 3, -16], ![-112, -42, 205, 60, -24]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [54, 45, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 70], [0, 1]]
 g := ![![[60, 25], [55, 54], [], [], [37], [1]], ![[0, 46], [39, 17], [], [], [37], [1]]]
 h' := ![![[26, 70], [12, 5], [0, 57], [25], [66], [17, 26], [0, 1]], ![[0, 1], [0, 66], [62, 14], [25], [66], [54, 45], [26, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50]]
 b := ![[], [30, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [54, 45, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![948, 3843, -31455, 20280, 3601]
  a := ![3, -65, 1, -66, 1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![13455, -12765, -31455, 20280, 3601]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -5, -2, -4, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-1, -5, -2, -4, 0]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![48, 9, 1, 0, 0], ![65, 50, 0, 1, 0], ![5, 26, 0, 0, 1]] where
  M :=![![![-1, -5, -2, -4, 0], ![0, -3, -6, -4, -4], ![12, 27, -21, -6, -2], ![6, 12, 23, -19, -1], ![18, 71, 12, 40, -21]]]
  hmulB := by decide  
  f := ![![![-6383, 1973, -24, 136, -380]], ![![2280, -707, 10, -48, 136]], ![![-4032, 1246, -15, 86, -240]], ![![-4253, 1313, -15, 91, -253]], ![![385, -120, 2, -8, 23]]]
  g := ![![![5, 3, -2, -4, 0], ![8, 5, -6, -4, -4], ![20, 8, -21, -6, -2], ![2, 11, 23, -19, -1], ![-43, -21, 12, 40, -21]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P1 : CertificateIrreducibleZModOfList' 71 2 2 6 [57, 45, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 70], [0, 1]]
 g := ![![[12, 5], [9, 57], [16, 54], [54], [37], [1]], ![[0, 66], [0, 14], [0, 17], [54], [37], [1]]]
 h' := ![![[26, 70], [55, 17], [11, 46], [62, 14], [4, 57], [14, 26], [0, 1]], ![[0, 1], [0, 54], [0, 25], [0, 57], [66, 14], [51, 45], [26, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45]]
 b := ![[], [27, 58]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N1 : CertifiedPrimeIdeal' SI71N1 71 where
  n := 2
  hpos := by decide
  P := [57, 45, 1]
  hirr := P71P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![55, -361, -133, -266, 3]
  a := ![1, -4, 0, -5, -1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![334, 198, -133, -266, 3]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N1 B_one_repr
lemma NI71N1 : Nat.card (O ⧸ I71N1) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![40213, -12430, 153, -856, 2395]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![40213, -12430, 153, -856, 2395]] 
 ![![71, 0, 0, 0, 0], ![47, 1, 0, 0, 0], ![67, 0, 1, 0, 0], ![35, 0, 0, 1, 0], ![55, 0, 0, 0, 1]] where
  M :=![![![40213, -12430, 153, -856, 2395], ![-14370, 4441, -54, 306, -856], ![2568, -792, 8, -54, 153], ![6726, -2080, 27, -145, 401], ![162, -54, 3, 0, 8]]]
  hmulB := by decide  
  f := ![![![-535, -1296, 111, 382, 223]], ![![-373, -911, 63, 256, 153]], ![![-521, -1278, 77, 350, 212]], ![![-259, -646, 18, 159, 102]], ![![-383, -972, -6, 212, 145]]]
  g := ![![![7217, -12430, 153, -856, 2395], ![-2579, 4441, -54, 306, -856], ![461, -792, 8, -54, 153], ![1207, -2080, 27, -145, 401], ![29, -54, 3, 0, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![1, -11, -27, -20, -5]] ![![-1, -5, -2, -4, 0]]
  ![![-535, -1296, 111, 382, 223]] where
 M := ![![![-535, -1296, 111, 382, 223]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![-535, -1296, 111, 382, 223]] ![![40213, -12430, 153, -856, 2395]]
  ![![71, 0, 0, 0, 0]] where
 M := ![![![71, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0, 0, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0, 0, 0]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![0, 0, 0, 73, 0], ![0, 0, 0, 0, 73]] where
  M :=![![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![0, 0, 0, 73, 0], ![0, 0, 0, 0, 73]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 5 2 6 [37, 38, 6, 51, 66, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 30, 33, 35, 51], [22, 46, 32, 58, 54], [47, 12, 21, 33, 17], [66, 57, 60, 20, 24], [0, 1]]
 g := ![![[37, 46, 42, 2, 16], [35, 38, 51, 1], [4, 60, 63, 67], [11, 61, 71, 7, 1], [], []], ![[66, 7, 0, 20, 37, 55, 45, 66], [4, 51, 36, 36], [4, 36, 1, 71], [12, 67, 68, 54, 0, 63, 72, 14], [52, 7, 18, 25], [31, 70, 23, 46]], ![[67, 25, 64, 63, 6, 26, 68, 70], [45, 30, 25, 64], [33, 51, 60, 24], [32, 30, 15, 52, 40, 36, 44, 61], [10, 41, 57, 48], [67, 14, 31, 69]], ![[40, 10, 3, 28, 11, 16, 21, 60], [12, 64, 58, 71], [7, 14, 23, 72], [64, 67, 55, 43, 37, 20, 69, 53], [60, 8, 48, 57], [16, 27, 6, 70]], ![[31, 68, 49, 61, 68, 28, 50, 64], [30, 32, 59, 23], [36, 18, 55, 12], [39, 30, 3, 41, 65, 3, 63, 9], [49, 37, 35, 2], [65, 15, 28, 65]]]
 h' := ![![[18, 30, 33, 35, 51], [46, 22, 59, 32, 69], [10, 43, 62, 22, 1], [31, 26, 26, 58, 33], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[22, 46, 32, 58, 54], [46, 70, 9, 66, 17], [62, 7, 18, 55, 6], [65, 30, 16, 28, 12], [9, 19, 67, 43, 58], [53, 13, 70, 50, 5], [18, 30, 33, 35, 51]], ![[47, 12, 21, 33, 17], [32, 12, 14, 72, 2], [23, 33, 2, 31, 65], [52, 60, 48, 31, 43], [60, 62, 41, 37, 69], [49, 55, 56, 16, 62], [22, 46, 32, 58, 54]], ![[66, 57, 60, 20, 24], [6, 52, 22, 51, 68], [31, 4, 28, 70, 61], [12, 45, 37, 33, 27], [18, 26, 63, 63, 69], [11, 32, 44, 29, 38], [47, 12, 21, 33, 17]], ![[0, 1], [21, 63, 42, 71, 63], [6, 59, 36, 41, 13], [30, 58, 19, 69, 31], [47, 39, 48, 3, 22], [53, 46, 48, 51, 41], [66, 57, 60, 20, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22, 32, 35, 55], [], [], []]
 b := ![[], [40, 18, 55, 3, 39], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 5
  hpos := by decide
  P := [37, 38, 6, 51, 66, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-516497411, 429342346, 4051448462, 2474172064, -633680734]
  a := ![1, 18, 1, 17, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7075307, 5881402, 55499294, 33892768, -8680558]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0, 0, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0, 0, 0]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![0, 0, 0, 79, 0], ![0, 0, 0, 0, 79]] where
  M :=![![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![0, 0, 0, 79, 0], ![0, 0, 0, 0, 79]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 5 2 6 [17, 2, 8, 67, 40, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 70, 3, 38, 11], [3, 41, 77, 6, 23], [71, 23, 35, 37, 13], [33, 23, 43, 77, 32], [0, 1]]
 g := ![![[4, 4, 25, 63, 73], [52, 3, 3, 21, 32], [40, 0, 28, 76, 9], [6, 49, 32, 39, 1], [], []], ![[36, 1, 19, 1, 26, 44, 62, 45], [44, 38, 11, 20, 31, 9, 32, 9], [5, 11, 2, 7, 38, 14, 54, 36], [61, 70, 56, 23, 2, 17, 34, 67], [12, 11, 46, 23], [40, 66, 25, 42]], ![[65, 67, 23, 78, 63, 58, 8, 76], [20, 75, 71, 76, 18, 53, 58, 18], [47, 11, 27, 62, 56, 70, 48, 72], [56, 20, 70, 25, 50, 21, 26, 46], [25, 14, 33, 36], [66, 65, 51, 55]], ![[6, 36, 17, 11, 22, 22, 57, 32], [45, 40, 2, 49, 2, 37, 55, 10], [0, 23, 14, 30, 4, 67, 27, 18], [75, 58, 40, 34, 29, 62, 53, 45], [40, 44, 68, 64], [73, 17, 48, 11]], ![[11, 29, 26, 43, 21, 32, 68, 40], [72, 3, 36, 31, 16, 50, 24, 64], [75, 38, 74, 44, 43, 29, 20, 45], [15, 34, 72, 46, 7, 11, 70, 49], [36, 47, 65, 22], [24, 38, 71, 76]]]
 h' := ![![[11, 70, 3, 38, 11], [64, 16, 31, 61, 51], [31, 54, 75, 6, 36], [56, 24, 21, 59, 76], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[3, 41, 77, 6, 23], [39, 58, 29, 25, 44], [45, 7, 38, 70, 61], [63, 62, 16, 19, 43], [69, 78, 49, 45, 68], [73, 22, 60, 49, 55], [11, 70, 3, 38, 11]], ![[71, 23, 35, 37, 13], [47, 49, 21, 77, 54], [45, 63, 20, 28, 68], [52, 59, 62, 30, 22], [19, 77, 71, 23, 70], [72, 36, 65, 55, 73], [3, 41, 77, 6, 23]], ![[33, 23, 43, 77, 32], [54, 51, 73, 31, 19], [37, 51, 6, 72, 63], [74, 25, 53, 63, 45], [16, 70, 50, 1, 21], [8, 66, 36, 53, 71], [71, 23, 35, 37, 13]], ![[0, 1], [43, 63, 4, 43, 69], [6, 62, 19, 61, 9], [21, 67, 6, 66, 51], [51, 12, 67, 10, 77], [49, 34, 75, 1, 38], [33, 23, 43, 77, 32]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57, 6, 21, 2], [], [], []]
 b := ![[], [70, 44, 68, 60, 7], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 5
  hpos := by decide
  P := [17, 2, 8, 67, 40, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4442212739, -12967434934, 14569164990, -6699842270, -271279680]
  a := ![-1, 2, 1, 4, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-56230541, -164144746, 184419810, -84808130, -3433920]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 3077056399 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def PBC79 : ContainsPrimesAboveP 79 ![I79N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![79, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 79 (by decide) 𝕀

instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8009, -54316, -144401, -108140, -27259]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![8009, -54316, -144401, -108140, -27259]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![0, 0, 0, 83, 0], ![51, 65, 54, 78, 1]] where
  M :=![![![8009, -54316, -144401, -108140, -27259], ![163554, 272493, -273082, -288802, -108140], ![324420, 756286, -123806, -273082, -144401], ![351426, 1047068, 307363, 20595, -82471], ![819246, 2652140, 1125025, 341644, -123806]]]
  hmulB := by decide  
  f := ![![![-29493918119, 9116656562, -112148375, 627685930, -1756555219]], ![![10539331314, -3257738209, 40075004, -224296750, 627685930]], ![![-1883057790, 582058684, -7160184, 40075004, -112148375]], ![![-4933220532, 1524872930, -18758195, 104988191, -293805463]], ![![-15731684769, 4862709885, -59818532, 334799776, -936924449]]]
  g := ![![![16846, 20693, 15995, 24314, -27259], ![68418, 87971, 67066, 98146, -108140], ![92637, 122197, 92456, 132412, -144401], ![54909, 77201, 57359, 77751, -82471], ![85944, 128910, 94103, 120464, -123806]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 4 2 6 [13, 49, 21, 13, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 38, 28, 6], [78, 58, 50, 25], [71, 69, 5, 52], [0, 1]]
 g := ![![[38, 57, 48, 64], [24, 64, 45, 38], [3, 51, 9], [54, 8, 75], [70, 1], []], ![[74, 56, 19, 68, 29, 20], [58, 9, 38, 4, 11, 56], [78, 39, 64], [64, 64, 11], [33, 56, 18, 75, 72, 35], [42, 34, 36]], ![[1, 52, 68, 29, 12, 9], [18, 19, 65, 60, 40, 38], [60, 78, 25], [33, 10, 11], [6, 37, 32, 7, 0, 41], [79, 19, 44]], ![[10, 46, 41, 60, 76, 6], [50, 35, 56, 33, 29, 8], [77, 75, 36], [31, 73, 75], [58, 0, 34, 46, 69, 13], [75, 62, 48]]]
 h' := ![![[4, 38, 28, 6], [20, 21, 28, 75], [55, 53, 17, 72], [54, 81, 28, 3], [3, 43, 58, 65], [0, 0, 1], [0, 1]], ![[78, 58, 50, 25], [54, 25, 80, 23], [77, 77, 12, 55], [57, 27, 70, 8], [15, 64, 78, 54], [51, 45, 63, 65], [4, 38, 28, 6]], ![[71, 69, 5, 52], [38, 51, 71, 16], [57, 44, 23, 31], [67, 67, 51, 78], [74, 56, 47, 29], [77, 33, 34, 59], [78, 58, 50, 25]], ![[0, 1], [13, 69, 70, 52], [16, 75, 31, 8], [41, 74, 17, 77], [64, 3, 66, 18], [82, 5, 68, 42], [71, 69, 5, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [60, 9, 66], []]
 b := ![[], [], [23, 27, 37, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 4
  hpos := by decide
  P := [13, 49, 21, 13, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![49926661, 162433694, -189392502, 121054948, -9507606]
  a := ![0, -10, 2, -20, 2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![6443549, 9402748, 3903834, 10393352, -9507606]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 47458321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29493918119, -9116656562, 112148375, -627685930, 1756555219]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![29493918119, -9116656562, 112148375, -627685930, 1756555219]] 
 ![![83, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![29, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![72, 0, 0, 0, 1]] where
  M :=![![![29493918119, -9116656562, 112148375, -627685930, 1756555219], ![-10539331314, 3257738209, -40075004, 224296750, -627685930], ![1883057790, -582058684, 7160184, -40075004, 112148375], ![4933220532, -1524872930, 18758195, -104988191, 293805463], ![120225012, -37161902, 457145, -2558614, 7160184]]]
  hmulB := by decide  
  f := ![![![-8009, 54316, 144401, 108140, 27259]], ![![-2453, -11, 11989, 9994, 2945]], ![![-6707, 9866, 51945, 41074, 11264]], ![![-5006, -7380, 10215, 10175, 3621]], ![![-16818, 15164, 111709, 89692, 25138]]]
  g := ![![![-597898678, -9116656562, 112148375, -627685930, 1756555219], ![213652599, 3257738209, -40075004, 224296750, -627685930], ![-38173218, -582058684, 7160184, -40075004, 112148375], ![-100005907, -1524872930, 18758195, -104988191, 293805463], ![-2437193, -37161902, 457145, -2558614, 7160184]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![8009, -54316, -144401, -108140, -27259]] ![![29493918119, -9116656562, 112148375, -627685930, 1756555219]]
  ![![83, 0, 0, 0, 0]] where
 M := ![![![-83, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5903, 11897, -10132, -6110, 4200]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![5903, 11897, -10132, -6110, 4200]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![28, 12, 81, 1, 0], ![3, 34, 73, 0, 1]] where
  M :=![![![5903, 11897, -10132, -6110, 4200], ![-25200, -67229, 71904, -20264, -6110], ![18330, 69177, -87647, 71904, -10132], ![42996, 74946, -53387, -77515, 39007], ![-215712, -526319, 529830, -34870, -87647]]]
  hmulB := by decide  
  f := ![![![29478931, -9112035, 112090, -627366, 1755664]], ![![-10533984, 3256061, -40064, 224180, -627366]], ![![1882098, -581779, 7141, -40064, 112090]], ![![9622280, -2974297, 36572, -204789, 573069]], ![![-1485453, 459135, -5665, 31604, -88469]]]
  g := ![![![1847, -647, 2002, -6110, 4200], ![6298, 4311, 24262, -20264, -6110], ![-22074, -5047, -58115, 71904, -10132], ![23555, -3608, 37953, -77515, 39007], ![11501, 32271, 109579, -34870, -87647]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [70, 42, 43, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [58, 41, 69], [77, 47, 20], [0, 1]]
 g := ![![[78, 82, 8], [72, 80], [20, 73], [75, 25, 79], [27, 46, 1], []], ![[32, 38, 3, 21], [81, 84], [12, 18], [16, 22, 67, 88], [77, 25, 20, 53], [28, 44]], ![[45, 80, 15, 84], [73, 11], [45, 21], [43, 68, 1, 67], [7, 67, 77, 67], [77, 44]]]
 h' := ![![[58, 41, 69], [35, 26, 39], [25, 84, 76], [1, 80, 47], [68, 7, 41], [0, 0, 1], [0, 1]], ![[77, 47, 20], [51, 7, 67], [84, 59, 23], [52, 80, 75], [10, 50, 7], [69, 55, 47], [58, 41, 69]], ![[0, 1], [7, 56, 72], [20, 35, 79], [77, 18, 56], [11, 32, 41], [5, 34, 41], [77, 47, 20]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31, 31], []]
 b := ![[], [47, 9, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [70, 42, 43, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-99042, -286238, 259535, -54926, -44967]
  a := ![13, 0, 1, 1, -4]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![17683, 21368, 89788, -54926, -44967]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 704969 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![26027, 78608, 24806, 3004, -5764]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![26027, 78608, 24806, 3004, -5764]] 
 ![![89, 0, 0, 0, 0], ![19, 1, 0, 0, 0], ![42, 0, 1, 0, 0], ![81, 0, 0, 1, 0], ![16, 0, 0, 0, 1]] where
  M :=![![![26027, 78608, 24806, 3004, -5764], ![34584, 137293, 96572, 49612, 3004], ![-9012, 43048, 127507, 96572, 24806], ![-91710, -195444, 70506, 102701, 46784], ![-289716, -679916, 101758, 237584, 127507]]]
  hmulB := by decide  
  f := ![![![-10722168430997, 3314253697680, -40770227982, 228187866948, -638575073024]], ![![-2245952244391, 694230423509, -8540062174, 47798078832, -133761106972]], ![![-5067591434862, 1566407369872, -19269130069, 107847856292, -301808126910]], ![![-9778528735347, 3022571901156, -37182109984, 208105443257, -582375173588]], ![![-1928071924612, 595972684692, -7331346494, 41032989048, -114829260329]]]
  g := ![![![-29893, 78608, 24806, 3004, -5764], ![-120187, 137293, 96572, 49612, 3004], ![-161814, 43048, 127507, 96572, 24806], ![-94459, -195444, 70506, 102701, 46784], ![-145276, -679916, 101758, 237584, 127507]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1

def I89N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![66571, -41107, 34716, -55010, 17408]] i)))

def SI89N2: IdealEqSpanCertificate' Table ![![66571, -41107, 34716, -55010, 17408]] 
 ![![89, 0, 0, 0, 0], ![86, 1, 0, 0, 0], ![40, 0, 1, 0, 0], ![17, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![66571, -41107, 34716, -55010, 17408], ![-104448, -159833, 146876, 69432, -55010], ![165030, 433789, -469599, 146876, 34716], ![-51924, -332738, 460493, -504315, 100943], ![-440628, -671787, 378670, 1067862, -469599]]]
  hmulB := by decide  
  f := ![![![151747247, 289581289, -182166718, -216890986, -88386000]], ![![152590778, 294374847, -177012856, -213673688, -87843674]], ![![75511942, 150912233, -77456027, -98465684, -41770862]], ![![32146577, 69250839, -23280047, -34965143, -16157525]], ![![6369818, 31069863, 28986608, 17171142, 2430453]]]
  g := ![![![34983, -41107, 34716, -55010, 17408], ![75234, -159833, 146876, 69432, -55010], ![-235092, 433789, -469599, 146876, 34716], ![208037, -332738, 460493, -504315, 100943], ![280582, -671787, 378670, 1067862, -469599]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N2 : Nat.card (O ⧸ I89N2) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N2)

lemma isPrimeI89N2 : Ideal.IsPrime I89N2 := prime_ideal_of_norm_prime hp89.out _ NI89N2
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![5903, 11897, -10132, -6110, 4200]] ![![26027, 78608, 24806, 3004, -5764]]
  ![![-66287, -248851, 37918, -151238, 58464]] where
 M := ![![![-66287, -248851, 37918, -151238, 58464]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![-66287, -248851, 37918, -151238, 58464]] ![![66571, -41107, 34716, -55010, 17408]]
  ![![89, 0, 0, 0, 0]] where
 M := ![![![9928811431, 69995147370, -104163191304, 130640545344, -28869322668]]]
 hmul := by decide  
 g := ![![![![111559679, 786462330, -1170372936, 1467871296, -324374412]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0, 0, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0, 0, 0]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![0, 0, 0, 97, 0], ![0, 0, 0, 0, 97]] where
  M :=![![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![0, 0, 0, 97, 0], ![0, 0, 0, 0, 97]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 5 2 6 [96, 87, 65, 11, 43, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [83, 22, 84, 87, 19], [87, 88, 40, 13, 15], [40, 62, 84, 6, 75], [38, 21, 83, 88, 85], [0, 1]]
 g := ![![[83, 0, 20, 39, 95], [25, 46, 62, 93], [8, 90, 65, 43], [2, 31, 83, 25], [54, 1], []], ![[7, 67, 34, 23, 76, 87, 59, 21], [32, 89, 72, 65], [66, 16, 45, 96], [20, 92, 4, 91], [2, 4, 51, 8], [30, 72, 90, 41, 89, 96, 74, 69]], ![[96, 29, 84, 87, 19, 8, 47, 92], [2, 56, 94, 27], [75, 39, 45, 93], [44, 7, 69, 4], [73, 85, 54, 64], [17, 79, 88, 96, 35, 81, 32, 77]], ![[78, 70, 48, 21, 7, 66, 76, 47], [18, 77, 6, 43], [4, 11, 35, 33], [88, 8, 89, 16], [51, 5, 18, 32], [40, 23, 41, 22, 65, 73, 6, 22]], ![[34, 80, 19, 23, 48, 89, 0, 18], [68, 39, 49, 70], [87, 25, 77, 91], [4, 11, 17, 72], [85, 28, 20, 35], [17, 6, 36, 12, 23, 20, 91, 18]]]
 h' := ![![[83, 22, 84, 87, 19], [68, 38, 77, 30, 17], [72, 75, 21, 23, 44], [8, 85, 13, 82, 72], [54, 56, 89, 20, 92], [0, 0, 0, 1], [0, 1]], ![[87, 88, 40, 13, 15], [33, 58, 15, 19, 44], [1, 67, 68, 21, 29], [56, 37, 11, 22, 75], [6, 3, 80, 23, 24], [2, 19, 85, 85, 28], [83, 22, 84, 87, 19]], ![[40, 62, 84, 6, 75], [5, 40, 94, 50, 56], [87, 60, 56, 29, 30], [20, 23, 24, 29, 53], [48, 36, 6, 61, 95], [84, 71, 31, 55, 89], [87, 88, 40, 13, 15]], ![[38, 21, 83, 88, 85], [22, 63, 47, 9, 89], [2, 0, 86, 89, 72], [80, 50, 2, 35, 18], [63, 38, 38, 12, 93], [20, 39, 15, 17, 41], [40, 62, 84, 6, 75]], ![[0, 1], [24, 92, 58, 86, 85], [21, 89, 60, 32, 19], [15, 96, 47, 26, 73], [60, 61, 78, 78, 84], [84, 65, 63, 36, 36], [38, 21, 83, 88, 85]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [91, 60, 78, 86], [], [], []]
 b := ![[], [35, 4, 15, 88, 21], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 5
  hpos := by decide
  P := [96, 87, 65, 11, 43, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11908593, -35292480, 39681439, -19339569, -349103]
  a := ![-1, -4, 1, -5, 1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-122769, -363840, 409087, -199377, -3599]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25909, 121078, 107642, 62484, 8166]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![25909, 121078, 107642, 62484, 8166]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![0, 0, 0, 101, 0], ![84, 62, 42, 36, 1]] where
  M :=![![![25909, 121078, 107642, 62484, 8166], ![-48996, 11061, 261332, 215284, 62484], ![-187452, -362462, 215839, 261332, 107642], ![-298428, -798652, -85584, 108197, 99424], ![-783996, -2237834, -495422, 90164, 215839]]]
  hmulB := by decide  
  f := ![![![1385, -390, 6, -140, 122]], ![![-732, -439, 580, 12, -140]], ![![420, 974, -1145, 580, 6]], ![![348, -188, 424, -1151, 360]], ![![984, -292, 68, -264, 135]]]
  g := ![![![-6535, -3814, -2330, -2292, 8166], ![-52452, -38247, -23396, -20140, 62484], ![-91380, -69666, -42625, -35780, 107642], ![-85644, -68940, -42192, -34367, 99424], ![-187272, -154652, -94660, -76040, 215839]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 4 2 6 [20, 74, 100, 10, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [82, 85, 54, 34], [62, 85, 13, 84], [48, 31, 34, 84], [0, 1]]
 g := ![![[6, 38, 39, 19], [91, 63, 43], [12, 18, 75, 68], [24, 77, 87], [0, 91, 1], []], ![[94, 49, 29, 24, 39, 59], [53, 92, 97], [54, 21, 31, 38, 14, 53], [94, 46, 68], [70, 48, 4], [68, 67, 22, 71, 70, 15]], ![[56, 78, 66, 0, 90, 82], [28, 20, 45], [26, 84, 21, 35, 31, 5], [45, 19, 31], [70, 63, 37], [62, 28, 93, 38, 3, 36]], ![[67, 12, 39, 65, 48, 70], [60, 55, 13], [90, 47, 2, 52, 94, 16], [6, 80, 6], [35, 6, 80], [2, 18, 96, 78, 30, 36]]]
 h' := ![![[82, 85, 54, 34], [28, 65, 47, 25], [63, 84, 50, 12], [25, 17, 64, 13], [0, 99, 13, 17], [0, 0, 0, 1], [0, 1]], ![[62, 85, 13, 84], [6, 85, 22, 50], [37, 64, 72, 20], [56, 70, 3, 19], [44, 88, 42, 88], [63, 35, 79, 99], [82, 85, 54, 34]], ![[48, 31, 34, 84], [65, 45, 26, 66], [25, 16, 99, 34], [89, 81, 80, 24], [79, 86, 96, 58], [41, 18, 45, 80], [62, 85, 13, 84]], ![[0, 1], [26, 7, 6, 61], [69, 38, 82, 35], [11, 34, 55, 45], [38, 30, 51, 39], [58, 48, 78, 22], [48, 31, 34, 84]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [59, 67, 34], []]
 b := ![[], [], [38, 65, 73, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 4
  hpos := by decide
  P := [20, 74, 100, 10, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![986711, 1016798, -101888, -3709106, 1389205]
  a := ![3, -4, 7, -8, 0]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1145609, -842712, -578698, -531886, 1389205]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 104060401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1385, -390, 6, -140, 122]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![1385, -390, 6, -140, 122]] 
 ![![101, 0, 0, 0, 0], ![65, 1, 0, 0, 0], ![59, 0, 1, 0, 0], ![70, 0, 0, 1, 0], ![54, 0, 0, 0, 1]] where
  M :=![![![1385, -390, 6, -140, 122], ![-732, -439, 580, 12, -140], ![420, 974, -1145, 580, 6], ![348, -188, 424, -1151, 360], ![-1740, -3654, 3230, 1428, -1145]]]
  hmulB := by decide  
  f := ![![![25909, 121078, 107642, 62484, 8166]], ![![16189, 78031, 71862, 42344, 5874]], ![![13279, 67140, 65017, 39088, 5836]], ![![15002, 76008, 73756, 44377, 6644]], ![![6090, 42578, 52646, 34300, 6503]]]
  g := ![![![293, -390, 6, -140, 122], ![3, -439, 580, 12, -140], ![-359, 974, -1145, 580, 6], ![482, -188, 424, -1151, 360], ![70, -3654, 3230, 1428, -1145]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![25909, 121078, 107642, 62484, 8166]] ![![1385, -390, 6, -140, 122]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-841, -1958, 341, 724, 379]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![-841, -1958, 341, 724, 379]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![76, 83, 1, 0, 0], ![78, 102, 0, 1, 0], ![22, 18, 0, 0, 1]] where
  M :=![![![-841, -1958, 341, 724, 379], ![-2274, -6185, -850, 682, 724], ![-2172, -6992, -2906, -850, 341], ![114, -2004, -4437, -3247, -787], ![2550, 490, -11537, -9724, -2906]]]
  hmulB := by decide  
  f := ![![![515, 1012, -909, -378, 315]], ![![-1890, -5119, 5552, -1818, -378]], ![![-1132, -3333, 3744, -1690, -81]], ![![-1446, -4236, 4757, -2137, -107]], ![![-382, -1082, 1189, -450, -58]]]
  g := ![![![-889, -1077, 341, 724, 379], ![-66, -177, -850, 682, 724], ![2694, 3056, -2906, -850, 341], ![5902, 6909, -4437, -3247, -787], ![16522, 19439, -11537, -9724, -2906]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [66, 41, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [62, 102], [0, 1]]
 g := ![![[49, 64], [20, 29], [100, 56], [82], [59], [62, 1]], ![[0, 39], [67, 74], [70, 47], [82], [59], [21, 102]]]
 h' := ![![[62, 102], [19, 8], [95, 21], [35, 46], [83, 59], [28, 70], [0, 1]], ![[0, 1], [0, 95], [58, 82], [3, 57], [33, 44], [42, 33], [62, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [14, 66]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [66, 41, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-186, -729, 548, -64, -36]
  a := ![1, 0, -1, -1, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-350, -379, 548, -64, -36]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-394049635, 121801898, -1498343, 8386112, -23468225]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![-394049635, 121801898, -1498343, 8386112, -23468225]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![100, 81, 1, 0, 0], ![37, 30, 0, 1, 0], ![74, 99, 0, 0, 1]] where
  M :=![![![-394049635, 121801898, -1498343, 8386112, -23468225], ![140809350, -43524603, 535434, -2996686, 8386112], ![-25158336, 7776552, -95700, 535434, -1498343], ![-65909646, 20372856, -250597, 1402643, -3925339], ![-1606302, 496394, -6021, 34240, -95700]]]
  hmulB := by decide  
  f := ![![![-72439, -271392, -170937, -81442, -1037]], ![![6222, -227821, -471712, -341874, -81442]], ![![-63064, -438977, -541422, -352502, -66713]], ![![-19261, -151360, -198844, -131677, -25988]], ![![-32324, -376965, -571835, -391784, -83530]]]
  g := ![![![11477157, 22475132, -1498343, 8386112, -23468225], ![-4101252, -8031255, 535434, -2996686, 8386112], ![732796, 1434963, -95700, 535434, -1498343], ![1919683, 3759228, -250597, 1402643, -3925339], ![46706, 91565, -6021, 34240, -95700]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P1 : CertificateIrreducibleZModOfList' 103 2 2 6 [50, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [101, 102], [0, 1]]
 g := ![![[33, 68], [60, 30], [88, 100], [13], [56], [101, 1]], ![[0, 35], [0, 73], [94, 3], [13], [56], [99, 102]]]
 h' := ![![[101, 102], [90, 45], [29, 66], [68, 93], [93, 61], [100, 57], [0, 1]], ![[0, 1], [0, 58], [0, 37], [88, 10], [74, 42], [89, 46], [101, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [82]]
 b := ![[], [41, 41]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N1 : CertifiedPrimeIdeal' SI103N1 103 where
  n := 2
  hpos := by decide
  P := [50, 2, 1]
  hirr := P103P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![86, 44, -60, 40, 1]
  a := ![4, 1, -1, 2, 0]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![44, 35, -60, 40, 1]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N1 B_one_repr
lemma NI103N1 : Nat.card (O ⧸ I103N1) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N1

def I103N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, -2, -32, -22, 2]] i)))

def SI103N2: IdealEqSpanCertificate' Table ![![5, -2, -32, -22, 2]] 
 ![![103, 0, 0, 0, 0], ![84, 1, 0, 0, 0], ![77, 0, 1, 0, 0], ![20, 0, 0, 1, 0], ![45, 0, 0, 0, 1]] where
  M :=![![![5, -2, -32, -22, 2], ![-12, -57, 38, -64, -22], ![66, 178, -135, 38, -32], ![102, 234, -20, -103, 30], ![-114, -190, 736, -2, -135]]]
  hmulB := by decide  
  f := ![![![1215329003, -375661758, 4621196, -25864482, 72380770]], ![![986925744, -305061641, 3752710, -21003632, 58777866]], ![![909300259, -281067376, 3457545, -19351616, 54154762]], ![![237959794, -73554070, 904824, -5064231, 14172058]], ![![531017079, -164138936, 2019152, -11301040, 31625531]]]
  g := ![![![29, -2, -32, -22, 2], ![40, -57, 38, -64, -22], ![-37, 178, -135, 38, -32], ![-168, 234, -20, -103, 30], ![-337, -190, 736, -2, -135]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N2 : Nat.card (O ⧸ I103N2) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N2)

lemma isPrimeI103N2 : Ideal.IsPrime I103N2 := prime_ideal_of_norm_prime hp103.out _ NI103N2
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![-841, -1958, 341, 724, 379]] ![![-394049635, 121801898, -1498343, 8386112, -23468225]]
  ![![-1215329003, 375661758, -4621196, 25864482, -72380770]] where
 M := ![![![-1215329003, 375661758, -4621196, 25864482, -72380770]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI103N1 : IdealMulLeCertificate' Table 
  ![![-1215329003, 375661758, -4621196, 25864482, -72380770]] ![![5, -2, -32, -22, 2]]
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


lemma PB1189I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB1189I2 : PrimesBelowBoundCertificateInterval O 61 103 1189 where
  m := 9
  g := ![2, 3, 1, 1, 2, 3, 1, 2, 3]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB1189I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1, I71N2]
    · exact ![I73N0]
    · exact ![I79N0]
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1, I89N2]
    · exact ![I97N0]
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
    · exact ![20151121, 67]
    · exact ![5041, 5041, 71]
    · exact ![2073071593]
    · exact ![3077056399]
    · exact ![47458321, 83]
    · exact ![704969, 89, 89]
    · exact ![8587340257]
    · exact ![104060401, 101]
    · exact ![10609, 10609, 103]
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
      exact NI71N2
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
      exact NI103N2
  β := ![I67N1, I71N2, I83N1, I89N1, I89N2, I101N1, I103N2]
  Il := ![[I67N1], [I71N2], [], [], [I83N1], [I89N1, I89N2], [], [I101N1], [I103N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
