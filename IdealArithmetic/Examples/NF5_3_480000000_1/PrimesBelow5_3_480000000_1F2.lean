
import IdealArithmetic.Examples.NF5_3_480000000_1.RI5_3_480000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, -2, 72, 56, 8]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![167, -2, 72, 56, 8]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![13, 38, 1, 0, 0], ![42, 37, 0, 1, 0], ![37, 52, 0, 0, 1]] where
  M :=![![![167, -2, 72, 56, 8], ![64, 223, -116, 144, 176], ![704, 342, 79, 428, 304], ![1184, 826, -28, 857, 706], ![2768, 1854, -16, 1962, 1589]]]
  hmulB := by decide  
  f := ![![![5, 246, 336, -8, -88]], ![![-704, -91, 508, 64, -112]], ![![-405, -10, 351, 36, -80]], ![![-378, 101, 480, 29, -114]], ![![-541, 64, 576, 46, -135]]]
  g := ![![![-51, -78, 72, 56, 8], ![-164, -147, -116, 144, 176], ![-441, -512, 79, 428, 304], ![-904, -993, -28, 857, 706], ![-2063, -2280, -16, 1962, 1589]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [28, 39, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 66], [0, 1]]
 g := ![![[66, 14], [6, 25], [49], [55], [47], [1]], ![[56, 53], [36, 42], [49], [55], [47], [1]]]
 h' := ![![[28, 66], [33, 58], [56, 62], [17, 60], [4, 16], [39, 28], [0, 1]], ![[0, 1], [49, 9], [50, 5], [22, 7], [50, 51], [19, 39], [28, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65]]
 b := ![[], [14, 66]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [28, 39, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1428, 1104, -177, 689, 1718]
  a := ![0, 1, 1, 0, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1325, -1597, -177, 689, 1718]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-33, 0, -12, -2, 4]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![-33, 0, -12, -2, 4]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![49, 53, 1, 0, 0], ![16, 30, 0, 1, 0], ![63, 40, 0, 0, 1]] where
  M :=![![![-33, 0, -12, -2, 4], ![32, -23, 4, 6, -2], ![-8, 10, -29, -6, 8], ![16, 16, 14, -1, -4], ![0, 8, -2, -2, 1]]]
  hmulB := by decide  
  f := ![![![-3, 0, 0, -2, 4]], ![![32, 19, 4, 30, -2]], ![![23, 15, 3, 22, 2]], ![![16, 10, 2, 15, 0]], ![![17, 12, 2, 16, 5]]]
  g := ![![![5, 8, -12, -2, 4], ![-2, -5, 4, 6, -2], ![15, 21, -29, -6, 8], ![-6, -8, 14, -1, -4], ![1, 2, -2, -2, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P1 : CertificateIrreducibleZModOfList' 67 2 2 6 [46, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [48, 66], [0, 1]]
 g := ![![[31, 62], [40, 1], [54], [26], [26], [1]], ![[59, 5], [21, 66], [54], [26], [26], [1]]]
 h' := ![![[48, 66], [36, 14], [63, 1], [66, 56], [49, 48], [21, 48], [0, 1]], ![[0, 1], [38, 53], [44, 66], [7, 11], [8, 19], [47, 19], [48, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56]]
 b := ![[], [65, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N1 : CertifiedPrimeIdeal' SI67N1 67 where
  n := 2
  hpos := by decide
  P := [46, 19, 1]
  hirr := P67P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![135776, 99996, -17532, 73199, 164417]
  a := ![3, -2, 0, -3, -61]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-157233, -115574, -17532, 73199, 164417]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N1 B_one_repr
lemma NI67N1 : Nat.card (O ⧸ I67N1) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 10, 8, -6, 0]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![5, 10, 8, -6, 0]] 
 ![![67, 0, 0, 0, 0], ![19, 1, 0, 0, 0], ![54, 0, 1, 0, 0], ![47, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![5, 10, 8, -6, 0], ![0, 19, 32, 22, -18], ![-72, -40, -3, -42, 24], ![96, 34, -14, 91, -42], ![-128, -82, -34, -128, 73]]]
  hmulB := by decide  
  f := ![![![5255, -1726, 3332, 850, -1032]], ![![1367, -451, 868, 220, -270]], ![![4326, -1424, 2745, 698, -852]], ![![3667, -1212, 2330, 589, -726]], ![![478, -174, 314, 68, -107]]]
  g := ![![![-5, 10, 8, -6, 0], ![-45, 19, 32, 22, -18], ![40, -40, -3, -42, 24], ![-57, 34, -14, 91, -42], ![132, -82, -34, -128, 73]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![167, -2, 72, 56, 8]] ![![-33, 0, -12, -2, 4]]
  ![![-5255, 1726, -3332, -850, 1032]] where
 M := ![![![-5255, 1726, -3332, -850, 1032]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![-5255, 1726, -3332, -850, 1032]] ![![5, 10, 8, -6, 0]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10385, 3379, -6567, -1697, 2016]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-10385, 3379, -6567, -1697, 2016]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![35, 22, 28, 1, 0], ![21, 67, 45, 0, 1]] where
  M :=![![![-10385, 3379, -6567, -1697, 2016], ![16128, -5175, 10152, 2675, -3075], ![-12300, 4115, -7850, -1948, 2475], ![1836, -326, 987, 449, -147], ![-2604, 1456, -2037, -92, 976]]]
  hmulB := by decide  
  f := ![![![161, 52, -75, -23, 18]], ![![144, 199, 150, -1, -51]], ![![-204, 20, 200, -28, -27]], ![![41, 93, 88, -21, -18]], ![![51, 214, 246, -27, -59]]]
  g := ![![![94, -1329, -701, -1697, 2016], ![-182, 2000, 1037, 2675, -3075], ![55, -1674, -911, -1948, 2475], ![-152, -5, -70, 449, -147], ![-280, -872, -611, -92, 976]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [52, 35, 34, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 15, 66], [9, 55, 5], [0, 1]]
 g := ![![[65, 48, 1], [8, 32, 36], [51, 63, 12], [29, 12], [37, 1], []], ![[66, 26, 2, 35], [3, 36, 9, 62], [17, 25, 43, 66], [53, 5], [6, 43], [65, 25]], ![[39, 44, 25, 32], [52, 65, 4, 20], [32, 46, 52, 2], [11, 4], [63, 12], [55, 25]]]
 h' := ![![[28, 15, 66], [10, 30, 70], [46, 10, 6], [32, 37, 15], [64, 2, 56], [0, 0, 1], [0, 1]], ![[9, 55, 5], [38, 61, 8], [15, 70, 67], [42, 0, 1], [10, 17, 17], [31, 34, 55], [28, 15, 66]], ![[0, 1], [6, 51, 64], [5, 62, 69], [2, 34, 55], [19, 52, 69], [61, 37, 15], [9, 55, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19, 58], []]
 b := ![[], [18, 70, 40], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [52, 35, 34, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-556390, -384993, 20106, -381834, -389778]
  a := ![1, 0, 1, -1, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![295678, 480711, 397908, -381834, -389778]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 357911 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![161, 52, -75, -23, 18]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![161, 52, -75, -23, 18]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![24, 43, 1, 0, 0], ![33, 45, 0, 1, 0], ![17, 66, 0, 0, 1]] where
  M :=![![![161, 52, -75, -23, 18], ![144, 199, 150, -1, -51], ![-204, 20, 200, -28, -27], ![-180, -155, -27, 120, -30], ![-228, -131, -9, -107, 65]]]
  hmulB := by decide  
  f := ![![![-10385, 3379, -6567, -1697, 2016]], ![![16128, -5175, 10152, 2675, -3075]], ![![6084, -1934, 3818, 1019, -1146]], ![![5421, -1714, 3396, 913, -1014]], ![![12469, -3981, 7836, 2079, -2362]]]
  g := ![![![34, 44, -75, -23, 18], ![-36, -40, 150, -1, -51], ![-51, -78, 200, -28, -27], ![-42, -34, -27, 120, -30], ![34, 11, -9, -107, 65]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P1 : CertificateIrreducibleZModOfList' 71 2 2 6 [25, 58, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 70], [0, 1]]
 g := ![![[8, 54], [41, 18], [15, 32], [12], [27], [1]], ![[0, 17], [62, 53], [5, 39], [12], [27], [1]]]
 h' := ![![[13, 70], [40, 57], [51, 35], [70, 23], [21, 56], [46, 13], [0, 1]], ![[0, 1], [0, 14], [9, 36], [14, 48], [39, 15], [2, 58], [13, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [29, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N1 : CertifiedPrimeIdeal' SI71N1 71 where
  n := 2
  hpos := by decide
  P := [25, 58, 1]
  hirr := P71P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11972, 10002, -4733, 1504, 33752]
  a := ![1, -4, -2, -5, 28]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7012, -29321, -4733, 1504, 33752]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N1 B_one_repr
lemma NI71N1 : Nat.card (O ⧸ I71N1) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-10385, 3379, -6567, -1697, 2016]] ![![161, 52, -75, -23, 18]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-30223, 9879, -19093, -4798, 5553]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![-30223, 9879, -19093, -4798, 5553]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![36, 57, 57, 1, 0], ![31, 25, 56, 0, 1]] where
  M :=![![![-30223, 9879, -19093, -4798, 5553], ![44424, -16753, 29354, 5483, -8841], ![-35364, 12045, -22236, -4331, 3804], ![-6996, -8748, 1699, -9498, -174], ![-11564, 640, -3973, -333, -10025]]]
  hmulB := by decide  
  f := ![![![-9559, -109194, -142141, 5312, 36975]], ![![295800, 27863, -229012, -30769, 52911]], ![![211644, 181056, 58632, -28439, -19698]], ![![388404, 110460, -198695, -43347, 43086]], ![![258963, 102792, -92232, -30063, 18316]]]
  g := ![![![-406, 1980, -775, -4798, 5553], ![1659, -1483, 2903, 5483, -8841], ![36, 2244, 159, -4331, 3804], ![4662, 7356, 7573, -9498, -174], ![4263, 3702, 7896, -333, -10025]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [14, 61, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 53, 37], [60, 19, 36], [0, 1]]
 g := ![![[41, 4, 57], [23, 6], [4, 57], [42, 8, 3], [70, 1], []], ![[18, 14, 65, 4], [24, 72], [12, 8], [17, 66, 6, 4], [37, 69], [34, 55]], ![[71, 52, 48, 27], [2, 71], [42, 19], [37, 30, 36, 61], [2, 35], [35, 55]]]
 h' := ![![[10, 53, 37], [37, 34, 38], [33, 33, 15], [69, 39, 35], [42, 23, 21], [0, 0, 1], [0, 1]], ![[60, 19, 36], [32, 2, 9], [52, 28, 46], [1, 71, 64], [41, 36, 9], [62, 41, 19], [10, 53, 37]], ![[0, 1], [26, 37, 26], [45, 12, 12], [7, 36, 47], [10, 14, 43], [44, 32, 53], [60, 19, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23, 69], []]
 b := ![[], [19, 22, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [14, 61, 3, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3117555, 1611012, 1057488, 3829324, -4255548]
  a := ![-1, 7, 6, 9, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-38577, -1510572, 288996, 3829324, -4255548]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 389017 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9559, 109194, 142141, -5312, -36975]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![9559, 109194, 142141, -5312, -36975]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![24, 16, 1, 0, 0], ![54, 12, 0, 1, 0], ![61, 26, 0, 0, 1]] where
  M :=![![![9559, 109194, 142141, -5312, -36975], ![-295800, -27863, 229012, 30769, -52911], ![-211644, -181056, -58632, 28439, 19698], ![226692, -86181, -324001, -19293, 78963], ![46436, -53119, -115343, -2538, 28844]]]
  hmulB := by decide  
  f := ![![![30223, -9879, 19093, 4798, -5553]], ![![-44424, 16753, -29354, -5483, 8841]], ![![684, 259, 148, 435, 60]], ![![15150, -4434, 9275, 2778, -2652]], ![![9591, -2297, 5554, 2061, -1354]]]
  g := ![![![-11774, -15616, 142141, -5312, -36975], ![-57891, -36789, 229012, 30769, -52911], ![-21120, -1320, -58632, 28439, 19698], ![57915, 44881, -324001, -19293, 78963], ![16332, 14697, -115343, -2538, 28844]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P1 : CertificateIrreducibleZModOfList' 73 2 2 6 [16, 41, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 72], [0, 1]]
 g := ![![[71, 32], [19], [36], [39, 48], [2], [1]], ![[0, 41], [19], [36], [42, 25], [2], [1]]]
 h' := ![![[32, 72], [65, 55], [2, 26], [33, 67], [5, 62], [57, 32], [0, 1]], ![[0, 1], [0, 18], [31, 47], [60, 6], [18, 11], [59, 41], [32, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66]]
 b := ![[], [56, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N1 : CertifiedPrimeIdeal' SI73N1 73 where
  n := 2
  hpos := by decide
  P := [16, 41, 1]
  hirr := P73P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10544, -6772, -2224, -12510, 7758]
  a := ![0, -12, 0, -22, 6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3358, -312, -2224, -12510, 7758]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N1 B_one_repr
lemma NI73N1 : Nat.card (O ⧸ I73N1) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![-30223, 9879, -19093, -4798, 5553]] ![![9559, 109194, 142141, -5312, -36975]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0, 0, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0, 0, 0]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![0, 0, 0, 79, 0], ![0, 0, 0, 0, 79]] where
  M :=![![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![0, 0, 0, 79, 0], ![0, 0, 0, 0, 79]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 5 2 6 [24, 36, 64, 59, 6, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 56, 28, 71, 18], [64, 3, 59, 48, 23], [69, 37, 44, 17, 40], [58, 61, 27, 22, 77], [0, 1]]
 g := ![![[51, 21, 70, 74, 18], [61, 54, 46, 43, 73], [19, 20, 52, 62, 9], [6, 33, 56, 73, 1], [], []], ![[31, 68, 44, 76, 31, 33, 68, 11], [7, 28, 38, 41, 65, 18, 36, 45], [71, 4, 22, 3, 9, 40, 68, 5], [39, 23, 68, 68, 12, 9, 3, 5], [56, 78, 44, 36], [49, 9, 59, 8]], ![[63, 55, 45, 71, 40, 34, 31, 2], [76, 71, 70, 49, 13, 56, 76, 18], [60, 22, 76, 72, 19, 65, 7, 9], [13, 78, 25, 70, 35, 11, 34, 31], [5, 2, 5, 2], [37, 64, 61, 55]], ![[23, 71, 41, 44, 60, 75, 16, 31], [54, 21, 16, 15, 39, 30, 72, 42], [69, 22, 70, 1, 76, 62, 50, 50], [63, 28, 68, 46, 55, 78, 39, 13], [27, 32, 21, 32], [41, 8, 55, 20]], ![[65, 27, 1, 59, 41, 32, 19, 48], [3, 56, 73, 32, 34, 78, 23, 53], [26, 78, 12, 12, 0, 25, 47, 6], [5, 18, 54, 59, 34, 4, 21, 30], [52, 57, 70, 73], [54, 22, 46, 4]]]
 h' := ![![[40, 56, 28, 71, 18], [37, 71, 70, 18, 27], [18, 59, 34, 10, 28], [14, 19, 7, 7, 76], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[64, 3, 59, 48, 23], [6, 4, 57, 7, 59], [36, 55, 65, 69, 68], [77, 62, 4, 11, 30], [50, 18, 58, 26, 49], [29, 51, 26, 31, 73], [40, 56, 28, 71, 18]], ![[69, 37, 44, 17, 40], [69, 44, 56, 54, 49], [4, 71, 51, 2, 11], [15, 21, 63, 62, 10], [51, 46, 53, 49, 58], [48, 44, 3, 21, 70], [64, 3, 59, 48, 23]], ![[58, 61, 27, 22, 77], [27, 51, 7, 33, 46], [9, 37, 52, 8, 20], [49, 64, 11, 23, 10], [51, 32, 66, 28, 42], [64, 41, 49, 53, 43], [69, 37, 44, 17, 40]], ![[0, 1], [75, 67, 47, 46, 56], [25, 15, 35, 69, 31], [27, 71, 73, 55, 32], [54, 62, 60, 55, 8], [14, 22, 0, 53, 51], [58, 61, 27, 22, 77]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 50, 56, 48], [], [], []]
 b := ![[], [75, 6, 54, 47, 50], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 5
  hpos := by decide
  P := [24, 36, 64, 59, 6, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![115305717318, 30931892023, 100045758632, 229946292556, -493269248028]
  a := ![13, 5, 5, 6, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1459566042, 391542937, 1266402008, 2910712564, -6243914532]
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

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-113, 58, -87, -11, 36]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-113, 58, -87, -11, 36]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![0, 0, 0, 83, 0], ![13, 80, 46, 2, 1]] where
  M :=![![![-113, 58, -87, -11, 36], ![288, -9, 138, 89, 3], ![12, 176, -98, 104, 135], ![396, 247, 3, 278, 222], ![828, 607, -39, 619, 517]]]
  hmulB := by decide  
  f := ![![![5, 1, -3, 1, 0]], ![![0, 1, 0, -7, 3]], ![![12, 11, 8, 14, -9]], ![![-36, -20, -3, -27, 15]], ![![7, 7, 4, 1, -2]]]
  g := ![![![-7, -34, -21, -1, 36], ![3, -3, 0, 1, 3], ![-21, -128, -76, -2, 135], ![-30, -211, -123, -2, 222], ![-71, -491, -287, -5, 517]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 4 2 6 [24, 26, 82, 13, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [43, 82, 0, 30], [72, 8, 80, 15], [38, 75, 3, 38], [0, 1]]
 g := ![![[57, 62, 69, 9], [28, 63, 21, 16], [80, 59, 69], [19, 61, 16], [70, 1], []], ![[34, 29, 66, 25, 2, 41], [51, 57, 39, 65, 53, 17], [6, 20, 81], [6, 81, 64], [68, 13, 69, 47, 53, 78], [54, 3, 70]], ![[13, 14, 54, 62, 43, 19], [49, 77, 10, 27, 32, 53], [62, 47, 31], [18, 11, 26], [67, 8, 20, 29, 42, 32], [78, 56, 59]], ![[8, 63, 43, 38, 45, 36], [55, 15, 2, 79, 16, 78], [56, 18, 64], [54, 57, 40], [52, 68, 45, 22, 6, 31], [55, 48, 33]]]
 h' := ![![[43, 82, 0, 30], [75, 12, 31, 3], [54, 36, 44, 79], [27, 7, 16, 61], [63, 65, 44, 4], [0, 0, 1], [0, 1]], ![[72, 8, 80, 15], [29, 47, 3, 56], [45, 31, 34, 23], [43, 1, 28, 74], [42, 26, 0, 75], [55, 15, 40, 61], [43, 82, 0, 30]], ![[38, 75, 3, 38], [42, 0, 48, 17], [33, 50, 38, 9], [44, 60, 17, 23], [12, 33, 34, 21], [75, 21, 75, 35], [72, 8, 80, 15]], ![[0, 1], [17, 24, 1, 7], [45, 49, 50, 55], [12, 15, 22, 8], [48, 42, 5, 66], [41, 47, 50, 70], [38, 75, 3, 38]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [15, 52, 4], []]
 b := ![[], [], [10, 27, 24, 44], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 4
  hpos := by decide
  P := [24, 26, 82, 13, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-43672, 39856, -148262, -247987, 796269]
  a := ![-1, -2, 0, -3, 0]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-125243, -767008, -443092, -22175, 796269]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 47458321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 1, -3, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![5, 1, -3, 1, 0]] 
 ![![83, 0, 0, 0, 0], ![76, 1, 0, 0, 0], ![17, 0, 1, 0, 0], ![63, 0, 0, 1, 0], ![11, 0, 0, 0, 1]] where
  M :=![![![5, 1, -3, 1, 0], ![0, 1, 0, -7, 3], ![12, 11, 8, 14, -9], ![-36, -20, -3, -27, 15], ![36, 22, 9, 40, -22]]]
  hmulB := by decide  
  f := ![![![-113, 58, -87, -11, 36]], ![![-100, 53, -78, -9, 33]], ![![-23, 14, -19, -1, 9]], ![![-81, 47, -66, -5, 30]], ![![-5, 15, -12, 6, 11]]]
  g := ![![![-1, 1, -3, 1, 0], ![4, 1, 0, -7, 3], ![-21, 11, 8, 14, -9], ![37, -20, -3, -27, 15], ![-49, 22, 9, 40, -22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-113, 58, -87, -11, 36]] ![![5, 1, -3, 1, 0]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![324929, -73179, -394881, -29661, 95196]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![324929, -73179, -394881, -29661, 95196]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![0, 0, 0, 89, 0], ![16, 87, 52, 74, 1]] where
  M :=![![![324929, -73179, -394881, -29661, 95196], ![761568, 435689, -87036, -93729, 6213], ![24852, 399663, 529418, -18426, -137487], ![-930732, -275214, 461607, 104291, -99489], ![-305124, -37020, 224799, 32070, -51622]]]
  hmulB := by decide  
  f := ![![![-2255, 162, -1059, -681, -6]], ![![-48, -2663, 1686, -1479, -2049]], ![![-8196, -3564, -1184, -4746, -3243]], ![![-12948, -9093, 339, -9422, -7716]], ![![-16348, -12444, 1049, -12416, -10510]]]
  g := ![![![-13463, -93879, -60057, -79485, 95196], ![7440, -1178, -4608, -6219, 6213], ![24996, 138888, 86278, 114108, -137487], ![7428, 94161, 63315, 83893, -99489], ![5852, 50046, 32687, 43282, -51622]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 4 2 6 [83, 71, 58, 60, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [49, 9, 56, 71], [2, 24, 68, 27], [67, 55, 54, 80], [0, 1]]
 g := ![![[23, 23, 66, 64], [14, 39, 53], [17, 37, 50], [41, 33, 58, 57], [29, 1], []], ![[2, 56, 78, 61, 5, 79], [83, 53, 10], [52, 25, 2], [64, 59, 61, 33, 87, 81], [14, 65, 22, 86, 76, 4], [15, 82, 57]], ![[41, 83, 85, 20, 6, 33], [20, 43, 81], [1, 64, 39], [47, 29, 16, 60, 9, 26], [78, 75, 88, 83, 17, 12], [51, 71, 17]], ![[60, 16, 33, 85, 68, 42], [5, 68, 42], [16, 45, 21], [57, 22, 2, 80, 54, 4], [66, 76, 88, 9, 57, 16], [48, 42, 81]]]
 h' := ![![[49, 9, 56, 71], [76, 53, 34, 81], [9, 60, 87, 63], [68, 62, 36, 36], [85, 83, 27, 71], [0, 0, 1], [0, 1]], ![[2, 24, 68, 27], [44, 63, 59, 36], [13, 32, 44, 59], [18, 35, 6, 64], [44, 6, 72, 29], [88, 42, 20, 43], [49, 9, 56, 71]], ![[67, 55, 54, 80], [20, 31, 77, 56], [16, 79, 49, 80], [59, 84, 87, 22], [72, 32, 1, 71], [43, 16, 71, 60], [2, 24, 68, 27]], ![[0, 1], [47, 31, 8, 5], [62, 7, 87, 65], [77, 86, 49, 56], [50, 57, 78, 7], [60, 31, 86, 75], [67, 55, 54, 80]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [55, 14, 80], []]
 b := ![[], [], [32, 80, 56, 30], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 4
  hpos := by decide
  P := [83, 71, 58, 60, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-134098345, -78477597, -26255750, -137141893, 77691471]
  a := ![3, -4, 7, -8, 0]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-15473729, -76827366, -45687778, -66138323, 77691471]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 62742241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2255, -162, 1059, 681, 6]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![2255, -162, 1059, 681, 6]] 
 ![![89, 0, 0, 0, 0], ![44, 1, 0, 0, 0], ![11, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![68, 0, 0, 0, 1]] where
  M :=![![![2255, -162, 1059, 681, 6], ![48, 2663, -1686, 1479, 2049], ![8196, 3564, 1184, 4746, 3243], ![12948, 9093, -339, 9422, 7716], ![30372, 20217, -105, 21435, 17411]]]
  hmulB := by decide  
  f := ![![![-324929, 73179, 394881, 29661, -95196]], ![![-169196, 31283, 196200, 15717, -47133]], ![![-40439, 4554, 42857, 3873, -10221]], ![![-495, 5559, 8124, -172, -2091]], ![![-244832, 56328, 299181, 22302, -72154]]]
  g := ![![![-53, -162, 1059, 681, 6], ![-2723, 2663, -1686, 1479, 2049], ![-4454, 3564, 1184, 4746, 3243], ![-10521, 9093, -339, 9422, 7716], ![-23666, 20217, -105, 21435, 17411]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![324929, -73179, -394881, -29661, 95196]] ![![2255, -162, 1059, 681, 6]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-703, 259, -459, -86, 123]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-703, 259, -459, -86, 123]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![77, 23, 38, 1, 0], ![15, 45, 67, 0, 1]] where
  M :=![![![-703, 259, -459, -86, 123], ![984, -461, 690, 29, -135], ![-540, 485, -490, 203, -24], ![-588, -446, -63, -690, 360], ![732, 634, 45, 943, -511]]]
  hmulB := by decide  
  f := ![![![-79, 146, 273, 2, -69]], ![![-552, -153, 288, 61, -63]], ![![-252, -320, -214, 37, 60]], ![![-287, -46, 196, 30, -45]], ![![-441, -270, 26, 54, 2]]]
  g := ![![![42, -34, -56, -86, 123], ![8, 51, 89, 29, -135], ![-163, -32, -68, 203, -24], ![486, -8, 21, -690, 360], ![-662, 20, -16, 943, -511]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [78, 35, 24, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [28, 71, 76], [45, 25, 21], [0, 1]]
 g := ![![[27, 92, 89], [2, 66], [22, 53], [39, 81], [78, 91], [1]], ![[76, 10, 31, 67], [69, 89], [73, 43], [67, 9], [76, 86], [51, 13, 74, 51]], ![[88, 45, 1, 60], [37, 25], [11, 16], [86, 36], [31, 2], [67, 72, 58, 46]]]
 h' := ![![[28, 71, 76], [74, 67, 34], [91, 85, 39], [62, 77, 21], [0, 94, 9], [19, 62, 73], [0, 1]], ![[45, 25, 21], [14, 88, 25], [62, 66, 63], [18, 7, 72], [54, 66, 94], [29, 69, 38], [28, 71, 76]], ![[0, 1], [16, 39, 38], [63, 43, 92], [57, 13, 4], [13, 34, 91], [54, 63, 83], [45, 25, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [93, 96], []]
 b := ![[], [77, 37, 60], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [78, 35, 24, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-518370, -217599, -284223, -793791, 1305864]
  a := ![1, -4, -4, -5, 10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![422841, -419838, -593949, -793791, 1305864]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 912673 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, -146, -273, -2, 69]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![79, -146, -273, -2, 69]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![20, 59, 1, 0, 0], ![81, 70, 0, 1, 0], ![77, 52, 0, 0, 1]] where
  M :=![![![79, -146, -273, -2, 69], ![552, 153, -288, -61, 63], ![252, 320, 214, -37, -60], ![-516, 25, 501, 53, -117], ![-132, 55, 195, 16, -44]]]
  hmulB := by decide  
  f := ![![![703, -259, 459, 86, -123]], ![![-984, 461, -690, -29, 135]], ![![-448, 222, -320, -2, 57]], ![![-117, 121, -114, 58, -9]], ![![23, 35, -6, 43, -20]]]
  g := ![![![4, 129, -273, -2, 69], ![66, 187, -288, -61, 63], ![37, -68, 214, -37, -60], ![-60, -280, 501, 53, -117], ![-20, -106, 195, 16, -44]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P1 : CertificateIrreducibleZModOfList' 97 2 2 6 [39, 51, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [46, 96], [0, 1]]
 g := ![![[61, 44], [89], [79], [95], [48], [46, 1]], ![[48, 53], [89], [79], [95], [48], [92, 96]]]
 h' := ![![[46, 96], [48, 23], [67, 63], [74, 46], [44, 17], [49, 40], [0, 1]], ![[0, 1], [39, 74], [55, 34], [56, 51], [50, 80], [46, 57], [46, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58]]
 b := ![[], [12, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N1 : CertifiedPrimeIdeal' SI97N1 97 where
  n := 2
  hpos := by decide
  P := [39, 51, 1]
  hirr := P97P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![211, 32, -70, 57, 63]
  a := ![4, 1, -1, 2, 0]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-81, -32, -70, 57, 63]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N1 B_one_repr
lemma NI97N1 : Nat.card (O ⧸ I97N1) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-703, 259, -459, -86, 123]] ![![79, -146, -273, -2, 69]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3411, 179, -1559, -1065, -64]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![-3411, 179, -1559, -1065, -64]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![29, 57, 75, 1, 0], ![41, 65, 83, 0, 1]] where
  M :=![![![-3411, 179, -1559, -1065, -64], ![-512, -4225, 2488, -2501, -3259], ![-13036, -5909, -1724, -7668, -5381], ![-21268, -14886, 515, -15473, -12563], ![-49452, -33008, 243, -34916, -28522]]]
  hmulB := by decide  
  f := ![![![13905, 5238, -5341, -1603, 1084]], ![![8672, 15587, 13682, -1491, -3725]], ![![-14900, 2610, 17078, 1390, -4099]], ![![-2383, 12064, 18814, -242, -4816]], ![![-1107, 14248, 20676, -457, -5325]]]
  g := ![![![298, 644, 828, -1065, -64], ![2036, 3467, 4560, -2501, -3259], ![4257, 7732, 10099, -7668, -5381], ![9332, 16670, 21819, -15473, -12563], ![21114, 37734, 49369, -34916, -28522]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [88, 54, 88, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [71, 88, 74], [43, 12, 27], [0, 1]]
 g := ![![[21, 6, 19], [41, 17], [31, 67, 76], [11, 49], [86, 68], [1]], ![[1, 64, 2, 51], [58, 81], [75, 36, 79, 12], [2, 84], [24, 4], [74, 9, 5, 12]], ![[19, 29, 90, 98], [44, 13], [13, 74, 74, 42], [90, 31], [34, 20], [37, 87, 30, 89]]]
 h' := ![![[71, 88, 74], [29, 78, 25], [100, 25, 57], [11, 12, 50], [75, 88, 94], [13, 47, 13], [0, 1]], ![[43, 12, 27], [10, 89, 12], [8, 85, 9], [51, 30, 74], [5, 46, 65], [20, 7, 99], [71, 88, 74]], ![[0, 1], [62, 35, 64], [55, 92, 35], [46, 59, 78], [54, 68, 43], [97, 47, 90], [43, 12, 27]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52, 23], []]
 b := ![[], [1, 100, 42], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [88, 54, 88, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-23727, -85133, -70568, 10043, 19669]
  a := ![7, -1, -26, -1, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-11103, -19169, -24320, 10043, 19669]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 1030301 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![45, 29, -3, 31, 26]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![45, 29, -3, 31, 26]] 
 ![![101, 0, 0, 0, 0], ![20, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![71, 0, 0, 1, 0], ![97, 0, 0, 0, 1]] where
  M :=![![![45, 29, -3, 31, 26], ![208, 141, -4, 145, 119], ![476, 327, -4, 340, 277], ![1004, 688, -11, 723, 589], ![2292, 1566, -31, 1642, 1340]]]
  hmulB := by decide  
  f := ![![![-783, 170, -453, -219, 190]], ![![-140, 33, -82, -37, 33]], ![![-34, 0, -16, -16, 11]], ![![-529, 131, -314, -133, 122]], ![![-783, 147, -442, -240, 199]]]
  g := ![![![-52, 29, -3, 31, 26], ![-242, 141, -4, 145, 119], ![-565, 327, -4, 340, 277], ![-1200, 688, -11, 723, 589], ![-2728, 1566, -31, 1642, 1340]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![395, -128, 249, 65, -76]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![395, -128, 249, 65, -76]] 
 ![![101, 0, 0, 0, 0], ![32, 1, 0, 0, 0], ![94, 0, 1, 0, 0], ![96, 0, 0, 1, 0], ![24, 0, 0, 0, 1]] where
  M :=![![![395, -128, 249, 65, -76], ![-608, 199, -386, -99, 119], ![476, -150, 298, 80, -89], ![-52, 25, -37, -4, 16], ![140, -27, 77, 33, -13]]]
  hmulB := by decide  
  f := ![![![-233, -99, 3, -253, 124]], ![![-64, -25, 4, -69, 33]], ![![-242, -107, -2, -260, 129]], ![![-172, -66, 11, -191, 91]], ![![-124, -64, -13, -130, 68]]]
  g := ![![![-231, -128, 249, 65, -76], ![356, 199, -386, -99, 119], ![-280, -150, 298, 80, -89], ![26, 25, -37, -4, 16], ![-90, -27, 77, 33, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![-3411, 179, -1559, -1065, -64]] ![![45, 29, -3, 31, 26]]
  ![![-2074295, -1416417, 29452, -1484929, -1212273]] where
 M := ![![![-2074295, -1416417, 29452, -1484929, -1212273]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![-2074295, -1416417, 29452, -1484929, -1212273]] ![![395, -128, 249, 65, -76]]
  ![![101, 0, 0, 0, 0]] where
 M := ![![![-36647749, -25166877, 611555, -26313025, -21527746]]]
 hmul := by decide  
 g := ![![![![-362849, -249177, 6055, -260525, -213146]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-40647, 13058, -25601, -6747, 7802]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![-40647, 13058, -25601, -6747, 7802]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![63, 28, 39, 1, 0], ![31, 36, 47, 0, 1]] where
  M :=![![![-40647, 13058, -25601, -6747, 7802], ![62416, -20491, 39610, 10159, -12439], ![-49756, 14836, -30650, -9006, 9019], ![4868, -2907, 4037, 340, -2780], ![-18156, 313, -8049, -6413, 353]]]
  hmulB := by decide  
  f := ![![![-26457, -26193, -12245, 3697, 3734]], ![![29872, -23729, -59780, -2049, 14825]], ![![59300, 23133, -21680, -6868, 4339]], ![![14415, -13276, -31368, -916, 7806]], ![![29623, -5446, -34308, -2753, 8241]]]
  g := ![![![1384, -766, -1254, -6747, 7802], ![-1864, 1387, 2214, 10159, -12439], ![2311, -560, -1003, -9006, 9019], ![676, 851, 1179, 340, -2780], ![3640, 1623, 2189, -6413, 353]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [42, 100, 51, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [57, 52, 18], [98, 50, 85], [0, 1]]
 g := ![![[6, 5, 82], [43, 62, 8], [65, 10, 61], [40, 28], [16, 26], [1]], ![[40, 35, 24, 83], [55, 36, 75, 82], [52, 12, 48, 63], [97, 7], [81, 61], [47, 94, 3, 64]], ![[94, 62, 50, 10], [85, 73, 23, 57], [80, 93, 100, 20], [26, 7], [29, 63], [46, 4, 55, 39]]]
 h' := ![![[57, 52, 18], [48, 23, 44], [51, 85, 27], [1, 53, 79], [62, 43, 53], [61, 3, 52], [0, 1]], ![[98, 50, 85], [62, 53, 39], [48, 27, 99], [87, 46, 63], [12, 75, 25], [85, 88, 79], [57, 52, 18]], ![[0, 1], [63, 27, 20], [85, 94, 80], [49, 4, 64], [27, 88, 25], [3, 12, 75], [98, 50, 85]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [93, 1], []]
 b := ![[], [11, 16, 40], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [42, 100, 51, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1894, -3422, -2395, -2722, -1005]
  a := ![1, 0, -5, -1, 0]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1949, 1058, 1466, -2722, -1005]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 1092727 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![26457, 26193, 12245, -3697, -3734]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![26457, 26193, 12245, -3697, -3734]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![93, 64, 1, 0, 0], ![22, 71, 0, 1, 0], ![62, 31, 0, 0, 1]] where
  M :=![![![26457, 26193, 12245, -3697, -3734], ![-29872, 23729, 59780, 2049, -14825], ![-59300, -23133, 21680, 6868, -4339], ![-2420, -44956, -59891, 2035, 15545], ![-8844, -18038, -16911, 1606, 4564]]]
  hmulB := by decide  
  f := ![![![40647, -13058, 25601, 6747, -7802]], ![![-62416, 20491, -39610, -10159, 12439]], ![![-1599, 798, -1199, -133, 597]], ![![-34390, 11364, -21875, -5565, 6935]], ![![5858, -1696, 3567, 1066, -956]]]
  g := ![![![-7762, -3682, 12245, -3697, -3734], ![-45780, -33865, 59780, 2049, -14825], ![-19006, -17124, 21680, 6868, -4339], ![44261, 30696, -59891, 2035, 15545], ![12093, 7852, -16911, 1606, 4564]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P1 : CertificateIrreducibleZModOfList' 103 2 2 6 [50, 72, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [31, 102], [0, 1]]
 g := ![![[55, 68], [100, 30], [25, 59], [33], [50], [31, 1]], ![[0, 35], [0, 73], [0, 44], [33], [50], [62, 102]]]
 h' := ![![[31, 102], [47, 45], [89, 37], [7, 33], [100, 62], [98, 87], [0, 1]], ![[0, 1], [0, 58], [0, 66], [0, 70], [65, 41], [14, 16], [31, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [72]]
 b := ![[], [60, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N1 : CertifiedPrimeIdeal' SI103N1 103 where
  n := 2
  hpos := by decide
  P := [50, 72, 1]
  hirr := P103P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2915, 2142, -76, 2400, 2112]
  a := ![3, 4, 0, 9, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1687, -2222, -76, 2400, 2112]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N1 B_one_repr
lemma NI103N1 : Nat.card (O ⧸ I103N1) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![-40647, 13058, -25601, -6747, 7802]] ![![26457, 26193, 12245, -3697, -3734]]
  ![![103, 0, 0, 0, 0]] where
 M := ![![![-103, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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


lemma PB1072I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB1072I2 : PrimesBelowBoundCertificateInterval O 61 103 1072 where
  m := 9
  g := ![3, 2, 2, 1, 2, 2, 2, 3, 2]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB1072I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0, I67N1, I67N2]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1]
    · exact ![I79N0]
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
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
    · exact ![4489, 4489, 67]
    · exact ![357911, 5041]
    · exact ![389017, 5329]
    · exact ![3077056399]
    · exact ![47458321, 83]
    · exact ![62742241, 89]
    · exact ![912673, 9409]
    · exact ![1030301, 101, 101]
    · exact ![1092727, 10609]
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
      exact NI73N1
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
  β := ![I67N2, I83N1, I89N1, I101N1, I101N2]
  Il := ![[I67N2], [], [], [], [I83N1], [I89N1], [], [I101N1, I101N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
