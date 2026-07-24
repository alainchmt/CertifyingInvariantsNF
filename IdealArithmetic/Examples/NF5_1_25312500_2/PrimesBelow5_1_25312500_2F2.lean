
import IdealArithmetic.Examples.NF5_1_25312500_2.RI5_1_25312500_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-167, 100, 105, -89, 18]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![-167, 100, 105, -89, 18]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![0, 0, 67, 0, 0], ![63, 53, 36, 1, 0], ![64, 48, 61, 0, 1]] where
  M :=![![![-167, 100, 105, -89, 18], ![-164, -47, 239, 121, -196], ![1242, -458, -1070, 239, 317], ![-1378, 822, 877, -726, 132], ![106, -706, 540, 982, -965]]]
  hmulB := by decide  
  f := ![![![-831, 474, -31, 7, -121]], ![![1186, -575, 11, -55, 135]], ![![-1290, 750, -46, 11, -190]], ![![-517, 385, -45, -32, -107]], ![![-1124, 728, -64, -23, -193]]]
  g := ![![![64, 59, 33, -89, 18], ![71, 44, 117, 121, -196], ![-509, -423, -433, 239, 317], ![536, 492, 283, -726, 132], ![0, -96, 359, 982, -965]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [43, 64, 60, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [66, 38, 66], [8, 28, 1], [0, 1]]
 g := ![![[53, 55, 17], [61, 20, 54], [46, 47], [24, 24], [7, 1], []], ![[4, 32, 5, 13], [31, 17, 41, 30], [16, 9], [49, 16], [29, 47], [65, 1]], ![[26, 2, 3, 15], [13, 20, 10, 56], [36, 23], [47, 54], [44, 37], [63, 1]]]
 h' := ![![[66, 38, 66], [57, 64, 33], [65, 2, 11], [57, 23, 39], [34, 45, 52], [0, 0, 1], [0, 1]], ![[8, 28, 1], [50, 49, 56], [15, 41, 38], [10, 19, 64], [24, 34, 4], [20, 9, 28], [66, 38, 66]], ![[0, 1], [49, 21, 45], [64, 24, 18], [65, 25, 31], [3, 55, 11], [35, 58, 38], [8, 28, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30, 41], []]
 b := ![[], [16, 54, 41], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [43, 64, 60, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6413275, 5609473, 3562087, -5160493, 1901229]
  a := ![-16, 11, 7, -17, -30]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2940584, 2803830, 1094998, -5160493, 1901229]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 300763 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-831, 474, -31, 7, -121]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![-831, 474, -31, 7, -121]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![9, 65, 1, 0, 0], ![23, 65, 0, 1, 0], ![7, 7, 0, 0, 1]] where
  M :=![![![-831, 474, -31, 7, -121], ![1186, -575, 11, -55, 135], ![-1290, 750, -46, 11, -190], ![1296, -592, 11, -66, 139], ![-362, 290, -26, -20, -77]]]
  hmulB := by decide  
  f := ![![![-167, 100, 105, -89, 18]], ![![-164, -47, 239, 121, -196]], ![![-163, -39, 230, 109, -183]], ![![-237, 1, 281, 76, -182]], ![![-33, -5, 44, 18, -33]]]
  g := ![![![2, 43, -31, 7, -121], ![21, 20, 11, -55, 135], ![3, 65, -46, 11, -190], ![26, 30, 11, -66, 139], ![13, 57, -26, -20, -77]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P1 : CertificateIrreducibleZModOfList' 67 2 2 6 [41, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [54, 66], [0, 1]]
 g := ![![[33, 59], [46, 26], [15], [64], [35], [1]], ![[3, 8], [43, 41], [15], [64], [35], [1]]]
 h' := ![![[54, 66], [57, 27], [4, 48], [4, 22], [45, 8], [26, 54], [0, 1]], ![[0, 1], [41, 40], [50, 19], [53, 45], [8, 59], [61, 13], [54, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [51, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N1 : CertifiedPrimeIdeal' SI67N1 67 where
  n := 2
  hpos := by decide
  P := [41, 13, 1]
  hirr := P67P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2507911, 562164, 1803250, -349212, -112353]
  a := ![-121, 61, 62, -122, -243]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-148042, -1390505, 1803250, -349212, -112353]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N1 B_one_repr
lemma NI67N1 : Nat.card (O ⧸ I67N1) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![-167, 100, 105, -89, 18]] ![![-831, 474, -31, 7, -121]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-91927, 49734, -2427, 2083, -12329]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-91927, 49734, -2427, 2083, -12329]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![19, 29, 1, 0, 0], ![27, 49, 0, 1, 0], ![50, 12, 0, 0, 1]] where
  M :=![![![-91927, 49734, -2427, 2083, -12329], ![122946, -66507, 3263, -2771, 16495], ![-143702, 77722, -3790, 3263, -19266], ![131652, -71252, 3503, -2954, 17675], ![-46490, 25106, -1210, 1076, -6217]]]
  hmulB := by decide  
  f := ![![![1397, -840, -887, 743, -138]], ![![1236, 425, -1897, -1031, 1624]], ![![735, 1, -888, -249, 589]], ![![1547, -123, -1751, -344, 1054]], ![![1172, -434, -1002, 232, 289]]]
  g := ![![![7245, 2338, -2427, 2083, -12329], ![-9704, -3145, 3263, -2771, 16495], ![11317, 3647, -3790, 3263, -19266], ![-10407, -3383, 3503, -2954, 17675], ![3638, 1156, -1210, 1076, -6217]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [65, 69, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 70], [0, 1]]
 g := ![![[24, 49], [33, 54], [22, 25], [30], [4], [1]], ![[51, 22], [70, 17], [1, 46], [30], [4], [1]]]
 h' := ![![[2, 70], [56, 64], [61, 57], [17, 66], [60, 32], [6, 2], [0, 1]], ![[0, 1], [42, 7], [33, 14], [7, 5], [53, 39], [10, 69], [2, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [66, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [65, 69, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-22231, 5128, 15478, -3916, -2066]
  a := ![-12, 8, 6, -13, -23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1511, -3198, 15478, -3916, -2066]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9827, 5318, -261, 221, -1319]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-9827, 5318, -261, 221, -1319]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![5, 67, 1, 0, 0], ![23, 53, 0, 1, 0], ![8, 10, 0, 0, 1]] where
  M :=![![![-9827, 5318, -261, 221, -1319], ![13150, -7107, 345, -301, 1761], ![-15358, 8314, -408, 345, -2062], ![14088, -7608, 369, -324, 1885], ![-4958, 2694, -134, 108, -669]]]
  hmulB := by decide  
  f := ![![![-35, 20, 7, -27, 24]], ![![-260, 53, 225, -13, -78]], ![![-239, 47, 206, -11, -71]], ![![-209, 49, 171, -22, -48]], ![![-54, 12, 46, -4, -15]]]
  g := ![![![-43, 342, -261, 221, -1319], ![60, -449, 345, -301, 1761], ![-67, 535, -408, 345, -2062], ![65, -479, 369, -324, 1885], ![-20, 178, -134, 108, -669]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P1 : CertificateIrreducibleZModOfList' 71 2 2 6 [61, 25, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [46, 70], [0, 1]]
 g := ![![[33, 29], [40, 18], [22, 20], [64], [57], [1]], ![[18, 42], [16, 53], [19, 51], [64], [57], [1]]]
 h' := ![![[46, 70], [45, 10], [7, 35], [39, 34], [31, 63], [10, 46], [0, 1]], ![[0, 1], [8, 61], [55, 36], [41, 37], [18, 8], [67, 25], [46, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49]]
 b := ![[], [40, 60]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N1 : CertifiedPrimeIdeal' SI71N1 71 where
  n := 2
  hpos := by decide
  P := [61, 25, 1]
  hirr := P71P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-442443, 98464, 319955, -59793, -19641]
  a := ![51, -28, -25, 50, 103]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7181, -253142, 319955, -59793, -19641]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N1 B_one_repr
lemma NI71N1 : Nat.card (O ⧸ I71N1) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31459, -17016, 832, -712, 4219]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![31459, -17016, 832, -712, 4219]] 
 ![![71, 0, 0, 0, 0], ![23, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![66, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![31459, -17016, 832, -712, 4219], ![-42070, 22761, -1112, 952, -5643], ![49170, -26598, 1301, -1112, 6595], ![-45060, 24376, -1190, 1021, -6043], ![15896, -8600, 422, -358, 2133]]]
  hmulB := by decide  
  f := ![![![737, -428, -466, 382, -67]], ![![247, -135, -164, 116, -10]], ![![10, -22, 11, 30, -27]], ![![770, -448, -488, 399, -69]], ![![-5, 40, -32, -56, 56]]]
  g := ![![![6464, -17016, 832, -712, 4219], ![-8646, 22761, -1112, 952, -5643], ![10103, -26598, 1301, -1112, 6595], ![-9261, 24376, -1190, 1021, -6043], ![3265, -8600, 422, -358, 2133]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-91927, 49734, -2427, 2083, -12329]] ![![-9827, 5318, -261, 221, -1319]]
  ![![1685115081, -911567192, 44562106, -38129540, 226012317]] where
 M := ![![![1685115081, -911567192, 44562106, -38129540, 226012317]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![1685115081, -911567192, 44562106, -38129540, 226012317]] ![![31459, -17016, 832, -712, 4219]]
  ![![71, 0, 0, 0, 0]] where
 M := ![![![98863594716071, -53480513564036, 2614405115176, -2237009636154, 13259862362646]]]
 hmul := by decide  
 g := ![![![![1392444996001, -753246669916, 36822607256, -31507177974, 186758624826]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, 0, 14, -2, -4]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![-7, 0, 14, -2, -4]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![2, 13, 60, 1, 0], ![19, 30, 3, 0, 1]] where
  M :=![![![-7, 0, 14, -2, -4], ![52, -27, -46, 26, 0], ![-36, 36, 19, -46, 26], ![-132, 44, 110, -13, -44], ![364, -172, -272, 124, 33]]]
  hmulB := by decide  
  f := ![![![-31, -32, 2, 10, 8]], ![![-68, -59, -2, 14, 12]], ![![-20, -28, -9, -2, 2]], ![![-30, -35, -8, 1, 4]], ![![-37, -34, -1, 8, 7]]]
  g := ![![![1, 2, 2, -2, -4], ![0, -5, -22, 26, 0], ![-6, -2, 37, -46, 26], ![10, 21, 14, -13, -44], ![-7, -38, -107, 124, 33]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [32, 60, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [67, 28, 27], [70, 44, 46], [0, 1]]
 g := ![![[23, 2, 41], [12, 55], [11, 6], [16, 66, 3], [64, 1], []], ![[36, 20, 65, 65], [71, 23], [10, 41], [64, 62, 4, 57], [58, 38], [61, 72]], ![[69, 49, 30, 41], [35, 65], [21, 67], [9, 12, 60, 54], [16, 54], [42, 72]]]
 h' := ![![[67, 28, 27], [31, 41, 25], [14, 4, 36], [72, 10, 58], [69, 70, 21], [0, 0, 1], [0, 1]], ![[70, 44, 46], [65, 14, 17], [72, 50, 13], [63, 26, 48], [1, 38, 40], [55, 51, 44], [67, 28, 27]], ![[0, 1], [40, 18, 31], [49, 19, 24], [65, 37, 40], [2, 38, 12], [52, 22, 28], [70, 44, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50, 7], []]
 b := ![[], [11, 15, 43], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [32, 60, 9, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7072664, 5119206, 4369578, -4555584, 1113441]
  a := ![-12, 9, 7, -10, -27]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-261875, 423816, 3758415, -4555584, 1113441]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 389017 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-31, -32, 2, 10, 8]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-31, -32, 2, 10, 8]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![43, 50, 1, 0, 0], ![62, 53, 0, 1, 0], ![63, 45, 0, 0, 1]] where
  M :=![![![-31, -32, 2, 10, 8], ![-68, -59, -2, 14, 12], ![-20, -28, -9, -2, 2], ![-44, -44, -22, -9, 0], ![-12, -20, -24, -20, -7]]]
  hmulB := by decide  
  f := ![![![-7, 0, 14, -2, -4]], ![![52, -27, -46, 26, 0]], ![![31, -18, -23, 16, -2]], ![![30, -19, -20, 17, -4]], ![![31, -19, -20, 16, -3]]]
  g := ![![![-17, -14, 2, 10, 8], ![-22, -17, -2, 14, 12], ![5, 6, -9, -2, 2], ![20, 21, -22, -9, 0], ![37, 35, -24, -20, -7]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P1 : CertificateIrreducibleZModOfList' 73 2 2 6 [34, 53, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 72], [0, 1]]
 g := ![![[8, 37], [71], [48], [19, 9], [35], [1]], ![[18, 36], [71], [48], [53, 64], [35], [1]]]
 h' := ![![[20, 72], [41, 16], [22, 61], [11, 62], [39, 70], [39, 20], [0, 1]], ![[0, 1], [69, 57], [1, 12], [10, 11], [52, 3], [1, 53], [20, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [41, 47]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N1 : CertifiedPrimeIdeal' SI73N1 73 where
  n := 2
  hpos := by decide
  P := [34, 53, 1]
  hirr := P73P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3414, -3442, 84, 1506, 2696]
  a := ![-16, 10, 4, -26, -12]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3702, -2860, 84, 1506, 2696]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N1 B_one_repr
lemma NI73N1 : Nat.card (O ⧸ I73N1) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![-7, 0, 14, -2, -4]] ![![-31, -32, 2, 10, 8]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3465, 424, 3791, 563, -2151]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![-3465, 424, 3791, 563, -2151]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![29, 55, 35, 1, 0], ![55, 7, 59, 0, 1]] where
  M :=![![![-3465, 424, 3791, 563, -2151], ![25864, -11697, -20151, 8145, 3277], ![-35320, 22212, 21562, -20151, 4868], ![-26630, 2654, 29713, 5202, -17437], ![132622, -54270, -108778, 33504, 25353]]]
  hmulB := by decide  
  f := ![![![-2541, 586, 55, 279, -110]], ![![1434, -2509, 237, 389, 668]], ![![-3744, 1072, -74, 237, -279]], ![![-1573, -1091, 153, 481, 309]], ![![-4461, 983, 2, 407, -226]]]
  g := ![![![1247, -196, 1405, 563, -2151], ![-4944, -6109, -6311, 8145, 3277], ![3561, 13879, 5565, -20151, 4868], ![9893, -2043, 11094, 5202, -17437], ![-28271, -26259, -35155, 33504, 25353]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [51, 35, 76, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [58, 74, 44], [24, 4, 35], [0, 1]]
 g := ![![[19, 6, 8], [32, 9, 25], [39, 76, 50], [26, 28, 44], [3, 1], []], ![[45, 26, 59, 32], [76, 54, 40, 13], [53, 47, 52, 38], [31, 11, 48, 46], [37, 16], [75, 40]], ![[30, 64, 15, 48], [1, 39, 4, 74], [25, 51, 71, 28], [38, 75, 12, 41], [2, 25], [5, 40]]]
 h' := ![![[58, 74, 44], [27, 39, 18], [65, 25, 5], [17, 57, 34], [5, 2, 53], [0, 0, 1], [0, 1]], ![[24, 4, 35], [74, 37, 50], [0, 36, 14], [52, 4, 37], [20, 6, 63], [13, 48, 4], [58, 74, 44]], ![[0, 1], [26, 3, 11], [58, 18, 60], [54, 18, 8], [2, 71, 42], [5, 31, 74], [24, 4, 35]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 74], []]
 b := ![[], [3, 2, 45], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [51, 35, 76, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2299945, 1138182, 1718864, -857950, -173469]
  a := ![1, 9, 7, 2, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![406600, 627085, 531415, -857950, -173469]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 493039 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![359, -176, -267, 133, 25]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![359, -176, -267, 133, 25]] 
 ![![79, 0, 0, 0, 0], ![14, 1, 0, 0, 0], ![53, 0, 1, 0, 0], ![58, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![359, -176, -267, 133, 25], ![-384, 367, 115, -401, 241], ![-1156, 192, 1216, 115, -642], ![2926, -1422, -2185, 1064, 223], ![-3510, 2518, 1846, -2452, 949]]]
  hmulB := by decide  
  f := ![![![4735, 3030, -4151, -4887, -2554]], ![![1048, 685, -865, -1033, -544]], ![![3381, 2194, -2873, -3408, -1789]], ![![3922, 2576, -3227, -3858, -2034]], ![![841, 612, -511, -665, -367]]]
  g := ![![![115, -176, -267, 133, 25], ![126, 367, 115, -401, 241], ![-892, 192, 1216, 115, -642], ![954, -1422, -2185, 1064, 223], ![-13, 2518, 1846, -2452, 949]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1

def I79N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 8, 2, -6, -4]] i)))

def SI79N2: IdealEqSpanCertificate' Table ![![1, 8, 2, -6, -4]] 
 ![![79, 0, 0, 0, 0], ![74, 1, 0, 0, 0], ![69, 0, 1, 0, 0], ![47, 0, 0, 1, 0], ![13, 0, 0, 0, 1]] where
  M :=![![![1, 8, 2, -6, -4], ![36, 5, -18, -2, -8], ![12, 20, -9, -18, 6], ![-20, 44, 34, -25, -20], ![132, -36, -80, 36, -7]]]
  hmulB := by decide  
  f := ![![![-209313, 113224, -5534, 4738, -28072]], ![![-192522, 104141, -5090, 4358, -25820]], ![![-186959, 101132, -4943, 4232, -25074]], ![![-120733, 65308, -3192, 2733, -16192]], ![![-35783, 19356, -946, 810, -4799]]]
  g := ![![![-5, 8, 2, -6, -4], ![14, 5, -18, -2, -8], ![-1, 20, -9, -18, 6], ![-53, 44, 34, -25, -20], ![85, -36, -80, 36, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N2 : Nat.card (O ⧸ I79N2) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N2)

lemma isPrimeI79N2 : Ideal.IsPrime I79N2 := prime_ideal_of_norm_prime hp79.out _ NI79N2
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![-3465, 424, 3791, 563, -2151]] ![![359, -176, -267, 133, 25]]
  ![![3408201, -4723484, 382870, 5678380, -4334013]] where
 M := ![![![3408201, -4723484, 382870, 5678380, -4334013]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI79N1 : IdealMulLeCertificate' Table 
  ![![3408201, -4723484, 382870, 5678380, -4334013]] ![![1, 8, 2, -6, -4]]
  ![![79, 0, 0, 0, 0]] where
 M := ![![![-847700099, 417178776, 628179244, -315877866, -56777221]]]
 hmul := by decide  
 g := ![![![![-10730381, 5280744, 7951636, -3998454, -718699]]]]
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

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31320649, -16942946, 828262, -708704, 4200805]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![31320649, -16942946, 828262, -708704, 4200805]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![0, 0, 0, 83, 0], ![2, 38, 19, 59, 1]] where
  M :=![![![31320649, -16942946, 828262, -708704, 4200805], ![-41888492, 22659755, -1107714, 947820, -5618213], ![48955364, -26482512, 1294617, -1107714, 6566033], ![-44863602, 24269102, -1186368, 1015165, -6017223], ![15827744, -8562072, 418590, -358106, 2122879]]]
  hmulB := by decide  
  f := ![![![-801, 422, 568, -338, -13]], ![![360, -635, 172, 798, -663]], ![![3620, -968, -3459, 172, 1461]], ![![-6558, 3418, 4678, -2719, -153]], ![![-3620, 1868, 2601, -1473, -113]]]
  g := ![![![276133, -2127392, -951651, -2994653, 4200805], ![-369302, 2845203, 1272751, 4005089, -5618213], ![431606, -3325202, -1487470, -4680767, 6566033], ![-395532, 3047272, 1363143, 4289534, -6017223], ![139542, -1075078, -480917, -1513349, 2122879]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 4 2 6 [74, 68, 3, 22, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [72, 27, 48, 36], [10, 81, 50, 20], [62, 57, 68, 27], [0, 1]]
 g := ![![[8, 4, 76, 70], [40, 20, 63, 75], [28], [27, 18, 40], [61, 1], []], ![[14, 79, 1, 63, 36, 75], [9, 26, 58, 65, 24, 11], [9, 45, 44], [65, 20, 48], [46, 23, 48, 78, 21, 10], [57, 10, 51]], ![[68, 70, 37, 57, 17, 52], [75, 71, 28, 25, 72, 80], [69, 60, 64], [64, 66, 61], [65, 76, 43, 9, 44, 35], [9, 6, 68]], ![[21, 46, 54, 71, 47, 3], [66, 27, 36, 66, 3, 48], [20, 70, 10], [25, 42, 12], [37, 58, 24, 30, 80, 65], [15, 1, 65]]]
 h' := ![![[72, 27, 48, 36], [28, 71, 38, 30], [72, 36, 13, 18], [22, 29, 51], [51, 11, 81, 66], [0, 0, 1], [0, 1]], ![[10, 81, 50, 20], [70, 11, 45, 3], [82, 24, 50, 9], [82, 9, 81, 58], [59, 55, 12, 31], [53, 19, 28, 36], [72, 27, 48, 36]], ![[62, 57, 68, 27], [32, 26, 9, 22], [44, 46, 37, 2], [81, 71, 12, 75], [13, 10, 31, 12], [15, 66, 19, 8], [10, 81, 50, 20]], ![[0, 1], [80, 58, 74, 28], [75, 60, 66, 54], [71, 57, 22, 33], [57, 7, 42, 57], [78, 81, 35, 39], [62, 57, 68, 27]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [72, 55, 29], []]
 b := ![[], [], [40, 45, 25, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 4
  hpos := by decide
  P := [74, 68, 3, 22, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![632836, -348096, -458738, 260258, -15333]
  a := ![-3, 0, 1, -4, -3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![7994, 2826, -2017, 14035, -15333]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 47458321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-801, 422, 568, -338, -13]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-801, 422, 568, -338, -13]] 
 ![![83, 0, 0, 0, 0], ![49, 1, 0, 0, 0], ![20, 0, 1, 0, 0], ![43, 0, 0, 1, 0], ![29, 0, 0, 0, 1]] where
  M :=![![![-801, 422, 568, -338, -13], ![360, -635, 172, 798, -663], ![3620, -968, -3459, 172, 1461], ![-6558, 3418, 4678, -2719, -153], ![5604, -4940, -2070, 5246, -2891]]]
  hmulB := by decide  
  f := ![![![31320649, -16942946, 828262, -708704, 4200805]], ![![17985823, -9729453, 475628, -406972, 2412304]], ![![8136968, -4401704, 215179, -184118, 1091351]], ![![15685835, -8485272, 414806, -354929, 2103824]], ![![11134055, -6022982, 294436, -251934, 1493328]]]
  g := ![![![-216, 422, 568, -338, -13], ![156, -635, 172, 798, -663], ![849, -968, -3459, 172, 1461], ![-1762, 3418, 4678, -2719, -153], ![1775, -4940, -2070, 5246, -2891]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![31320649, -16942946, 828262, -708704, 4200805]] ![![-801, 422, 568, -338, -13]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![869, -474, 55, 11, 132]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![869, -474, 55, 11, 132]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![88, 67, 1, 0, 0], ![67, 27, 0, 1, 0], ![83, 4, 0, 0, 1]] where
  M :=![![![869, -474, 55, 11, 132], ![-1254, 593, 53, 121, -110], ![1264, -824, 100, 53, 231], ![-1508, 496, 99, 208, -68], ![186, -442, 124, 154, 155]]]
  hmulB := by decide  
  f := ![![![107, 132, -255, -227, 283]], ![![-3312, 1287, 2783, -737, -737]], ![![-2316, 1061, 1793, -748, -275]], ![![-917, 503, 631, -416, 15]], ![![-221, 238, 41, -269, 178]]]
  g := ![![![-176, -56, 55, 11, 132], ![-55, -65, 53, 121, -110], ![-340, -111, 100, 53, 231], ![-208, -129, 99, 208, -68], ![-381, -152, 124, 154, 155]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [46, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [71, 88], [0, 1]]
 g := ![![[12, 88], [50], [44], [66, 81], [7, 57], [1]], ![[30, 1], [50], [44], [32, 8], [49, 32], [1]]]
 h' := ![![[71, 88], [13, 34], [34, 53], [79, 69], [34, 80], [43, 71], [0, 1]], ![[0, 1], [24, 55], [59, 36], [83, 20], [18, 9], [11, 18], [71, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61]]
 b := ![[], [52, 75]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [46, 18, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-33370, 7008, 26068, -3251, -3832]
  a := ![12, -6, -3, 8, 29]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-20129, -18387, 26068, -3251, -3832]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25, -22, -2, -2, 4]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![25, -22, -2, -2, 4]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![23, 36, 1, 0, 0], ![74, 86, 0, 1, 0], ![77, 11, 0, 0, 1]] where
  M :=![![![25, -22, -2, -2, 4], ![-44, 15, -10, -6, -8], ![54, -22, -7, -10, 2], ![-26, 34, -18, -19, -16], ![40, 8, -16, -20, -9]]]
  hmulB := by decide  
  f := ![![![1, 2, -6, -6, 8]], ![![-92, 31, 74, -18, -20]], ![![-35, 12, 27, -8, -6]], ![![-88, 32, 66, -23, -12]], ![![-15, 7, 8, -8, 3]]]
  g := ![![![-1, 2, -2, -2, 4], ![14, 11, -10, -6, -8], ![9, 12, -7, -10, 2], ![34, 28, -18, -19, -16], ![29, 27, -16, -20, -9]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P1 : CertificateIrreducibleZModOfList' 89 2 2 6 [59, 55, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 88], [0, 1]]
 g := ![![[13, 9], [39], [53], [71, 11], [48, 88], [1]], ![[52, 80], [39], [53], [0, 78], [14, 1], [1]]]
 h' := ![![[34, 88], [55, 3], [24, 67], [83, 63], [16, 10], [30, 34], [0, 1]], ![[0, 1], [68, 86], [77, 22], [0, 26], [0, 79], [29, 55], [34, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77]]
 b := ![[], [13, 83]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N1 : CertifiedPrimeIdeal' SI89N1 89 where
  n := 2
  hpos := by decide
  P := [59, 55, 1]
  hirr := P89P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-14381, 3294, 10701, -1819, -55]
  a := ![9, -6, -5, 8, 19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1367, -2527, 10701, -1819, -55]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N1 B_one_repr
lemma NI89N1 : Nat.card (O ⧸ I89N1) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N1

def I89N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1921, -638, -1717, 271, 589]] i)))

def SI89N2: IdealEqSpanCertificate' Table ![![1921, -638, -1717, 271, 589]] 
 ![![89, 0, 0, 0, 0], ![63, 1, 0, 0, 0], ![31, 0, 1, 0, 0], ![50, 0, 0, 1, 0], ![34, 0, 0, 0, 1]] where
  M :=![![![1921, -638, -1717, 271, 589], ![-7336, 3907, 5153, -3163, -47], ![4898, -4710, -1434, 5153, -3116], ![15260, -4964, -13739, 2002, 4835], ![-42302, 20606, 31550, -15456, -3151]]]
  hmulB := by decide  
  f := ![![![-50545, 26008, -307, 2293, -6014]], ![![-35081, 17977, -170, 1642, -4138]], ![![-18517, 9494, -111, 846, -2195]], ![![-27696, 14106, -113, 1328, -3238]], ![![-19680, 10014, -94, 932, -2305]]]
  g := ![![![694, -638, -1717, 271, 589], ![-2848, 3907, 5153, -3163, -47], ![2184, -4710, -1434, 5153, -3116], ![5499, -4964, -13739, 2002, 4835], ![-16164, 20606, 31550, -15456, -3151]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N2 : Nat.card (O ⧸ I89N2) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N2)

lemma isPrimeI89N2 : Ideal.IsPrime I89N2 := prime_ideal_of_norm_prime hp89.out _ NI89N2
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![869, -474, 55, 11, 132]] ![![25, -22, -2, -2, 4]]
  ![![50545, -26008, 307, -2293, 6014]] where
 M := ![![![50545, -26008, 307, -2293, 6014]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![50545, -26008, 307, -2293, 6014]] ![![1921, -638, -1717, 271, 589]]
  ![![89, 0, 0, 0, 0]] where
 M := ![![![-89, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-207, 44, 206, 4, -96]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-207, 44, 206, 4, -96]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![0, 0, 0, 97, 0], ![84, 44, 12, 4, 1]] where
  M :=![![![-207, 44, 206, 4, -96], ![1170, -565, -886, 416, 104], ![-1340, 924, 737, -886, 312], ![-1616, 336, 1626, 57, -786], ![6268, -2740, -4980, 1832, 943]]]
  hmulB := by decide  
  f := ![![![33, -12, -6, -8, 0]], ![![-14, 35, -18, -20, -16]], ![![68, -4, -11, -18, -4]], ![![16, 64, -26, -35, -26]], ![![32, 8, -16, -20, -9]]]
  g := ![![![81, 44, 14, 4, -96], ![-78, -53, -22, 0, 104], ![-284, -132, -31, -22, 312], ![664, 360, 114, 33, -786], ![-752, -456, -168, -20, 943]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 4 2 6 [91, 27, 7, 14, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [62, 92, 22, 83], [62, 58, 51, 11], [56, 43, 24, 3], [0, 1]]
 g := ![![[75, 53, 72, 94], [96, 58, 16], [60, 53, 73], [63, 68, 93], [92, 83, 1], []], ![[87, 74, 94, 73, 6, 21], [53, 19, 93], [3, 46, 62], [81, 61, 22], [59, 69, 36], [74, 13, 61, 50, 39, 69]], ![[66, 73, 20, 62, 32, 94], [89], [6, 79, 24], [64, 48, 94], [45, 89, 35], [55, 43, 68, 33, 73, 70]], ![[30, 58, 64, 24, 43, 35], [65, 77, 48], [24, 33, 53], [66, 5, 79], [49, 81, 88], [40, 49, 66, 48, 76, 27]]]
 h' := ![![[62, 92, 22, 83], [21, 83, 64, 26], [67, 76, 11, 4], [17, 12, 89, 48], [67, 51, 31, 44], [0, 0, 0, 1], [0, 1]], ![[62, 58, 51, 11], [30, 56, 12, 12], [10, 25, 39, 53], [63, 51, 26, 81], [81, 87, 10, 33], [55, 75, 25, 91], [62, 92, 22, 83]], ![[56, 43, 24, 3], [51, 82, 3, 36], [14, 16, 34], [50, 63, 12, 86], [65, 72, 26, 71], [38, 75, 4, 36], [62, 58, 51, 11]], ![[0, 1], [49, 70, 18, 23], [12, 77, 13, 40], [16, 68, 67, 76], [28, 81, 30, 46], [92, 44, 68, 66], [56, 43, 24, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [49, 67, 27], []]
 b := ![[], [], [47, 89, 7, 24], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 4
  hpos := by decide
  P := [91, 27, 7, 14, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-582369, -192960, 241990, 79855, 119510]
  a := ![4, 0, 0, 5, 2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-109497, -56200, -12290, -4105, 119510]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 88529281 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![33, -12, -6, -8, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![33, -12, -6, -8, 0]] 
 ![![97, 0, 0, 0, 0], ![90, 1, 0, 0, 0], ![76, 0, 1, 0, 0], ![10, 0, 0, 1, 0], ![27, 0, 0, 0, 1]] where
  M :=![![![33, -12, -6, -8, 0], ![-14, 35, -18, -20, -16], ![68, -4, -11, -18, -4], ![16, 64, -26, -35, -26], ![68, 36, -20, -32, -17]]]
  hmulB := by decide  
  f := ![![![-207, 44, 206, 4, -96]], ![![-180, 35, 182, 8, -88]], ![![-176, 44, 169, -6, -72]], ![![-38, 8, 38, 1, -18]], ![![7, -16, 6, 20, -17]]]
  g := ![![![17, -12, -6, -8, 0], ![-12, 35, -18, -20, -16], ![16, -4, -11, -18, -4], ![-28, 64, -26, -35, -26], ![-9, 36, -20, -32, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-207, 44, 206, 4, -96]] ![![33, -12, -6, -8, 0]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0, 0, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0, 0, 0]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![0, 0, 0, 101, 0], ![0, 0, 0, 0, 101]] where
  M :=![![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![0, 0, 0, 101, 0], ![0, 0, 0, 0, 101]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 5 2 6 [69, 28, 73, 74, 71, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [87, 61, 69, 19, 22], [19, 64, 27, 95, 28], [85, 23, 6, 57, 30], [41, 53, 100, 31, 21], [0, 1]]
 g := ![![[69, 31, 25, 78, 43], [14, 10, 28, 14], [10, 44, 65, 92, 36], [47, 88, 94, 21], [30, 1], []], ![[70, 82, 11, 42, 91, 78, 22, 77], [29, 68], [8, 32, 31, 76, 96, 61, 12, 30], [44, 99, 21, 43], [17, 83, 91, 21], [10, 35, 71, 89, 44, 99, 93, 43]], ![[32, 16, 58, 11, 60, 89, 10, 15], [76, 62, 25, 78], [58, 26, 2, 72, 70, 3, 41, 40], [4, 49, 42, 19], [80, 100, 57, 13], [40, 63, 47, 10, 8, 25, 68, 35]], ![[77, 9, 29, 89, 98, 35, 20, 77], [24, 58, 15, 16], [20, 39, 4, 90, 21, 11, 9, 33], [24, 51, 38, 77], [78, 60, 21, 25], [87, 25, 44, 93, 25, 30, 57, 33]], ![[19, 99, 96, 52, 97, 78, 36, 88], [50, 42, 57, 68], [79, 94, 51, 18, 95, 73, 59, 14], [2, 12, 27, 79], [19, 6, 4, 82], [26, 84, 86, 52, 94, 90, 87, 70]]]
 h' := ![![[87, 61, 69, 19, 22], [30, 29, 27, 0, 89], [17, 0, 87, 44, 69], [65, 86, 46, 86, 6], [51, 0, 4, 30, 18], [0, 0, 0, 1], [0, 1]], ![[19, 64, 27, 95, 28], [6, 96, 66, 61, 16], [54, 93, 12, 13], [0, 74, 44, 36, 65], [39, 59, 59, 86, 12], [0, 45, 93, 29, 83], [87, 61, 69, 19, 22]], ![[85, 23, 6, 57, 30], [96, 10, 1, 5, 72], [54, 22, 6, 31, 49], [85, 8, 86, 80, 47], [82, 70, 97, 55, 76], [59, 13, 64, 87, 66], [19, 64, 27, 95, 28]], ![[41, 53, 100, 31, 21], [48, 32, 59, 17, 22], [47, 78, 43, 96, 97], [37, 26, 11, 75, 71], [73, 78, 86, 46, 28], [1, 70, 35, 18, 5], [85, 23, 6, 57, 30]], ![[0, 1], [8, 35, 49, 18, 3], [78, 9, 54, 18, 88], [78, 8, 15, 26, 13], [32, 96, 57, 86, 68], [63, 74, 10, 67, 48], [41, 53, 100, 31, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 11, 74, 75], [], [], []]
 b := ![[], [23, 83, 31, 14, 93], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 5
  hpos := by decide
  P := [69, 28, 73, 74, 71, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3403825014892109, -1519091624348665, -2675428213321104, 1041652687929497, 471727997662482]
  a := ![-60, 45, 21, -60, -127]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![33701237771209, -15040511132165, -26489388250704, 10313392949797, 4670574234282]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10510100501 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def PBC101 : ContainsPrimesAboveP 101 ![I101N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![101, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 101 (by decide) 𝕀

instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-267, -958, 230, 378, 317]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![-267, -958, 230, 378, 317]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![0, 0, 0, 103, 0], ![31, 9, 3, 73, 1]] where
  M :=![![![-267, -958, 230, 378, 317], ![-2562, -1199, 390, 838, 439], ![-300, -1456, 167, 390, 399], ![-3014, -1606, 220, 787, 451], ![-1392, -1680, 58, 450, 397]]]
  hmulB := by decide  
  f := ![![![15, 2, -20, -8, 15]], ![![-178, 75, 144, -48, -31]], ![![292, -168, -193, 144, -17]], ![![110, 22, -154, -69, 121]], ![![67, 21, -101, -53, 85]]]
  g := ![![![-98, -37, -7, -221, 317], ![-157, -50, -9, -303, 439], ![-123, -49, -10, -279, 399], ![-165, -55, -11, -312, 451], ![-133, -51, -11, -277, 397]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 4 2 6 [74, 69, 48, 20, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [50, 7, 97, 85], [100, 9, 26, 85], [36, 86, 83, 36], [0, 1]]
 g := ![![[55, 64, 59, 38], [13, 66, 36, 7], [0, 81, 75, 98], [86, 13, 34], [43, 83, 1], []], ![[28, 38, 94, 45, 23, 3], [60, 35, 27, 20, 3, 74], [2, 15, 65, 21, 45, 99], [29, 75, 30], [43, 2, 26], [26, 40, 12, 92, 83, 39]], ![[25, 37, 86, 59, 90, 84], [78, 90, 91, 52, 9, 45], [89, 83, 93, 2, 95, 20], [99, 83, 50], [58, 26, 81], [100, 2, 69, 64, 81, 39]], ![[73, 20, 83, 24, 15, 25], [67, 65, 68, 70, 99, 29], [81, 3, 13, 100, 43, 28], [3, 2, 100], [99, 34, 98], [16, 14, 27, 50, 65, 100]]]
 h' := ![![[50, 7, 97, 85], [68, 90, 89, 48], [0, 35, 83, 78], [40, 45, 56, 43], [11, 58, 66, 31], [0, 0, 0, 1], [0, 1]], ![[100, 9, 26, 85], [71, 36, 53, 29], [23, 81, 12, 73], [35, 18, 39, 47], [92, 82, 73, 66], [94, 57, 96, 51], [50, 7, 97, 85]], ![[36, 86, 83, 36], [26, 62, 59, 8], [14, 78, 46, 7], [13, 1, 43, 39], [52, 99, 95, 16], [92, 96, 23, 94], [100, 9, 26, 85]], ![[0, 1], [78, 18, 5, 18], [80, 12, 65, 48], [36, 39, 68, 77], [19, 70, 75, 93], [49, 53, 87, 60], [36, 86, 83, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [44, 93, 41], []]
 b := ![[], [], [55, 88, 68, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 4
  hpos := by decide
  P := [74, 69, 48, 20, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4950948076, -1051986754, -5183705982, -301826314, 2596466074]
  a := ![-18, 14, 6, -19, -35]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-733393206, -237089140, -125952468, -1843144172, 2596466074]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 112550881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-15, -2, 20, 8, -15]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![-15, -2, 20, 8, -15]] 
 ![![103, 0, 0, 0, 0], ![61, 1, 0, 0, 0], ![66, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![92, 0, 0, 0, 1]] where
  M :=![![![-15, -2, 20, 8, -15], ![178, -75, -144, 48, 31], ![-292, 168, 193, -144, 17], ![-110, -22, 154, 69, -121], ![868, -324, -742, 174, 213]]]
  hmulB := by decide  
  f := ![![![267, 958, -230, -378, -317]], ![![183, 579, -140, -232, -192]], ![![174, 628, -149, -246, -207]], ![![50, 90, -20, -37, -29]], ![![252, 872, -206, -342, -287]]]
  g := ![![![1, -2, 20, 8, -15], ![107, -75, -144, 48, 31], ![-230, 168, 193, -144, 17], ![16, -22, 154, 69, -121], ![472, -324, -742, 174, 213]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![-267, -958, 230, 378, 317]] ![![-15, -2, 20, 8, -15]]
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


lemma PB314I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB314I2 : PrimesBelowBoundCertificateInterval O 61 103 314 where
  m := 9
  g := ![2, 3, 2, 3, 2, 3, 2, 1, 2]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB314I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1, I71N2]
    · exact ![I73N0, I73N1]
    · exact ![I79N0, I79N1, I79N2]
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1, I89N2]
    · exact ![I97N0, I97N1]
    · exact ![I101N0]
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
    · exact ![5041, 5041, 71]
    · exact ![389017, 5329]
    · exact ![493039, 79, 79]
    · exact ![47458321, 83]
    · exact ![7921, 7921, 89]
    · exact ![88529281, 97]
    · exact ![10510100501]
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
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
  β := ![I71N2, I79N1, I79N2, I83N1, I89N2, I97N1, I103N1]
  Il := ![[], [I71N2], [], [I79N1, I79N2], [I83N1], [I89N2], [I97N1], [], [I103N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
