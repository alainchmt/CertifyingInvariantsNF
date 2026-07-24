
import IdealArithmetic.Examples.NF5_3_1215000000_2.RI5_3_1215000000_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-595, 532, -444, 748, -386]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![-595, 532, -444, 748, -386]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![0, 0, 67, 0, 0], ![64, 53, 57, 1, 0], ![57, 1, 21, 0, 1]] where
  M :=![![![-595, 532, -444, 748, -386], ![2316, -2057, 1724, -2900, 1496], ![-8976, 7980, -6681, 11248, -5800], ![9380, -8340, 6984, -11749, 6064], ![-17236, 15320, -12826, 21594, -11133]]]
  hmulB := by decide  
  f := ![![![39, -36, 8, 8, -6]], ![![36, 5, -36, -4, 16]], ![![-96, 124, 37, -16, -8]], ![![-16, 75, 11, -9, 0]], ![![5, 7, 17, 2, -7]]]
  g := ![![![-395, -578, -522, 748, -386], ![1532, 2241, 2024, -2900, 1496], ![-5944, -8692, -7851, 11248, -5800], ![6204, 9079, 8199, -11749, 6064], ![-11413, -16687, -15073, 21594, -11133]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [44, 39, 24, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [63, 7, 10], [47, 59, 57], [0, 1]]
 g := ![![[61, 18, 40], [22, 46, 47], [27, 25], [18, 1], [43, 1], []], ![[32, 10, 58, 49], [50, 65], [46, 55], [4, 1], [56, 64], [18, 33]], ![[50, 36, 29, 8], [31, 17, 62, 66], [61, 54], [44, 4], [16, 49], [38, 33]]]
 h' := ![![[63, 7, 10], [37, 55, 43], [18, 58, 39], [0, 56, 5], [51, 21, 1], [0, 0, 1], [0, 1]], ![[47, 59, 57], [16, 26, 5], [7, 43], [50, 62, 51], [62, 14, 1], [28, 1, 59], [63, 7, 10]], ![[0, 1], [52, 53, 19], [36, 33, 28], [24, 16, 11], [34, 32, 65], [1, 66, 7], [47, 59, 57]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46, 34], []]
 b := ![[], [20, 15, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [44, 39, 24, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11690316, 4753497, -5943246, -18843441, -12275252]
  a := ![0, 7, -7, -5, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![28617312, 15160166, 19789749, -18843441, -12275252]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 300763 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![39, -36, 8, 8, -6]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![39, -36, 8, 8, -6]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![63, 29, 1, 0, 0], ![15, 18, 0, 1, 0], ![64, 24, 0, 0, 1]] where
  M :=![![![39, -36, 8, 8, -6], ![36, 5, -36, -4, 16], ![-96, 124, 37, -16, -8], ![-4, -4, 24, 9, -8], ![92, -88, -58, 18, 25]]]
  hmulB := by decide  
  f := ![![![-595, 532, -444, 748, -386]], ![![2316, -2057, 1724, -2900, 1496]], ![![309, -271, 229, -384, 198]], ![![629, -558, 468, -787, 406]], ![![4, 0, 2, -2, 1]]]
  g := ![![![-3, -4, 8, 8, -6], ![20, 11, -36, -4, 16], ![-25, -7, 37, -16, -8], ![-17, -10, 24, 9, -8], ![28, 10, -58, 18, 25]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P1 : CertificateIrreducibleZModOfList' 67 2 2 6 [22, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [47, 66], [0, 1]]
 g := ![![[7, 64], [56, 62], [47], [56], [65], [1]], ![[0, 3], [22, 5], [47], [56], [65], [1]]]
 h' := ![![[47, 66], [41, 59], [8, 14], [38, 39], [59, 49], [45, 47], [0, 1]], ![[0, 1], [0, 8], [63, 53], [62, 28], [17, 18], [43, 20], [47, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [30, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N1 : CertifiedPrimeIdeal' SI67N1 67 where
  n := 2
  hpos := by decide
  P := [22, 20, 1]
  hirr := P67P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-698599, -1712328, 1794550, 1464403, 2629079]
  a := ![3, 62, -124, -1, -249]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4537050, -2137484, 1794550, 1464403, 2629079]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N1 B_one_repr
lemma NI67N1 : Nat.card (O ⧸ I67N1) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![-595, 532, -444, 748, -386]] ![![39, -36, 8, 8, -6]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1705, -2201, -378, 369, 44]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![1705, -2201, -378, 369, 44]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![0, 0, 0, 71, 0], ![21, 0, 14, 10, 1]] where
  M :=![![![1705, -2201, -378, 369, 44], ![-264, 1846, -1454, -501, 738], ![-4428, 3905, 2799, -435, -1002], ![440, -1349, 672, 338, -378], ![2996, -1207, -3304, -159, 1397]]]
  hmulB := by decide  
  f := ![![![-65, -19, 4, 63, 32]], ![![-192, -36, 40, 267, 126]], ![![-756, -121, 191, 1143, 534]], ![![-1384, -215, 354, 2110, 982]], ![![-391, -64, 96, 584, 273]]]
  g := ![![![11, -31, -14, -1, 44], ![-222, 26, -166, -111, 738], ![234, 55, 237, 135, -1002], ![118, -19, 84, 58, -378], ![-371, -17, -322, -199, 1397]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 4 2 6 [37, 38, 21, 66, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 59, 12, 41], [55, 32, 51, 18], [15, 50, 8, 12], [0, 1]]
 g := ![![[67, 70, 45, 48], [10, 47, 18, 38], [1, 44, 29, 48], [34, 57, 25], [1], []], ![[70, 4, 48, 5, 25, 56], [65, 41, 1, 8, 8, 61], [11, 9, 13, 5, 68, 35], [22, 36, 29], [3], [12, 17, 48]], ![[23, 26, 9, 24, 51, 37], [49, 65, 60, 28, 70, 49], [36, 56, 68, 36, 0, 8], [27, 47, 12], [7, 47, 15], [29, 48, 40]], ![[5, 19, 43, 67, 36, 36], [23, 34, 6, 36, 38, 38], [60, 42, 30, 33, 14, 30], [6, 62, 29], [35, 58, 15], [31, 60, 2]]]
 h' := ![![[6, 59, 12, 41], [56, 31, 21, 41], [34, 5, 27, 31], [40, 50, 45, 30], [34, 33, 50, 5], [0, 0, 1], [0, 1]], ![[55, 32, 51, 18], [28, 28, 38, 6], [21, 22, 60, 33], [38, 33, 13, 49], [0, 17, 9, 61], [18, 49, 28], [6, 59, 12, 41]], ![[15, 50, 8, 12], [47, 33, 65, 52], [24, 38, 33, 57], [69, 59, 46, 23], [43, 51, 54, 15], [35, 3, 23, 21], [55, 32, 51, 18]], ![[0, 1], [65, 50, 18, 43], [68, 6, 22, 21], [34, 0, 38, 40], [55, 41, 29, 61], [1, 19, 19, 50], [15, 50, 8, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [70, 21, 42], []]
 b := ![[], [], [42, 61, 25, 45], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 4
  hpos := by decide
  P := [37, 38, 21, 66, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-13263827597, -4475482444, 5856402804, 21124758456, 12729907038]
  a := ![1, 6, -8, -3, -18]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3951998245, -63034964, -2427637968, -1495412844, 12729907038]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 25411681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-65, -19, 4, 63, 32]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-65, -19, 4, 63, 32]] 
 ![![71, 0, 0, 0, 0], ![51, 1, 0, 0, 0], ![26, 0, 1, 0, 0], ![57, 0, 0, 1, 0], ![57, 0, 0, 0, 1]] where
  M :=![![![-65, -19, 4, 63, 32], ![-192, -36, 40, 267, 126], ![-756, -121, 191, 1143, 534], ![-1384, -215, 354, 2110, 982], ![-1972, -301, 518, 3039, 1415]]]
  hmulB := by decide  
  f := ![![![1705, -2201, -378, 369, 44]], ![![1221, -1555, -292, 258, 42]], ![![562, -751, -99, 129, 2]], ![![1375, -1786, -294, 301, 30]], ![![1411, -1784, -350, 294, 55]]]
  g := ![![![-65, -19, 4, 63, 32], ![-307, -36, 40, 267, 126], ![-1340, -121, 191, 1143, 534], ![-2477, -215, 354, 2110, 982], ![-3577, -301, 518, 3039, 1415]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![1705, -2201, -378, 369, 44]] ![![-65, -19, 4, 63, 32]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1783, 272, -459, -2731, -1268]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![1783, 272, -459, -2731, -1268]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![69, 30, 1, 0, 0], ![63, 49, 0, 1, 0], ![32, 23, 0, 0, 1]] where
  M :=![![![1783, 272, -459, -2731, -1268], ![7608, 1169, -2000, -11716, -5462], ![32772, 4938, -8547, -50488, -23432], ![60324, 9206, -15850, -92975, -43290], ![87126, 13152, -22761, -134259, -62345]]]
  hmulB := by decide  
  f := ![![![2899, -6620, 2249, 1483, -1354]], ![![8124, -4895, -7386, 106, 2966]], ![![5835, -7936, -874, 1387, -58]], ![![7905, -8981, -2959, 1354, 798]], ![![4106, -4745, -1457, 727, 375]]]
  g := ![![![3371, 2425, -459, -2731, -1268], ![14500, 10423, -2000, -11716, -5462], ![62371, 44852, -8547, -50488, -23432], ![115023, 82687, -15850, -92975, -43290], ![165904, 119296, -22761, -134259, -62345]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [13, 30, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [43, 72], [0, 1]]
 g := ![![[36, 24], [46], [19], [35, 23], [24], [1]], ![[46, 49], [46], [19], [2, 50], [24], [1]]]
 h' := ![![[43, 72], [71, 30], [42, 22], [56, 47], [3, 60], [60, 43], [0, 1]], ![[0, 1], [47, 43], [39, 51], [33, 26], [28, 13], [11, 30], [43, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [48, 47]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [13, 30, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-91722, -254248, 265561, 199631, 386429]
  a := ![1, -25, 48, -1, 95]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-593944, -368368, 265561, 199631, 386429]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17, -9, -4, 1, 2]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-17, -9, -4, 1, 2]] 
 ![![73, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![48, 0, 1, 0, 0], ![35, 0, 0, 1, 0], ![56, 0, 0, 0, 1]] where
  M :=![![![-17, -9, -4, 1, 2], ![-12, -8, -4, 1, 2], ![-12, -3, -3, 1, 2], ![-12, -5, -2, 2, 2], ![0, -3, 0, 3, 1]]]
  hmulB := by decide  
  f := ![![![-17, 19, -6, 5, -2]], ![![-1, 1, 0, 0, 0]], ![![-12, 13, -5, 5, -2]], ![![-7, 8, -2, 1, 0]], ![![-16, 17, -6, 7, -3]]]
  g := ![![![1, -9, -4, 1, 2], ![1, -8, -4, 1, 2], ![0, -3, -3, 1, 2], ![-1, -5, -2, 2, 2], ![-2, -3, 0, 3, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1

def I73N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 0, -2, 4, -2]] i)))

def SI73N2: IdealEqSpanCertificate' Table ![![-1, 0, -2, 4, -2]] 
 ![![73, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![65, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![45, 0, 0, 0, 1]] where
  M :=![![![-1, 0, -2, 4, -2], ![12, -9, 6, -14, 8], ![-48, 44, -29, 52, -28], ![44, -40, 34, -55, 28], ![-76, 68, -64, 102, -51]]]
  hmulB := by decide  
  f := ![![![207, 112, 58, 8, -18]], ![![27, 15, 8, 2, -2]], ![![183, 100, 53, 12, -14]], ![![-4, 0, 2, 9, 4]], ![![119, 68, 38, 18, -5]]]
  g := ![![![3, 0, -2, 4, -2], ![-9, -9, 6, -14, 8], ![37, 44, -29, 52, -28], ![-42, -40, 34, -55, 28], ![79, 68, -64, 102, -51]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N2 : Nat.card (O ⧸ I73N2) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N2)

lemma isPrimeI73N2 : Ideal.IsPrime I73N2 := prime_ideal_of_norm_prime hp73.out _ NI73N2

def I73N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![177, -483, 217, 114, -122]] i)))

def SI73N3: IdealEqSpanCertificate' Table ![![177, -483, 217, 114, -122]] 
 ![![73, 0, 0, 0, 0], ![29, 1, 0, 0, 0], ![35, 0, 1, 0, 0], ![48, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![177, -483, 217, 114, -122], ![732, -520, -586, 33, 228], ![-1368, 1969, 99, -357, 66], ![-344, 179, 342, 4, -140], ![1642, -1889, -593, 288, 155]]]
  hmulB := by decide  
  f := ![![![-347, 65, 31, 600, 160]], ![![-151, 19, 21, 261, 80]], ![![-265, 36, 22, 435, 122]], ![![-356, 3, 74, 598, 224]], ![![-283, 6, 32, 432, 145]]]
  g := ![![![27, -483, 217, 114, -122], ![454, -520, -586, 33, 228], ![-620, 1969, 99, -357, 66], ![-229, 179, 342, 4, -140], ![853, -1889, -593, 288, 155]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N3 : Nat.card (O ⧸ I73N3) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N3)

lemma isPrimeI73N3 : Ideal.IsPrime I73N3 := prime_ideal_of_norm_prime hp73.out _ NI73N3
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![1783, 272, -459, -2731, -1268]] ![![-17, -9, -4, 1, 2]]
  ![![4705, 613, -1381, -7670, -3538]] where
 M := ![![![4705, 613, -1381, -7670, -3538]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI73N1 : IdealMulLeCertificate' Table 
  ![![4705, 613, -1381, -7670, -3538]] ![![-1, 0, -2, 4, -2]]
  ![![347, -65, -31, -600, -160]] where
 M := ![![![347, -65, -31, -600, -160]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI73N2 : IdealMulLeCertificate' Table 
  ![![347, -65, -31, -600, -160]] ![![177, -483, 217, 114, -122]]
  ![![73, 0, 0, 0, 0]] where
 M := ![![![-73, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1, I73N2, I73N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
    exact isPrimeI73N2
    exact isPrimeI73N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0 ⊙ MulI73N1 ⊙ MulI73N2)
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


def P79P0 : CertificateIrreducibleZModOfList' 79 5 2 6 [9, 50, 61, 42, 68, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 65, 59, 71, 21], [9, 57, 3, 18, 21], [25, 41, 75, 2, 41], [26, 73, 21, 67, 75], [0, 1]]
 g := ![![[23, 27, 53, 77, 2], [27, 38, 41, 26, 44], [10, 74, 7, 71, 26], [4, 30, 0, 11, 1], [], []], ![[52, 68, 63, 10, 22, 39, 57, 25], [26, 31, 28, 78, 25, 54, 3, 11], [8, 19, 26, 44, 28, 60, 23, 36], [5, 40, 40, 59, 10, 13, 11, 13], [66, 20, 67, 46], [2, 31, 12, 46]], ![[7, 67, 57, 27, 48, 36, 29, 76], [9, 6, 9, 13, 70, 63, 17, 10], [8, 69, 49, 4, 21, 30, 72, 36], [68, 30, 9, 47, 28, 49, 70, 9], [54, 55, 51, 44], [63, 76, 77, 46]], ![[17, 32, 67, 25, 61, 10, 15, 6], [70, 57, 50, 22, 67, 76, 32, 29], [9, 23, 65, 27, 52, 59, 63, 29], [72, 65, 74, 63, 73, 42, 55, 12], [38, 45, 54, 22], [47, 58, 11, 22]], ![[51, 42, 45, 68, 57, 55, 35, 74], [16, 7, 2, 58, 35, 17, 22, 60], [67, 77, 51, 69, 7, 16, 40, 37], [13, 41, 30, 6, 42, 46, 56, 34], [1, 25, 12, 32], [76, 5, 35, 16]]]
 h' := ![![[30, 65, 59, 71, 21], [73, 9, 18, 25, 9], [68, 51, 0, 55, 26], [43, 4, 73, 36, 42], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[9, 57, 3, 18, 21], [61, 48, 16, 78, 39], [24, 60, 36, 68, 25], [16, 55, 50, 5, 48], [49, 60, 10, 62, 11], [13, 45, 60, 14, 21], [30, 65, 59, 71, 21]], ![[25, 41, 75, 2, 41], [78, 5, 15, 25, 19], [26, 4, 8, 0, 61], [21, 1, 68, 23, 48], [53, 49, 8, 64, 55], [67, 36, 23, 22, 53], [9, 57, 3, 18, 21]], ![[26, 73, 21, 67, 75], [2, 16, 16, 56, 2], [0, 14, 62, 70, 54], [65, 63, 51, 58, 54], [14, 14, 34, 50, 61], [44, 47, 39, 69, 41], [25, 41, 75, 2, 41]], ![[0, 1], [60, 1, 14, 53, 10], [39, 29, 52, 44, 71], [7, 35, 74, 36, 45], [55, 35, 27, 61, 30], [71, 30, 35, 53, 43], [26, 73, 21, 67, 75]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25, 32, 21, 41], [], [], []]
 b := ![[], [61, 24, 37, 14, 62], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 5
  hpos := by decide
  P := [9, 50, 61, 42, 68, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11913661228623, 56651796768026, -56153466118452, -33556558457408, -80352150110062]
  a := ![-1, 7, -17, 8, -29]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![150805838337, 717111351494, -710803368588, -424766562752, -1017115824178]
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

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-51, 120, -34, -36, 16]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-51, 120, -34, -36, 16]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![73, 43, 73, 1, 0], ![21, 42, 48, 0, 1]] where
  M :=![![![-51, 120, -34, -36, 16], ![-96, 67, 118, -42, -72], ![432, -388, -93, -120, -84], ![280, 24, -130, -355, -132], ![-8, 400, 70, -552, -283]]]
  hmulB := by decide  
  f := ![![![-289, -96, -94, 60, 8]], ![![-48, -231, 58, -174, 120]], ![![-720, 428, -463, 720, -348]], ![![-907, 165, -455, 587, -232]], ![![-527, 118, -272, 360, -147]]]
  g := ![![![27, 12, 22, -36, 16], ![54, 59, 80, -42, -72], ![132, 100, 153, -120, -84], ![349, 251, 387, -355, -132], ![557, 434, 650, -552, -283]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [77, 73, 37, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 82, 29], [24, 0, 54], [0, 1]]
 g := ![![[59, 33, 31], [20, 36, 81], [74, 26], [2, 17], [51, 46, 1], []], ![[78, 55, 6, 41], [6, 46, 1, 64], [8, 16], [11, 48], [55, 63], [33, 11]], ![[57, 47, 28, 24], [8, 55, 1, 80], [18, 40], [19, 21], [71, 72, 79, 54], [8, 11]]]
 h' := ![![[22, 82, 29], [37, 79, 60], [24, 44, 9], [24, 3, 62], [57, 39, 73], [0, 0, 1], [0, 1]], ![[24, 0, 54], [33, 42, 50], [75, 53, 31], [44, 75, 4], [71, 10, 52], [18, 20], [22, 82, 29]], ![[0, 1], [31, 45, 56], [56, 69, 43], [23, 5, 17], [65, 34, 41], [43, 63, 82], [24, 0, 54]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51, 54], []]
 b := ![[], [63, 21, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [77, 73, 37, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![21443477, -19089772, 15947208, -26818190, 13873754]
  a := ![0, 4, 16, -26, 14]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![20335211, 6643310, 15755842, -26818190, 13873754]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 571787 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-125, 107, 82, -11, -30]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-125, 107, 82, -11, -30]] 
 ![![83, 0, 0, 0, 0], ![11, 1, 0, 0, 0], ![45, 0, 1, 0, 0], ![75, 0, 0, 1, 0], ![31, 0, 0, 0, 1]] where
  M :=![![![-125, 107, 82, -11, -30], ![180, -286, 14, 55, -22], ![132, 45, -245, -35, 110], ![-116, 167, 8, -30, 6], ![64, -287, 190, 75, -99]]]
  hmulB := by decide  
  f := ![![![5385, 2805, 1404, -245, -710]], ![![765, 397, 200, -36, -100]], ![![2955, 1544, 769, -130, -392]], ![![4909, 2552, 1282, -227, -644]], ![![2005, 1054, 520, -82, -269]]]
  g := ![![![-39, 107, 82, -11, -30], ![-9, -286, 14, 55, -22], ![119, 45, -245, -35, 110], ![-3, 167, 8, -30, 6], ![-95, -287, 190, 75, -99]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1

def I83N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, -29, -49, 0, 20]] i)))

def SI83N2: IdealEqSpanCertificate' Table ![![47, -29, -49, 0, 20]] 
 ![![83, 0, 0, 0, 0], ![18, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![16, 0, 0, 1, 0], ![19, 0, 0, 0, 1]] where
  M :=![![![47, -29, -49, 0, 20], ![-120, 156, 20, -27, 0], ![0, -113, 109, 33, -54], ![68, -87, -20, 14, 4], ![-106, 221, -61, -48, 39]]]
  hmulB := by decide  
  f := ![![![-183, 165, -149, 210, -134]], ![![-30, 28, -26, 33, -24]], ![![-48, 47, -41, 57, -38]], ![![8, 1, -4, -16, -8]], ![![-97, 98, -86, 114, -81]]]
  g := ![![![7, -29, -49, 0, 20], ![-32, 156, 20, -27, 0], ![20, -113, 109, 33, -54], ![18, -87, -20, 14, 4], ![-43, 221, -61, -48, 39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N2 : Nat.card (O ⧸ I83N2) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N2)

lemma isPrimeI83N2 : Ideal.IsPrime I83N2 := prime_ideal_of_norm_prime hp83.out _ NI83N2
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-51, 120, -34, -36, 16]] ![![-125, 107, 82, -11, -30]]
  ![![28687, -51911, 8580, 10631, -6650]] where
 M := ![![![28687, -51911, 8580, 10631, -6650]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI83N1 : IdealMulLeCertificate' Table 
  ![![28687, -51911, 8580, 10631, -6650]] ![![47, -29, -49, 0, 20]]
  ![![83, 0, 0, 0, 0]] where
 M := ![![![9005417, -12294126, -1315633, 2152771, -106406]]]
 hmul := by decide  
 g := ![![![![108499, -148122, -15851, 25937, -1282]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 19, -17, -124, -56]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![73, 19, -17, -124, -56]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![0, 0, 0, 89, 0], ![13, 68, 75, 34, 1]] where
  M :=![![![73, 19, -17, -124, -56], ![336, 46, -88, -511, -248], ![1488, 191, -377, -2263, -1022], ![2652, 433, -720, -4100, -1932], ![3894, 549, -969, -6000, -2747]]]
  hmulB := by decide  
  f := ![![![197, 103, 53, -10, -26]], ![![156, 76, 40, -7, -20]], ![![120, 63, 29, -7, -14]], ![![120, 65, 32, -6, -16]], ![![295, 151, 75, -15, -37]]]
  g := ![![![9, 43, 47, 20, -56], ![40, 190, 208, 89, -248], ![166, 783, 857, 365, -1022], ![312, 1481, 1620, 692, -1932], ![445, 2105, 2304, 982, -2747]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 4 2 6 [45, 73, 12, 70, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [84, 23, 82, 25], [50, 83, 36, 39], [63, 71, 60, 25], [0, 1]]
 g := ![![[10, 78, 26, 42], [4, 54, 87], [12, 1, 69], [82, 1, 72, 49], [19, 1], []], ![[39, 40, 47, 88, 5, 73], [64, 79, 84], [40, 45, 40], [23, 37, 22, 47, 73, 21], [48, 65, 74, 35, 1, 20], [53, 44, 2]], ![[54, 61, 25, 52, 43, 17], [0, 81, 40], [6, 7, 73], [1, 81, 50, 35, 40, 84], [20, 9, 85, 28, 16, 9], [12, 23, 8]], ![[27, 72, 4, 37, 18, 39], [14, 39, 55], [45, 32, 72], [71, 82, 4, 46, 57, 36], [22, 31, 53, 56, 5, 81], [56, 12, 2]]]
 h' := ![![[84, 23, 82, 25], [76, 50, 68, 65], [73, 58, 59, 40], [48, 0, 38, 46], [35, 81, 55, 82], [0, 0, 1], [0, 1]], ![[50, 83, 36, 39], [23, 66, 24, 45], [12, 60, 62, 66], [78, 84, 69, 29], [76, 4, 53, 29], [43, 62, 43, 28], [84, 23, 82, 25]], ![[63, 71, 60, 25], [42, 83, 78, 19], [65, 41, 47, 60], [35, 80, 9, 42], [12, 7, 59, 86], [2, 70, 29, 77], [50, 83, 36, 39]], ![[0, 1], [78, 68, 8, 49], [21, 19, 10, 12], [55, 14, 62, 61], [26, 86, 11, 70], [25, 46, 16, 73], [63, 71, 60, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [86, 31, 83], []]
 b := ![[], [], [49, 67, 56, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 4
  hpos := by decide
  P := [45, 73, 12, 70, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-14016690929, -28315700115, 28999093783, 28855542136, 44340165158]
  a := ![13, 7, -15, 5, -27]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6634144247, -34196032931, -37039475203, -16614719924, 44340165158]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 62742241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 103, 53, -10, -26]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![197, 103, 53, -10, -26]] 
 ![![89, 0, 0, 0, 0], ![21, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![10, 0, 0, 1, 0], ![32, 0, 0, 0, 1]] where
  M :=![![![197, 103, 53, -10, -26], ![156, 76, 40, -7, -20], ![120, 63, 29, -7, -14], ![120, 65, 32, -6, -16], ![6, -3, 3, 0, -1]]]
  hmulB := by decide  
  f := ![![![73, 19, -17, -124, -56]], ![![21, 5, -5, -35, -16]], ![![20, 3, -5, -31, -14]], ![![38, 7, -10, -60, -28]], ![![70, 13, -17, -112, -51]]]
  g := ![![![-14, 103, 53, -10, -26], ![-10, 76, 40, -7, -20], ![-9, 63, 29, -7, -14], ![-9, 65, 32, -6, -16], ![1, -3, 3, 0, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![73, 19, -17, -124, -56]] ![![197, 103, 53, -10, -26]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-29, -35, -149, 262, -122]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-29, -35, -149, 262, -122]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![0, 0, 0, 97, 0], ![71, 79, 37, 71, 1]] where
  M :=![![![-29, -35, -149, 262, -122], ![732, -508, 376, -917, 524], ![-3144, 2845, -1801, 3355, -1834], ![2864, -2621, 2192, -3538, 1800], ![-4894, 4439, -4183, 6552, -3259]]]
  hmulB := by decide  
  f := ![![![311, 49, -79, -472, -220]], ![![1320, 202, -344, -2029, -944]], ![![5664, 861, -1483, -8725, -4058]], ![![10444, 1587, -2736, -16092, -7484]], ![![11263, 1714, -2947, -17344, -8067]]]
  g := ![![![89, 99, 45, 92, -122], ![-376, -432, -196, -393, 524], ![1310, 1523, 681, 1377, -1834], ![-1288, -1493, -664, -1354, 1800], ![2335, 2700, 1200, 2453, -3259]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 4 2 6 [61, 76, 11, 12, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 7, 54, 90], [30, 60, 51, 1], [49, 29, 89, 6], [0, 1]]
 g := ![![[81, 70, 84, 61], [96, 76, 11], [43, 68, 79], [93, 74, 47], [36, 85, 1], []], ![[1, 64, 3, 33, 2, 84], [55, 38, 86], [55, 1, 75], [14, 36, 27], [11, 16, 81], [53, 66, 66, 96, 26, 45]], ![[87, 38, 2, 33, 64, 16], [27, 90, 61], [84, 45, 35], [30, 5, 48], [63, 79, 65], [41, 55, 6, 72, 44, 1]], ![[96, 90, 61, 13, 29, 12], [38, 55, 35], [5, 77, 61], [76, 70, 66], [61, 78, 11], [77, 45, 25, 21, 36, 22]]]
 h' := ![![[6, 7, 54, 90], [65, 60, 41, 62], [95, 9, 50, 37], [14, 40, 48, 51], [35, 33, 67, 12], [0, 0, 0, 1], [0, 1]], ![[30, 60, 51, 1], [22, 1, 18, 45], [46, 0, 14, 59], [43, 73, 23, 47], [11, 6, 91, 67], [87, 74, 96, 88], [6, 7, 54, 90]], ![[49, 29, 89, 6], [66, 86, 27, 4], [8, 16, 52, 62], [31, 2, 38, 61], [55, 5, 57, 57], [55, 38, 27, 68], [30, 60, 51, 1]], ![[0, 1], [13, 47, 11, 83], [10, 72, 78, 36], [86, 79, 85, 35], [58, 53, 76, 58], [44, 82, 71, 37], [49, 29, 89, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [96, 78, 89], []]
 b := ![[], [], [15, 44, 95, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 4
  hpos := by decide
  P := [61, 76, 11, 12, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-90141579, -26478468, 35992142, 142474994, 81355570]
  a := ![-1, 1, -2, -1, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-60478217, -66531634, -30661484, -58080108, 81355570]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 88529281 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![311, 49, -79, -472, -220]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![311, 49, -79, -472, -220]] 
 ![![97, 0, 0, 0, 0], ![52, 1, 0, 0, 0], ![12, 0, 1, 0, 0], ![72, 0, 0, 1, 0], ![52, 0, 0, 0, 1]] where
  M :=![![![311, 49, -79, -472, -220], ![1320, 202, -344, -2029, -944], ![5664, 861, -1483, -8725, -4058], ![10444, 1587, -2736, -16092, -7484], ![15058, 2287, -3947, -23208, -10793]]]
  hmulB := by decide  
  f := ![![![-29, -35, -149, 262, -122]], ![![-8, -24, -76, 131, -60]], ![![-36, 25, -37, 67, -34]], ![![8, -53, -88, 158, -72]], ![![-66, 27, -123, 208, -99]]]
  g := ![![![455, 49, -79, -472, -220], ![1960, 202, -344, -2029, -944], ![8432, 861, -1483, -8725, -4058], ![15552, 1587, -2736, -16092, -7484], ![22430, 2287, -3947, -23208, -10793]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-29, -35, -149, 262, -122]] ![![311, 49, -79, -472, -220]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-263, -131, -60, 39, 44]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![-263, -131, -60, 39, 44]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![84, 74, 1, 0, 0], ![77, 45, 0, 1, 0], ![100, 81, 0, 0, 1]] where
  M :=![![![-263, -131, -60, 39, 44], ![-264, -110, -32, 123, 78], ![-468, -121, 45, 495, 246], ![-736, -167, 114, 908, 438], ![-844, -133, 218, 1299, 605]]]
  hmulB := by decide  
  f := ![![![973, -859, 718, -1221, 632]], ![![-3792, 3372, -2798, 4725, -2442]], ![![-1824, 1627, -1345, 2265, -1170]], ![![-1099, 982, -812, 1364, -704]], ![![-1800, 1607, -1326, 2232, -1153]]]
  g := ![![![-26, -10, -60, 39, 44], ![-147, -95, -32, 123, 78], ![-663, -452, 45, 495, 246], ![-1228, -841, 114, 908, 438], ![-1779, -1225, 218, 1299, 605]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [27, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [94, 100], [0, 1]]
 g := ![![[4, 68], [36], [3, 30], [37], [80], [94, 1]], ![[33, 33], [36], [96, 71], [37], [80], [87, 100]]]
 h' := ![![[94, 100], [34, 13], [20, 95], [44, 38], [29, 80], [88, 22], [0, 1]], ![[0, 1], [44, 88], [62, 6], [81, 63], [75, 21], [35, 79], [94, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48]]
 b := ![[], [84, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [27, 7, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1329, -1367, 1512, 2459, 2560]
  a := ![3, -3, 4, 2, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5680, -4270, 1512, 2459, 2560]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 16, -3, 11, -8]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![5, 16, -3, 11, -8]] 
 ![![101, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![37, 0, 1, 0, 0], ![51, 0, 0, 1, 0], ![59, 0, 0, 0, 1]] where
  M :=![![![5, 16, -3, 11, -8], ![48, -27, 30, -46, 22], ![-132, 130, -103, 176, -92], ![156, -126, 112, -185, 94], ![-270, 240, -201, 339, -175]]]
  hmulB := by decide  
  f := ![![![13, 68, 5, -103, -50]], ![![4, 5, 0, -12, -6]], ![![17, 26, -2, -55, -26]], ![![27, 38, -3, -84, -40]], ![![37, 44, -4, -106, -51]]]
  g := ![![![-1, 16, -3, 11, -8], ![2, -27, 30, -46, 22], ![-9, 130, -103, 176, -92], ![9, -126, 112, -185, 94], ![-17, 240, -201, 339, -175]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![575, 300, 146, -30, -72]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![575, 300, 146, -30, -72]] 
 ![![101, 0, 0, 0, 0], ![30, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![24, 0, 0, 1, 0], ![93, 0, 0, 0, 1]] where
  M :=![![![575, 300, 146, -30, -72], ![432, 243, 124, -24, -60], ![360, 152, 95, -12, -48], ![360, 176, 88, -17, -44], ![-12, 36, 6, -6, -1]]]
  hmulB := by decide  
  f := ![![![763, 100, -186, -1170, -528]], ![![258, 35, -64, -396, -180]], ![![207, 28, -51, -318, -144]], ![![432, 64, -112, -665, -308]], ![![1071, 144, -264, -1644, -745]]]
  g := ![![![-23, 300, 146, -30, -72], ![-18, 243, 124, -24, -60], ![-3, 152, 95, -12, -48], ![-12, 176, 88, -17, -44], ![-9, 36, 6, -6, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2

def I101N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 79, 42, 1, -16]] i)))

def SI101N3: IdealEqSpanCertificate' Table ![![149, 79, 42, 1, -16]] 
 ![![101, 0, 0, 0, 0], ![90, 1, 0, 0, 0], ![81, 0, 1, 0, 0], ![51, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![149, 79, 42, 1, -16], ![96, 58, 38, 31, 2], ![-12, 33, 51, 157, 62], ![-96, 19, 76, 290, 126], ![-276, -39, 72, 429, 197]]]
  hmulB := by decide  
  f := ![![![769, -2009, 848, 469, -484]], ![![714, -1810, 732, 419, -422]], ![![561, -1532, 685, 362, -386]], ![![375, -1008, 442, 237, -250]], ![![119, -214, 34, 44, -27]]]
  g := ![![![-102, 79, 42, 1, -16], ![-97, 58, 38, 31, 2], ![-154, 33, 51, 157, 62], ![-234, 19, 76, 290, 126], ![-256, -39, 72, 429, 197]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N3 : Nat.card (O ⧸ I101N3) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N3)

lemma isPrimeI101N3 : Ideal.IsPrime I101N3 := prime_ideal_of_norm_prime hp101.out _ NI101N3
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![-263, -131, -60, 39, 44]] ![![5, 16, -3, 11, -8]]
  ![![-5479, -2825, -1437, 274, 708]] where
 M := ![![![-5479, -2825, -1437, 274, 708]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![-5479, -2825, -1437, 274, 708]] ![![575, 300, 146, -30, -72]]
  ![![-4798001, -2474887, -1258389, 240508, 620200]] where
 M := ![![![-4798001, -2474887, -1258389, 240508, 620200]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI101N2 : IdealMulLeCertificate' Table 
  ![![-4798001, -2474887, -1258389, 240508, 620200]] ![![149, 79, 42, 1, -16]]
  ![![101, 0, 0, 0, 0]] where
 M := ![![![-1131654601, -583730510, -296806579, 56726549, 146281532]]]
 hmul := by decide  
 g := ![![![![-11204501, -5779510, -2938679, 561649, 1448332]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1929, 315, -501, -2932, -1380]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![1929, 315, -501, -2932, -1380]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![89, 16, 39, 1, 0], ![2, 59, 57, 0, 1]] where
  M :=![![![1929, 315, -501, -2932, -1380], ![8280, 1222, -2116, -12715, -5864], ![35184, 5519, -9377, -54247, -25430], ![65348, 9753, -16948, -100640, -46596], ![93662, 14549, -24865, -144444, -67559]]]
  hmulB := by decide  
  f := ![![![-1717, 1089, 1511, -38, -602]], ![![3612, -4996, -460, 883, -76]], ![![456, 2961, -3653, -953, 1766]], ![![-771, 1313, -144, -261, 136]], ![![2316, -1266, -2234, -8, 909]]]
  g := ![![![2579, 1249, 1869, -2932, -1380], ![11181, 5346, 8039, -12715, -5864], ![47709, 23047, 34522, -54247, -25430], ![88500, 42419, 63728, -100640, -46596], ![127032, 61278, 91838, -144444, -67559]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [11, 2, 41, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [14, 78, 79], [48, 24, 24], [0, 1]]
 g := ![![[83, 74, 19], [42, 46, 30], [67, 88, 14], [84, 56], [47, 33], [1]], ![[95, 63, 91, 66], [48, 11, 83, 64], [18, 30, 29, 76], [98, 25], [20, 81], [81, 49, 35, 81]], ![[30, 84, 4, 12], [45, 64, 13, 22], [74, 24, 72, 5], [89, 33], [23, 28], [53, 28, 91, 22]]]
 h' := ![![[14, 78, 79], [53, 78, 88], [87, 59, 37], [53, 8, 80], [16, 102, 46], [92, 101, 62], [0, 1]], ![[48, 24, 24], [46, 82, 34], [12, 91, 90], [18, 18, 80], [90, 1, 98], [102, 49, 94], [14, 78, 79]], ![[0, 1], [32, 46, 84], [52, 56, 79], [20, 77, 46], [81, 0, 62], [5, 56, 50], [48, 24, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [98, 8], []]
 b := ![[], [4, 46, 69], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [11, 2, 41, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-290905, -14052280, 13629866, 4321850, 18540958]
  a := ![1, -5, 12, -5, 21]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4097257, -11428334, -11764630, 4321850, 18540958]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 1092727 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1717, -1089, -1511, 38, 602]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![1717, -1089, -1511, 38, 602]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![58, 88, 1, 0, 0], ![69, 42, 0, 1, 0], ![6, 78, 0, 0, 1]] where
  M :=![![![1717, -1089, -1511, 38, 602], ![-3612, 4996, 460, -883, 76], ![-456, -2961, 3653, 953, -1766], ![2176, -2775, -516, 462, 72], ![-2882, 6589, -2237, -1476, 1347]]]
  hmulB := by decide  
  f := ![![![-1929, -315, 501, 2932, 1380]], ![![-8280, -1222, 2116, 12715, 5864]], ![![-8502, -1275, 2181, 13041, 6034]], ![![-5303, -804, 1363, 8126, 3768]], ![![-7292, -1085, 1873, 11202, 5177]]]
  g := ![![![807, 809, -1511, 38, 602], ![293, -42, 460, -883, 76], ![-2597, -2201, 3653, 953, -1766], ![-2, 171, -516, 462, 72], ![2142, 1557, -2237, -1476, 1347]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P1 : CertificateIrreducibleZModOfList' 103 2 2 6 [29, 99, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 102], [0, 1]]
 g := ![![[78, 32], [92, 49], [86, 64], [50], [66], [4, 1]], ![[0, 71], [82, 54], [33, 39], [50], [66], [8, 102]]]
 h' := ![![[4, 102], [10, 49], [81, 96], [28, 8], [6, 87], [90, 90], [0, 1]], ![[0, 1], [0, 54], [53, 7], [60, 95], [45, 16], [38, 13], [4, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [70, 68]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N1 : CertifiedPrimeIdeal' SI103N1 103 where
  n := 2
  hpos := by decide
  P := [29, 99, 1]
  hirr := P103P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![495, -62, -54, 44, -56]
  a := ![4, 0, -1, 1, -1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![9, 70, -54, 44, -56]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N1 B_one_repr
lemma NI103N1 : Nat.card (O ⧸ I103N1) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![1929, 315, -501, -2932, -1380]] ![![1717, -1089, -1511, 38, 602]]
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


lemma PB1705I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB1705I2 : PrimesBelowBoundCertificateInterval O 61 103 1705 where
  m := 9
  g := ![2, 2, 4, 1, 3, 2, 2, 4, 2]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB1705I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1, I73N2, I73N3]
    · exact ![I79N0]
    · exact ![I83N0, I83N1, I83N2]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1, I101N2, I101N3]
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
    · exact ![25411681, 71]
    · exact ![5329, 73, 73, 73]
    · exact ![3077056399]
    · exact ![571787, 83, 83]
    · exact ![62742241, 89]
    · exact ![88529281, 97]
    · exact ![10201, 101, 101, 101]
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
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
      exact NI73N2
      exact NI73N3
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
      exact NI101N2
      exact NI101N3
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
  β := ![I71N1, I73N1, I73N2, I73N3, I83N1, I83N2, I89N1, I97N1, I101N1, I101N2, I101N3]
  Il := ![[], [I71N1], [I73N1, I73N2, I73N3], [], [I83N1, I83N2], [I89N1], [I97N1], [I101N1, I101N2, I101N3], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
