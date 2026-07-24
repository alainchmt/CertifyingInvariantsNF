
import IdealArithmetic.Examples.NF5_3_364500000_2.RI5_3_364500000_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![629, 490, 222, -77, -88]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![629, 490, 222, -77, -88]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![0, 0, 67, 0, 0], ![47, 30, 64, 1, 0], ![37, 23, 10, 0, 1]] where
  M :=![![![629, 490, 222, -77, -88], ![2112, 1665, 782, -260, -308], ![3696, 2881, 1309, -450, -520], ![5184, 4080, 1900, -641, -746], ![5268, 4110, 1878, -637, -747]]]
  hmulB := by decide  
  f := ![![![191, 8, -50, -5, 14]], ![![-336, -23, 82, 12, -20]], ![![240, -5, -75, 2, 24]], ![![211, -10, -70, 4, 24]], ![![29, -5, -12, 2, 5]]]
  g := ![![![112, 72, 90, -77, -88], ![384, 247, 306, -260, -308], ![658, 423, 527, -450, -520], ![939, 604, 752, -641, -746], ![938, 603, 748, -637, -747]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [32, 50, 28, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [52, 55, 49], [54, 11, 18], [0, 1]]
 g := ![![[57, 66, 55], [18, 52, 24], [45, 56], [49, 9], [39, 1], []], ![[61, 45, 38, 64], [50, 25, 32, 21], [31, 47], [63, 1], [65, 54], [3, 56]], ![[31, 63, 49, 38], [30, 40, 22, 57], [8, 39], [27, 16], [9, 10], [34, 56]]]
 h' := ![![[52, 55, 49], [27, 46, 16], [59, 25, 52], [62, 2, 18], [25, 28, 64], [0, 0, 1], [0, 1]], ![[54, 11, 18], [61, 65, 18], [27, 47, 55], [9, 42, 28], [22, 55, 66], [62, 26, 11], [52, 55, 49]], ![[0, 1], [1, 23, 33], [52, 62, 27], [43, 23, 21], [6, 51, 4], [19, 41, 55], [54, 11, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21, 29], []]
 b := ![[], [9, 66, 50], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [32, 50, 28, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11094020, 6384547, 1727772, -2990116, -2312707]
  a := ![0, -7, 2, -4, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3540293, 2228064, 3227198, -2990116, -2312707]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 300763 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25, 20, 10, -3, -4]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![25, 20, 10, -3, -4]] 
 ![![67, 0, 0, 0, 0], ![14, 1, 0, 0, 0], ![36, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![13, 0, 0, 0, 1]] where
  M :=![![![25, 20, 10, -3, -4], ![96, 73, 30, -12, -12], ![144, 117, 61, -18, -24], ![240, 180, 72, -29, -30], ![204, 168, 90, -27, -35]]]
  hmulB := by decide  
  f := ![![![-1229, -50, 314, 33, -86]], ![![-226, -9, 58, 6, -16]], ![![-684, -27, 175, 18, -48]], ![![-159, -6, 42, 4, -12]], ![![-263, -8, 68, 6, -19]]]
  g := ![![![-8, 20, 10, -3, -4], ![-26, 73, 30, -12, -12], ![-48, 117, 61, -18, -24], ![-63, 180, 72, -29, -30], ![-70, 168, 90, -27, -35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![577, 350, 108, -159, -128]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![577, 350, 108, -159, -128]] 
 ![![67, 0, 0, 0, 0], ![59, 1, 0, 0, 0], ![35, 0, 1, 0, 0], ![10, 0, 0, 1, 0], ![8, 0, 0, 0, 1]] where
  M :=![![![577, 350, 108, -159, -128], ![3072, 1775, 506, -808, -636], ![7632, 4479, 1311, -2038, -1616], ![17856, 10434, 3032, -4749, -3758], ![24828, 14534, 4236, -6615, -5239]]]
  hmulB := by decide  
  f := ![![![1627, 524, -740, -35, 150]], ![![1379, 449, -626, -35, 130]], ![![875, 267, -399, -1, 70]], ![![370, 154, -164, -49, 58]], ![![20, -36, -12, 51, -29]]]
  g := ![![![-317, 350, 108, -159, -128], ![-1585, 1775, 506, -808, -636], ![-4018, 4479, 1311, -2038, -1616], ![-9348, 10434, 3032, -4749, -3758], ![-13028, 14534, 4236, -6615, -5239]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![629, 490, 222, -77, -88]] ![![25, 20, 10, -3, -4]]
  ![![58301, 45680, 21068, -7154, -8334]] where
 M := ![![![58301, 45680, 21068, -7154, -8334]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![58301, 45680, 21068, -7154, -8334]] ![![577, 350, 108, -159, -128]]
  ![![67, 0, 0, 0, 0]] where
 M := ![![![101237, 79730, 36984, -12127, -14338]]]
 hmul := by decide  
 g := ![![![![1511, 1190, 552, -181, -214]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![527, 194, -240, -40, 66]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![527, 194, -240, -40, 66]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![40, 60, 66, 1, 0], ![29, 35, 17, 0, 1]] where
  M :=![![![527, 194, -240, -40, 66], ![-1584, -519, 732, 48, -160], ![1920, 502, -887, 92, 96], ![-360, 340, 236, -527, 264], ![168, -510, -112, 668, -399]]]
  hmulB := by decide  
  f := ![![![2329, 1842, 856, -288, -338]], ![![8112, 6327, 2908, -992, -1152]], ![![13824, 10854, 5015, -1700, -1984]], ![![21296, 16692, 7702, -2615, -3048]], ![![8539, 6689, 3085, -1048, -1221]]]
  g := ![![![3, 4, 18, -40, 66], ![16, 31, 4, 48, -160], ![-64, -118, -121, 92, 96], ![184, 320, 430, -527, 264], ![-211, -375, -527, 668, -399]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [3, 45, 67, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 37, 4], [48, 33, 67], [0, 1]]
 g := ![![[62, 58, 8], [62, 9, 16], [25, 48, 16], [62, 60], [4, 1], []], ![[42, 33, 4, 15], [44, 21, 27, 16], [3, 2, 41, 18], [26, 12], [62, 24], [5, 16]], ![[20, 51, 66, 52], [7, 63, 64, 55], [43, 17, 39, 68], [45, 54], [17, 20], [13, 16]]]
 h' := ![![[27, 37, 4], [27, 39, 24], [67, 69, 67], [29, 2, 67], [59, 30, 42], [0, 0, 1], [0, 1]], ![[48, 33, 67], [40, 30, 25], [68, 55, 2], [67, 61, 18], [43, 4, 15], [4, 21, 33], [27, 37, 4]], ![[0, 1], [27, 2, 22], [70, 18, 2], [11, 8, 57], [69, 37, 14], [64, 50, 37], [48, 33, 67]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 47], []]
 b := ![[], [41, 26, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [3, 45, 67, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1228651464, 589159987, -138778433, -248678999, -81175187]
  a := ![3, -62, -1, -65, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![190561857, 258465232, 248648080, -248678999, -81175187]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 357911 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2329, 1842, 856, -288, -338]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![2329, 1842, 856, -288, -338]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![58, 5, 1, 0, 0], ![65, 40, 0, 1, 0], ![5, 8, 0, 0, 1]] where
  M :=![![![2329, 1842, 856, -288, -338], ![8112, 6327, 2908, -992, -1152], ![13824, 10854, 5015, -1700, -1984], ![19752, 15468, 7132, -2425, -2824], ![19800, 15538, 7176, -2436, -2841]]]
  hmulB := by decide  
  f := ![![![527, 194, -240, -40, 66]], ![![-1584, -519, 732, 48, -160]], ![![346, 129, -157, -28, 44]], ![![-415, -110, 196, -17, -26]], ![![-139, -52, 64, 12, -19]]]
  g := ![![![-379, 166, 856, -288, -338], ![-1272, 573, 2908, -992, -1152], ![-2206, 981, 5015, -1700, -1984], ![-3129, 1400, 7132, -2425, -2824], ![-3153, 1406, 7176, -2436, -2841]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P1 : CertificateIrreducibleZModOfList' 71 2 2 6 [20, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [70, 70], [0, 1]]
 g := ![![[32, 32], [45, 45], [70, 9], [30], [1], [1]], ![[0, 39], [0, 26], [61, 62], [30], [1], [1]]]
 h' := ![![[70, 70], [23, 23], [20, 20], [25, 3], [25, 39], [51, 70], [0, 1]], ![[0, 1], [0, 48], [0, 51], [22, 68], [57, 32], [52, 1], [70, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [9, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N1 : CertifiedPrimeIdeal' SI71N1 71 where
  n := 2
  hpos := by decide
  P := [20, 1, 1]
  hirr := P71P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8426, -4436, -830, 2479, 1858]
  a := ![1, -6, 1, -5, -4]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1841, -1610, -830, 2479, 1858]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N1 B_one_repr
lemma NI71N1 : Nat.card (O ⧸ I71N1) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![527, 194, -240, -40, 66]] ![![2329, 1842, 856, -288, -338]]
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


def P73P0 : CertificateIrreducibleZModOfList' 73 5 2 6 [42, 10, 51, 38, 6, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 60, 63, 18, 30], [65, 23, 32, 59, 4], [62, 35, 69, 62, 64], [65, 27, 55, 7, 48], [0, 1]]
 g := ![![[36, 11, 28, 64, 25], [46, 26, 20, 71], [72, 60, 19, 64], [41, 43, 71, 67, 1], [], []], ![[28, 71, 6, 49, 2, 54, 57, 34], [30, 3, 1, 46], [39, 21, 71, 67], [53, 64, 38, 28, 71, 31, 20, 45], [62, 55, 26, 8], [45, 58, 60, 24]], ![[46, 49, 28, 28, 19, 20, 22, 61], [13, 32, 70, 24], [14, 61, 71, 38], [23, 54, 46, 5, 8, 40, 4, 54], [6, 56, 45, 57], [43, 70, 11, 16]], ![[9, 38, 55, 16, 3, 17, 69, 57], [48, 39, 3, 2], [45, 51, 34, 32], [19, 71, 36, 35, 11, 18, 35, 1], [24, 46, 26, 70], [0, 11, 4, 8]], ![[42, 26, 37, 35, 51, 25, 71, 24], [36, 6, 63, 1], [41, 65, 66, 50], [60, 55, 59, 60, 44, 28, 28, 35], [31, 51, 34, 72], [58, 47, 61, 41]]]
 h' := ![![[21, 60, 63, 18, 30], [15, 21, 8, 37, 68], [66, 18, 58, 49, 12], [30, 47, 45, 25, 65], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[65, 23, 32, 59, 4], [0, 23, 61, 52, 15], [47, 4, 68, 2, 51], [58, 11, 14, 68, 33], [72, 41, 49, 45, 29], [11, 72, 48, 69, 9], [21, 60, 63, 18, 30]], ![[62, 35, 69, 62, 64], [34, 47, 6, 20, 56], [19, 65, 46, 67, 43], [60, 48, 56, 54, 44], [67, 62, 59, 17, 14], [10, 58, 20, 17, 35], [65, 23, 32, 59, 4]], ![[65, 27, 55, 7, 48], [22, 66, 31, 71, 23], [40, 20, 37, 26, 41], [18, 32, 5, 59, 18], [55, 6, 13, 40, 64], [48, 9, 13, 47, 56], [62, 35, 69, 62, 64]], ![[0, 1], [53, 62, 40, 39, 57], [18, 39, 10, 2, 72], [39, 8, 26, 13, 59], [67, 37, 25, 44, 38], [37, 7, 64, 13, 46], [65, 27, 55, 7, 48]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58, 29, 42, 58], [], [], []]
 b := ![[], [37, 19, 28, 67, 37], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 5
  hpos := by decide
  P := [42, 10, 51, 38, 6, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-202529167496624, -118157845314969, -34190795333864, 54047246620302, 42717779232978]
  a := ![1, 25, -3, 18, 13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2774372157488, -1618600620753, -468367059368, 740373241374, 585175057986]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, -3, 0, 1, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![-7, -3, 0, 1, 0]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![29, 52, 1, 0, 0], ![72, 76, 0, 1, 0], ![58, 4, 0, 0, 1]] where
  M :=![![![-7, -3, 0, 1, 0], ![0, -5, -8, 0, 4], ![-48, -26, 3, 8, 0], ![0, -12, -30, 3, 14], ![-108, -55, 12, 17, 1]]]
  hmulB := by decide  
  f := ![![![-49, -3, 10, 1, -2]], ![![48, -15, -16, 4, 4]], ![![13, -11, -7, 3, 2]], ![![0, -18, -6, 5, 2]], ![![-34, -3, 6, 1, -1]]]
  g := ![![![-1, -1, 0, 1, 0], ![0, 5, -8, 0, 4], ![-9, -10, 3, 8, 0], ![-2, 16, -30, 3, 14], ![-22, -25, 12, 17, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [17, 17, 1] where
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
 g := ![![[1, 73], [34, 38], [24, 13], [67, 21], [52], [1]], ![[24, 6], [20, 41], [40, 66], [26, 58], [52], [1]]]
 h' := ![![[62, 78], [54, 51], [66, 65], [46, 31], [37, 10], [62, 62], [0, 1]], ![[0, 1], [56, 28], [67, 14], [72, 48], [25, 69], [35, 17], [62, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [6, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [17, 17, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![12421, -387, -24546, 3849, 13314]
  a := ![-1, -7, 5, 5, -19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4115, 11775, -24546, 3849, 13314]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-175, 1704, 1380, -745, -896]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![-175, 1704, 1380, -745, -896]] 
 ![![79, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![61, 0, 1, 0, 0], ![51, 0, 0, 1, 0], ![30, 0, 0, 0, 1]] where
  M :=![![![-175, 1704, 1380, -745, -896], ![21504, 9571, 1314, -4408, -2980], ![35760, 23391, 8019, -10606, -8816], ![95040, 54986, 15708, -25041, -19722], ![125460, 76312, 23644, -34689, -27959]]]
  hmulB := by decide  
  f := ![![![10727, 4386, -4436, -1149, 1398]], ![![390, 189, -126, -58, 48]], ![![8981, 3629, -3715, -909, 1138]], ![![6435, 2764, -2588, -812, 888]], ![![4722, 1810, -1948, -353, 519]]]
  g := ![![![-376, 1704, 1380, -745, -896], ![2508, 9571, 1314, -4408, -2980], ![2679, 23391, 8019, -10606, -8816], ![8553, 54986, 15708, -25041, -19722], ![10547, 76312, 23644, -34689, -27959]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1

def I79N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2165, -92, 548, 62, -150]] i)))

def SI79N2: IdealEqSpanCertificate' Table ![![-2165, -92, 548, 62, -150]] 
 ![![79, 0, 0, 0, 0], ![11, 1, 0, 0, 0], ![58, 0, 1, 0, 0], ![31, 0, 0, 1, 0], ![37, 0, 0, 0, 1]] where
  M :=![![![-2165, -92, 548, 62, -150], ![3600, 157, -908, -104, 248], ![-2976, -122, 757, 84, -208], ![696, 40, -168, -23, 44], ![-3552, -140, 908, 98, -251]]]
  hmulB := by decide  
  f := ![![![-227, -36, 116, -34, -2]], ![![-31, -7, 16, -2, -2]], ![![-146, -14, 77, -32, 4]], ![![-155, -44, 76, -1, -14]], ![![-17, 24, 16, -32, 15]]]
  g := ![![![-371, -92, 548, 62, -150], ![615, 157, -908, -104, 248], ![-512, -122, 757, 84, -208], ![115, 40, -168, -23, 44], ![-613, -140, 908, 98, -251]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N2 : Nat.card (O ⧸ I79N2) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N2)

lemma isPrimeI79N2 : Ideal.IsPrime I79N2 := prime_ideal_of_norm_prime hp79.out _ NI79N2

def I79N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-23125, -984, 5852, 662, -1602]] i)))

def SI79N3: IdealEqSpanCertificate' Table ![![-23125, -984, 5852, 662, -1602]] 
 ![![79, 0, 0, 0, 0], ![37, 1, 0, 0, 0], ![66, 0, 1, 0, 0], ![64, 0, 0, 1, 0], ![15, 0, 0, 0, 1]] where
  M :=![![![-23125, -984, 5852, 662, -1602], ![38448, 1673, -9700, -1112, 2648], ![-31776, -1302, 8081, 892, -2224], ![7464, 440, -1792, -259, 460], ![-37872, -1464, 9700, 1026, -2695]]]
  hmulB := by decide  
  f := ![![![9533, 2208, -4468, 774, 322]], ![![4367, 1073, -2040, 282, 190]], ![![7494, 1526, -3535, 856, 108]], ![![9704, 2728, -4496, 221, 660]], ![![-771, -784, 296, 652, -445]]]
  g := ![![![-4953, -984, 5852, 662, -1602], ![8205, 1673, -9700, -1112, 2648], ![-6844, -1302, 8081, 892, -2224], ![1508, 440, -1792, -259, 460], ![-8217, -1464, 9700, 1026, -2695]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N3 : Nat.card (O ⧸ I79N3) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N3)

lemma isPrimeI79N3 : Ideal.IsPrime I79N3 := prime_ideal_of_norm_prime hp79.out _ NI79N3
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![-7, -3, 0, 1, 0]] ![![-175, 1704, 1380, -745, -896]]
  ![![31753, 14345, 2106, -6602, -4510]] where
 M := ![![![31753, 14345, 2106, -6602, -4510]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI79N1 : IdealMulLeCertificate' Table 
  ![![31753, 14345, 2106, -6602, -4510]] ![![-2165, -92, 548, 62, -150]]
  ![![-11946173, -558723, 2983682, 363576, -801916]] where
 M := ![![![-11946173, -558723, 2983682, 363576, -801916]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI79N2 : IdealMulLeCertificate' Table 
  ![![-11946173, -558723, 2983682, 363576, -801916]] ![![-23125, -984, 5852, 662, -1602]]
  ![![79, 0, 0, 0, 0]] where
 M := ![![![193047883505, 8269515153, -48808370446, -5542554206, 13350970454]]]
 hmul := by decide  
 g := ![![![![2443644095, 104677407, -617827474, -70158914, 168999626]]]]
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

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0, 0, 0]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0, 0, 0]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![0, 0, 0, 83, 0], ![0, 0, 0, 0, 83]] where
  M :=![![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![0, 0, 0, 83, 0], ![0, 0, 0, 0, 83]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 5 2 6 [7, 12, 38, 53, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 36, 59, 23, 51], [69, 82, 3, 30, 45], [57, 31, 3, 64, 12], [0, 16, 18, 49, 58], [0, 1]]
 g := ![![[18, 34, 20, 43, 69], [33, 28, 5, 14, 7], [43, 72, 11, 4], [44, 70], [1], []], ![[66, 63, 9, 22, 24, 75, 12, 10], [14, 41, 13, 78, 59, 36, 32, 12], [76, 40, 57, 38], [37, 66, 10, 44], [56, 36, 47, 2, 79, 4, 60, 10], [6, 0, 22, 28]], ![[79, 18, 72, 63, 73, 31, 70, 18], [50, 80, 41, 82, 47, 39, 47, 46], [27, 38, 54, 4], [18, 23, 18, 48], [59, 28, 31, 40, 10, 75, 24, 45], [73, 2, 44, 33]], ![[45, 19, 73, 6, 53, 56, 72, 10], [2, 68, 75, 32, 31, 76, 62, 30], [39, 23, 29, 41], [1, 34, 4, 29], [30, 32, 30, 58, 15, 58, 75, 30], [70, 22, 42, 61]], ![[0, 16, 69, 60, 14, 4, 14, 52], [42, 79, 34, 69, 21, 18, 20, 22], [61, 38, 76, 63], [36, 55, 19, 41], [44, 40, 24, 10, 22, 36, 7, 43], [77, 82, 40, 44]]]
 h' := ![![[40, 36, 59, 23, 51], [18, 52, 26, 16, 61], [48, 44, 17, 67, 67], [73, 63, 73, 65, 2], [76, 71, 45, 30], [0, 0, 1], [0, 1]], ![[69, 82, 3, 30, 45], [12, 36, 82, 29, 77], [56, 53, 7, 44, 50], [16, 0, 9, 54, 72], [21, 69, 12, 33, 58], [64, 69, 73, 81, 77], [40, 36, 59, 23, 51]], ![[57, 31, 3, 64, 12], [18, 80, 50, 53, 10], [38, 24, 80, 6, 5], [71, 9, 9, 28, 81], [23, 12, 73, 72, 52], [17, 51, 48, 11, 1], [69, 82, 3, 30, 45]], ![[0, 16, 18, 49, 58], [40, 38, 53, 28, 30], [7, 54, 57, 56, 25], [23, 78, 74, 77, 46], [14, 71, 50, 70, 19], [20, 50, 77, 13, 25], [57, 31, 3, 64, 12]], ![[0, 1], [38, 43, 38, 40, 71], [52, 74, 5, 76, 19], [75, 16, 1, 25, 48], [24, 26, 69, 44, 37], [42, 79, 50, 61, 63], [0, 16, 18, 49, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66, 69, 25, 55], [], [], []]
 b := ![[], [3, 7, 49, 53, 51], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 5
  hpos := by decide
  P := [7, 12, 38, 53, 0, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2363339410649, -918470583784, 1073543720104, 246129069840, -341568159656]
  a := ![0, -4, -2, -18, 10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-28473968803, -11065910648, 12934261688, 2965410480, -4115279032]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 3939040643 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def PBC83 : ContainsPrimesAboveP 83 ![I83N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![83, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 83 (by decide) 𝕀

instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![51811, 2152, -13152, -1458, 3618]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![51811, 2152, -13152, -1458, 3618]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![83, 52, 1, 0, 0], ![45, 8, 0, 1, 0], ![21, 30, 0, 0, 1]] where
  M :=![![![51811, 2152, -13152, -1458, 3618], ![-86832, -4055, 21692, 2640, -5832], ![69984, 2146, -18359, -1636, 5280], ![-19944, -2836, 3496, 1441, -356], ![80544, 688, -22520, -1102, 6997]]]
  hmulB := by decide  
  f := ![![![-1213, -752, 64, 194, -38]], ![![912, -343, -2044, -176, 776]], ![![-703, -958, -1119, 90, 414]], ![![-489, -420, -216, 83, 70]], ![![-153, -378, -640, 0, 247]]]
  g := ![![![12731, 6620, -13152, -1458, 3618], ![-21164, -10991, 21692, 2640, -5832], ![17489, 9118, -18359, -1636, 5280], ![-4129, -2084, 3496, 1441, -356], ![20813, 10906, -22520, -1102, 6997]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [16, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [87, 88], [0, 1]]
 g := ![![[78, 39], [69], [25], [35, 81], [56, 4], [1]], ![[0, 50], [69], [25], [51, 8], [48, 85], [1]]]
 h' := ![![[87, 88], [45, 67], [9, 46], [63, 5], [83, 80], [73, 87], [0, 1]], ![[0, 1], [0, 22], [6, 43], [53, 84], [12, 9], [77, 2], [87, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [3, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [16, 2, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2897, -5558, -13354, 4798, 8261]
  a := ![13, -7, 4, 2, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![8046, 4524, -13354, 4798, 8261]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-26531, -16110, -4978, 7326, 5900]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![-26531, -16110, -4978, 7326, 5900]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![52, 44, 1, 0, 0], ![26, 4, 0, 1, 0], ![11, 30, 0, 0, 1]] where
  M :=![![![-26531, -16110, -4978, 7326, 5900], ![-141600, -81757, -23272, 37244, 29304], ![-351648, -206364, -60393, 93944, 74488], ![-823056, -480882, -139696, 218937, 173236], ![-1144440, -669922, -195234, 304974, 241529]]]
  hmulB := by decide  
  f := ![![![26477, 14318, -11522, -7510, 6556]], ![![-157344, -72181, 69880, 29404, -30040]], ![![-58268, -25624, 25999, 9584, -10360]], ![![-6382, -1738, 2964, -211, -396]], ![![-41089, -19298, 18200, 8208, -8155]]]
  g := ![![![-259, -38, -4978, 7326, 5900], ![-2496, -965, -23272, 37244, 29304], ![-5316, -1792, -60393, 93944, 74488], ![-12998, -4574, -139696, 218937, 173236], ![-17735, -6128, -195234, 304974, 241529]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P1 : CertificateIrreducibleZModOfList' 89 2 2 6 [70, 69, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 88], [0, 1]]
 g := ![![[76, 17], [39], [10], [0, 1], [38, 44], [1]], ![[60, 72], [39], [10], [20, 88], [28, 45], [1]]]
 h' := ![![[20, 88], [84, 62], [12, 22], [0, 30], [10, 88], [19, 20], [0, 1]], ![[0, 1], [78, 27], [7, 67], [66, 59], [79, 1], [63, 69], [20, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [86]]
 b := ![[], [15, 43]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N1 : CertifiedPrimeIdeal' SI89N1 89 where
  n := 2
  hpos := by decide
  P := [70, 69, 1]
  hirr := P89P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6158, 2423, -3088, -1102, 1532]
  a := ![-1, -1, -1, -4, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2006, 1087, -3088, -1102, 1532]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N1 B_one_repr
lemma NI89N1 : Nat.card (O ⧸ I89N1) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N1

def I89N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-883, -516, -150, 235, 186]] i)))

def SI89N2: IdealEqSpanCertificate' Table ![![-883, -516, -150, 235, 186]] 
 ![![89, 0, 0, 0, 0], ![75, 1, 0, 0, 0], ![80, 0, 1, 0, 0], ![33, 0, 0, 1, 0], ![29, 0, 0, 0, 1]] where
  M :=![![![-883, -516, -150, 235, 186], ![-4464, -2609, -758, 1188, 940], ![-11280, -6593, -1917, 3002, 2376], ![-26280, -15360, -4464, 6993, 5534], ![-36612, -21400, -6222, 9743, 7711]]]
  hmulB := by decide  
  f := ![![![-1499, -42, 374, 53, -112]], ![![-1233, -33, 308, 43, -92]], ![![-1376, -41, 345, 50, -104]], ![![-531, -6, 130, 16, -38]], ![![-539, -24, 140, 22, -43]]]
  g := ![![![412, -516, -150, 235, 186], ![2083, -2609, -758, 1188, 940], ![5265, -6593, -1917, 3002, 2376], ![12265, -15360, -4464, 6993, 5534], ![17090, -21400, -6222, 9743, 7711]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N2 : Nat.card (O ⧸ I89N2) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N2)

lemma isPrimeI89N2 : Ideal.IsPrime I89N2 := prime_ideal_of_norm_prime hp89.out _ NI89N2
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![51811, 2152, -13152, -1458, 3618]] ![![-26531, -16110, -4978, 7326, 5900]]
  ![![4985383, -19168786, -16387610, 8350772, 10354766]] where
 M := ![![![4985383, -19168786, -16387610, 8350772, 10354766]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![4985383, -19168786, -16387610, 8350772, 10354766]] ![![-883, -516, -150, 235, 186]]
  ![![89, 0, 0, 0, 0]] where
 M := ![![![-332547372637, -194377432544, -56508019552, 88486875751, 70030433912]]]
 hmul := by decide  
 g := ![![![![-3736487333, -2184016096, -634921568, 994234559, 786858808]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8647, -5058, -1472, 2304, 1824]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-8647, -5058, -1472, 2304, 1824]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![60, 1, 59, 1, 0], ![73, 25, 54, 0, 1]] where
  M :=![![![-8647, -5058, -1472, 2304, 1824], ![-43776, -25575, -7428, 11648, 9216], ![-110592, -64642, -18791, 29436, 23296], ![-257664, -150596, -43772, 68569, 54264], ![-358992, -209834, -61000, 95536, 75609]]]
  hmulB := by decide  
  f := ![![![-151, -78, 72, 32, -32]], ![![768, 337, -348, -112, 128]], ![![-1536, -606, 705, 164, -224]], ![![-996, -405, 459, 117, -152]], ![![-799, -319, 370, 88, -119]]]
  g := ![![![-2887, -546, -2432, 2304, 1824], ![-14592, -2759, -12292, 11648, 9216], ![-36880, -6974, -31067, 29436, 23296], ![-85908, -16245, -72367, 68569, 54264], ![-119697, -22635, -100830, 95536, 75609]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [75, 0, 88, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [76, 75, 68], [30, 21, 29], [0, 1]]
 g := ![![[74, 17, 62], [61, 3], [24, 49], [58, 50], [50, 81], [1]], ![[96, 53, 8, 82], [0, 6], [79, 12], [41, 86], [19, 25], [6, 55, 85, 55]], ![[15, 46, 31, 71], [80, 22], [17, 50], [53, 24], [76, 16], [87, 84, 11, 42]]]
 h' := ![![[76, 75, 68], [63, 26, 81], [51, 89, 10], [69, 9, 90], [32, 36, 70], [22, 0, 9], [0, 1]], ![[30, 21, 29], [93, 79, 74], [53, 48, 54], [35, 8, 77], [54, 58, 38], [86, 40, 92], [76, 75, 68]], ![[0, 1], [38, 89, 39], [11, 57, 33], [5, 80, 27], [87, 3, 86], [8, 57, 93], [30, 21, 29]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [91, 85], []]
 b := ![[], [94, 2, 23], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [75, 0, 88, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1669686, -1142490, -786056, 642124, 647141]
  a := ![3, 3, 0, -1, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-901427, -185187, -758938, 642124, 647141]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 912673 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10283, -666, 2424, 395, -594]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![-10283, -666, 2424, 395, -594]] 
 ![![97, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![30, 0, 0, 0, 1]] where
  M :=![![![-10283, -666, 2424, 395, -594], ![14256, -535, -4498, 96, 1580], ![-18960, -3715, 2529, 1822, 192], ![-9432, -7182, -2904, 3249, 2854], ![-33732, -10898, 1152, 5119, 2555]]]
  hmulB := by decide  
  f := ![![![54853, 30528, -23776, -16579, 14180]], ![![1581, 1203, -650, -859, 632]], ![![12728, 5981, -5637, -2546, 2528]], ![![-10024, -3054, 4620, 51, -846]], ![![34914, 16248, -15480, -6797, 6825]]]
  g := ![![![-93, -666, 2424, 395, -594], ![71, -535, -4498, 96, 1580], ![-269, -3715, 2529, 1822, 192], ![-342, -7182, -2904, 3249, 2854], ![-644, -10898, 1152, 5119, 2555]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1

def I97N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-817, -520, -172, 236, 194]] i)))

def SI97N2: IdealEqSpanCertificate' Table ![![-817, -520, -172, 236, 194]] 
 ![![97, 0, 0, 0, 0], ![67, 1, 0, 0, 0], ![35, 0, 1, 0, 0], ![55, 0, 0, 1, 0], ![57, 0, 0, 0, 1]] where
  M :=![![![-817, -520, -172, 236, 194], ![-4656, -2651, -736, 1208, 944], ![-11328, -6680, -1971, 3040, 2416], ![-26664, -15572, -4520, 7089, 5608], ![-36984, -21688, -6340, 9872, 7825]]]
  hmulB := by decide  
  f := ![![![-3457, -2792, -1364, 460, 514]], ![![-2515, -2027, -988, 332, 374]], ![![-1475, -1184, -567, 196, 214]], ![![-2239, -1812, -900, 293, 342]], ![![-2385, -1904, -896, 316, 339]]]
  g := ![![![165, -520, -172, 236, 194], ![809, -2651, -736, 1208, 944], ![2065, -6680, -1971, 3040, 2416], ![4797, -15572, -4520, 7089, 5608], ![6691, -21688, -6340, 9872, 7825]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N2 : Nat.card (O ⧸ I97N2) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N2)

lemma isPrimeI97N2 : Ideal.IsPrime I97N2 := prime_ideal_of_norm_prime hp97.out _ NI97N2
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-8647, -5058, -1472, 2304, 1824]] ![![-10283, -666, 2424, 395, -594]]
  ![![-38539123, -22491868, -6521700, 10239635, 8097990]] where
 M := ![![![-38539123, -22491868, -6521700, 10239635, 8097990]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI97N1 : IdealMulLeCertificate' Table 
  ![![-38539123, -22491868, -6521700, 10239635, 8097990]] ![![-817, -520, -172, 236, 194]]
  ![![97, 0, 0, 0, 0]] where
 M := ![![![-362439271301, -211849561312, -61587392096, 96440752223, 76325304376]]]
 hmul := by decide  
 g := ![![![![-3736487333, -2184016096, -634921568, 994234559, 786858808]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 9, 2, -6, 2]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![7, 9, 2, -6, 2]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![57, 53, 1, 0, 0], ![9, 48, 0, 1, 0], ![24, 45, 0, 0, 1]] where
  M :=![![![7, 9, 2, -6, 2], ![-48, -25, 38, 20, -24], ![288, 147, -93, -58, 40], ![-456, -168, 266, 57, -104], ![792, 353, -282, -114, 89]]]
  hmulB := by decide  
  f := ![![![-29341, -1255, 7420, 842, -2030]], ![![48720, 2093, -12314, -1400, 3368]], ![![8607, 373, -2173, -248, 594]], ![![20631, 887, -5214, -593, 1426]], ![![14256, 614, -3602, -410, 985]]]
  g := ![![![-1, 1, 2, -6, 2], ![-18, -19, 38, 20, -24], ![51, 60, -93, -58, 40], ![-135, -122, 266, 57, -104], ![156, 166, -282, -114, 89]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [50, 84, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 100], [0, 1]]
 g := ![![[34, 65], [25], [4, 37], [13], [56], [17, 1]], ![[28, 36], [25], [27, 64], [13], [56], [34, 100]]]
 h' := ![![[17, 100], [67, 41], [2, 5], [26, 21], [75, 66], [59, 37], [0, 1]], ![[0, 1], [57, 60], [87, 96], [80, 80], [86, 35], [82, 64], [17, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [7, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [50, 84, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![483, -1484, -7791, 1934, 5527]
  a := ![1, 5, -3, -2, 11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2916, 692, -7791, 1934, 5527]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7319, 291, -1868, -200, 518]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![7319, 291, -1868, -200, 518]] 
 ![![101, 0, 0, 0, 0], ![60, 1, 0, 0, 0], ![18, 0, 1, 0, 0], ![36, 0, 0, 1, 0], ![45, 0, 0, 0, 1]] where
  M :=![![![7319, 291, -1868, -200, 518], ![-12432, -647, 3054, 408, -800], ![9600, 119, -2655, -146, 816], ![-3576, -838, 370, 405, 108], ![10368, -513, -3368, 124, 1213]]]
  hmulB := by decide  
  f := ![![![-19373, -7481, 8762, 1964, -2730]], ![![-10860, -4213, 4910, 1124, -1544]], ![![-4386, -1627, 1991, 366, -572]], ![![-6204, -2548, 2790, 809, -980]], ![![-9381, -3430, 4264, 724, -1189]]]
  g := ![![![73, 291, -1868, -200, 518], ![-72, -647, 3054, 408, -800], ![186, 119, -2655, -146, 816], ![204, -838, 370, 405, 108], ![423, -513, -3368, 124, 1213]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-533, -346, -28, 72, 12]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![-533, -346, -28, 72, 12]] 
 ![![101, 0, 0, 0, 0], ![67, 1, 0, 0, 0], ![28, 0, 1, 0, 0], ![89, 0, 0, 1, 0], ![30, 0, 0, 0, 1]] where
  M :=![![![-533, -346, -28, 72, 12], ![-288, -549, -788, 40, 288], ![-3456, -2082, -13, 364, 80], ![-816, -1536, -1892, 287, 584], ![-5088, -2906, 60, 384, 183]]]
  hmulB := by decide  
  f := ![![![97199, 67330, 24724, -30472, -25900]], ![![70633, 48089, 17312, -21776, -18388]], ![![41428, 27274, 9427, -12364, -10304]], ![![120059, 79410, 27608, -35993, -30052]], ![![76410, 47958, 15556, -21776, -17793]]]
  g := ![![![165, -346, -28, 72, 12], ![459, -549, -788, 40, 288], ![1006, -2082, -13, 364, 80], ![1109, -1536, -1892, 287, 584], ![1468, -2906, 60, 384, 183]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2

def I101N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4711, 2758, 804, -1255, -994]] i)))

def SI101N3: IdealEqSpanCertificate' Table ![![4711, 2758, 804, -1255, -994]] 
 ![![101, 0, 0, 0, 0], ![70, 1, 0, 0, 0], ![75, 0, 1, 0, 0], ![67, 0, 0, 1, 0], ![42, 0, 0, 0, 1]] where
  M :=![![![4711, 2758, 804, -1255, -994], ![23856, 13939, 4050, -6344, -5020], ![60240, 35219, 10243, -16030, -12688], ![140328, 82026, 23848, -37337, -29550], ![195492, 114278, 33228, -52019, -41171]]]
  hmulB := by decide  
  f := ![![![-8245, -3324, 3708, 1011, -1264]], ![![-5414, -2191, 2434, 674, -836]], ![![-6603, -2633, 2973, 775, -992]], ![![-4979, -2074, 2232, 690, -810]], ![![-3990, -1524, 1804, 389, -553]]]
  g := ![![![-1216, 2758, 804, -1255, -994], ![-6136, 13939, 4050, -6344, -5020], ![-15509, 35219, 10243, -16030, -12688], ![-36113, 82026, 23848, -37337, -29550], ![-50313, 114278, 33228, -52019, -41171]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N3 : Nat.card (O ⧸ I101N3) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N3)

lemma isPrimeI101N3 : Ideal.IsPrime I101N3 := prime_ideal_of_norm_prime hp101.out _ NI101N3
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![7, 9, 2, -6, 2]] ![![7319, 291, -1868, -200, 518]]
  ![![737, 454, 144, -202, -164]] where
 M := ![![![737, 454, 144, -202, -164]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![737, 454, 144, -202, -164]] ![![-533, -346, -28, 72, 12]]
  ![![-21973, -17200, -7916, 2690, 3136]] where
 M := ![![![-21973, -17200, -7916, 2690, 3136]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI101N2 : IdealMulLeCertificate' Table 
  ![![-21973, -17200, -7916, 2690, 3136]] ![![4711, 2758, 804, -1255, -994]]
  ![![101, 0, 0, 0, 0]] where
 M := ![![![-152611, -120190, -55752, 18281, 21614]]]
 hmul := by decide  
 g := ![![![![-1511, -1190, -552, 181, 214]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-59041, -2483, 14964, 1679, -4104]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![-59041, -2483, 14964, 1679, -4104]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![87, 36, 89, 1, 0], ![94, 39, 74, 0, 1]] where
  M :=![![![-59041, -2483, 14964, 1679, -4104], ![98496, 4425, -24740, -2904, 6716], ![-80592, -2964, 20761, 2124, -5808], ![20448, 1940, -4334, -1019, 890], ![-94884, -2623, 25120, 2127, -7281]]]
  hmulB := by decide  
  f := ![![![-2479, -947, 1122, 239, -342]], ![![8208, 2883, -3740, -492, 956]], ![![-11472, -3516, 5287, 84, -984]], ![![-9063, -2821, 4173, 118, -808]], ![![-7474, -2304, 3444, 71, -651]]]
  g := ![![![1754, 943, 1643, 1679, -4104], ![-2720, -1485, -2556, -2904, 6716], ![2724, 1428, 2539, 2124, -5808], ![247, 38, 199, -1019, 890], ![3927, 1988, 3637, 2127, -7281]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [12, 94, 28, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [52, 23, 54], [23, 79, 49], [0, 1]]
 g := ![![[30, 47, 52], [28, 94, 72], [30, 61, 46], [60, 30], [101, 63], [1]], ![[41, 7, 100, 21], [48, 43, 59, 43], [42, 66, 85, 95], [27, 60], [19, 7], [30, 18, 71, 80]], ![[89, 75, 71, 17], [52, 78, 83, 19], [62, 30, 47, 46], [75, 76], [39, 9], [64, 93, 39, 23]]]
 h' := ![![[52, 23, 54], [76, 77, 84], [52, 62, 22], [3, 24, 56], [65, 40, 37], [91, 9, 75], [0, 1]], ![[23, 79, 49], [0, 41, 82], [15, 41, 39], [76, 51, 55], [83, 28, 36], [65, 97, 25], [52, 23, 54]], ![[0, 1], [62, 88, 40], [32, 0, 42], [86, 28, 95], [70, 35, 30], [69, 100, 3], [23, 79, 49]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56, 48], []]
 b := ![[], [100, 91, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [12, 94, 28, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7596, 3454, -3104, -1431, 1391]
  a := ![4, 0, 0, 1, -1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![13, 7, 207, -1431, 1391]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 1092727 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2479, 947, -1122, -239, 342]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![2479, 947, -1122, -239, 342]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![100, 14, 1, 0, 0], ![42, 9, 0, 1, 0], ![12, 58, 0, 0, 1]] where
  M :=![![![2479, 947, -1122, -239, 342], ![-8208, -2883, 3740, 492, -956], ![11472, 3516, -5287, -84, 984], ![-7704, -962, 3698, -1597, 310], ![7980, 547, -3886, 2181, -627]]]
  hmulB := by decide  
  f := ![![![59041, 2483, -14964, -1679, 4104]], ![![-98496, -4425, 24740, 2904, -6716]], ![![44716, 1838, -11367, -1256, 3128]], ![![15270, 607, -3898, -421, 1078]], ![![-47664, -2177, 11944, 1419, -3233]]]
  g := ![![![1171, -10, -1122, -239, 342], ![-3800, -41, 3740, 492, -956], ![5164, 206, -5287, -84, 984], ![-3050, -547, 3698, -1597, 310], ![3034, 696, -3886, 2181, -627]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P1 : CertificateIrreducibleZModOfList' 103 2 2 6 [1, 77, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [26, 102], [0, 1]]
 g := ![![[77, 1], [77, 1], [77, 1], [30], [56], [26, 1]], ![[0, 102], [0, 102], [0, 102], [30], [56], [52, 102]]]
 h' := ![![[26, 102], [26, 102], [26, 102], [77, 1], [2, 37], [77, 57], [0, 1]], ![[0, 1], [0, 1], [0, 1], [0, 102], [37, 66], [14, 46], [26, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [31, 61]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N1 : CertifiedPrimeIdeal' SI103N1 103 where
  n := 2
  hpos := by decide
  P := [1, 77, 1]
  hirr := P103P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-212543, -114837, -23800, 62221, 45720]
  a := ![7, -21, -1, -23, -21]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9655, -29062, -23800, 62221, 45720]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N1 B_one_repr
lemma NI103N1 : Nat.card (O ⧸ I103N1) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![-59041, -2483, 14964, 1679, -4104]] ![![2479, 947, -1122, -239, 342]]
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


lemma PB934I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB934I2 : PrimesBelowBoundCertificateInterval O 61 103 934 where
  m := 9
  g := ![3, 2, 1, 4, 1, 3, 3, 4, 2]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB934I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0, I67N1, I67N2]
    · exact ![I71N0, I71N1]
    · exact ![I73N0]
    · exact ![I79N0, I79N1, I79N2, I79N3]
    · exact ![I83N0]
    · exact ![I89N0, I89N1, I89N2]
    · exact ![I97N0, I97N1, I97N2]
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
    · exact ![300763, 67, 67]
    · exact ![357911, 5041]
    · exact ![2073071593]
    · exact ![6241, 79, 79, 79]
    · exact ![3939040643]
    · exact ![7921, 7921, 89]
    · exact ![912673, 97, 97]
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
      exact NI79N3
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
      exact NI89N2
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
      exact NI97N2
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
  β := ![I67N1, I67N2, I79N1, I79N2, I79N3, I89N2, I97N1, I97N2, I101N1, I101N2, I101N3]
  Il := ![[I67N1, I67N2], [], [], [I79N1, I79N2, I79N3], [], [I89N2], [I97N1, I97N2], [I101N1, I101N2, I101N3], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
