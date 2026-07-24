
import IdealArithmetic.Examples.NF5_1_15000000_1.RI5_1_15000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-322, -128, 138, 89, -135]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![-322, -128, 138, 89, -135]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![0, 0, 67, 0, 0], ![38, 1, 42, 1, 0], ![19, 16, 49, 0, 1]] where
  M :=![![![-322, -128, 138, 89, -135], ![1215, 221, -346, -31, 267], ![-2403, 68, 361, -521, -93], ![1107, -530, 164, 820, -411], ![1170, 504, -522, -366, 515]]]
  hmulB := by decide  
  f := ![![![-1006, 118, 158, 127, -195]], ![![1755, -263, -278, -207, 381]], ![![-3429, 334, 531, 445, -621]], ![![-2654, 267, 412, 343, -486]], ![![-2389, 216, 369, 314, -421]]]
  g := ![![![-17, 29, 45, 89, -135], ![-40, -60, -181, -31, 267], ![286, 31, 400, -521, -93], ![-332, 78, -211, 820, -411], ![79, -110, -155, -366, 515]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [21, 63, 28, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [45, 4, 21], [61, 62, 46], [0, 1]]
 g := ![![[17, 7, 9], [64, 10, 35], [18, 47], [36, 55], [39, 1], []], ![[25, 42, 18, 65], [9, 53, 7, 54], [11, 22], [13, 17], [47, 25], [14, 39]], ![[48, 21, 22, 44], [12, 43, 23, 44], [41, 9], [59, 56], [29, 16], [56, 39]]]
 h' := ![![[45, 4, 21], [63, 35, 64], [49, 65, 54], [5, 31, 28], [52, 1, 51], [0, 0, 1], [0, 1]], ![[61, 62, 46], [63, 9, 13], [35, 5, 23], [20, 29, 42], [5, 20, 34], [56, 66, 62], [45, 4, 21]], ![[0, 1], [57, 23, 57], [7, 64, 57], [59, 7, 64], [62, 46, 49], [66, 1, 4], [61, 62, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61, 13], []]
 b := ![[], [46, 35, 60], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [21, 63, 28, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9660492, 5955530, -745810, -2554947, -3461157]
  a := ![0, -8, -7, -7, -37]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2574783, 953567, 4121771, -2554947, -3461157]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 300763 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-149, -3, 27, -24, -12]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![-149, -3, 27, -24, -12]] 
 ![![67, 0, 0, 0, 0], ![44, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![55, 0, 0, 0, 1]] where
  M :=![![![-149, -3, 27, -24, -12], ![108, -86, 39, 120, -72], ![648, 363, -344, -300, 360], ![-1161, -354, 426, 196, -387], ![603, 27, -117, 81, 58]]]
  hmulB := by decide  
  f := ![![![85645, -11085, -13473, -10524, 17364]], ![![53912, -6980, -8481, -6624, 10932]], ![![13189, -1710, -2075, -1620, 2676]], ![![8028, -1041, -1263, -986, 1629]], ![![71512, -9258, -11250, -8787, 14500]]]
  g := ![![![10, -3, 27, -24, -12], ![97, -86, 39, 120, -72], ![-448, 363, -344, -300, 360], ![462, -354, 426, 196, -387], ![-55, 27, -117, 81, 58]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, -1, 1, 0, 0]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![-5, -1, 1, 0, 0]] 
 ![![67, 0, 0, 0, 0], ![58, 1, 0, 0, 0], ![53, 0, 1, 0, 0], ![28, 0, 0, 1, 0], ![31, 0, 0, 0, 1]] where
  M :=![![![-5, -1, 1, 0, 0], ![0, -4, 1, 4, 0], ![0, 1, -6, -4, 12], ![-27, -10, 10, 6, -9], ![9, -3, -3, 3, 4]]]
  hmulB := by decide  
  f := ![![![397, -39, -63, -52, 72]], ![![334, -32, -53, -44, 60]], ![![335, -32, -53, -44, 60]], ![![151, -14, -24, -20, 27]], ![![190, -18, -30, -25, 34]]]
  g := ![![![0, -1, 1, 0, 0], ![1, -4, 1, 4, 0], ![0, 1, -6, -4, 12], ![2, -10, 10, 6, -9], ![2, -3, -3, 3, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![-322, -128, 138, 89, -135]] ![![-149, -3, 27, -24, -12]]
  ![![-61156, 26917, -7449, -42523, 20487]] where
 M := ![![![-61156, 26917, -7449, -42523, 20487]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![-61156, 26917, -7449, -42523, 20487]] ![![-5, -1, 1, 0, 0]]
  ![![67, 0, 0, 0, 0]] where
 M := ![![![1638284, 309808, -476236, -56213, 375267]]]
 hmul := by decide  
 g := ![![![![24452, 4624, -7108, -839, 5601]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 1, -3, -4, 2]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-1, 1, -3, -4, 2]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![19, 64, 1, 0, 0], ![6, 14, 0, 1, 0], ![40, 18, 0, 0, 1]] where
  M :=![![![-1, 1, -3, -4, 2], ![-18, -10, 5, 2, -12], ![108, 23, -38, -20, 6], ![-63, 4, 14, -14, -15], ![39, 9, -3, -3, -22]]]
  hmulB := by decide  
  f := ![![![-2603, 335, 409, 320, -526]], ![![4734, -616, -745, -582, 960]], ![![3449, -450, -543, -424, 700]], ![![813, -106, -128, -100, 165]], ![![-301, 37, 47, 37, -60]]]
  g := ![![![0, 3, -3, -4, 2], ![5, -2, 5, 2, -12], ![10, 37, -38, -20, 6], ![5, -6, 14, -14, -15], ![14, 9, -3, -3, -22]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [47, 43, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 70], [0, 1]]
 g := ![![[13, 58], [37, 64], [57, 6], [64], [3], [1]], ![[4, 13], [54, 7], [12, 65], [64], [3], [1]]]
 h' := ![![[28, 70], [36, 22], [19, 8], [55, 19], [9, 8], [24, 28], [0, 1]], ![[0, 1], [13, 49], [30, 63], [19, 52], [20, 63], [27, 43], [28, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [1, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [47, 43, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1585825, -902500, 392308, 663846, 481742]
  a := ![3, -61, -63, -66, -235]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-454823, -619372, 392308, 663846, 481742]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![283, -58, -46, -30, 72]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![283, -58, -46, -30, 72]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![38, 69, 1, 0, 0], ![0, 63, 0, 1, 0], ![43, 36, 0, 0, 1]] where
  M :=![![![283, -58, -46, -30, 72], ![-648, 21, 96, 92, -90], ![810, -282, -149, -70, 276], ![-864, 94, 130, 105, -168], ![198, -108, -48, -18, 85]]]
  hmulB := by decide  
  f := ![![![425, 66, -114, 2, 84]], ![![-756, 59, 88, -208, 6]], ![![-508, 83, 31, -190, 42]], ![![-648, 65, 66, -195, 18]], ![![-149, 66, -18, -104, 49]]]
  g := ![![![-15, 34, -46, -30, 72], ![-6, -129, 96, 92, -90], ![-76, 63, -149, -70, 276], ![20, -133, 130, 105, -168], ![-23, 18, -48, -18, 85]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P1 : CertificateIrreducibleZModOfList' 71 2 2 6 [8, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [55, 70], [0, 1]]
 g := ![![[2, 9], [6, 27], [26, 12], [36], [43], [1]], ![[0, 62], [0, 44], [47, 59], [36], [43], [1]]]
 h' := ![![[55, 70], [23, 68], [5, 58], [12, 15], [4, 65], [63, 55], [0, 1]], ![[0, 1], [0, 3], [0, 13], [56, 56], [29, 6], [35, 16], [55, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [5, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N1 : CertifiedPrimeIdeal' SI71N1 71 where
  n := 2
  hpos := by decide
  P := [8, 16, 1]
  hirr := P71P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16472, -9343, 3939, 6602, 4509]
  a := ![1, -6, -6, -7, -24]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5071, -12104, 3939, 6602, 4509]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N1 B_one_repr
lemma NI71N1 : Nat.card (O ⧸ I71N1) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-23, -1, 5, 0, -4]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![-23, -1, 5, 0, -4]] 
 ![![71, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![61, 0, 1, 0, 0], ![43, 0, 0, 1, 0], ![62, 0, 0, 0, 1]] where
  M :=![![![-23, -1, 5, 0, -4], ![36, -6, -3, 8, 0], ![0, 33, -20, -28, 24], ![-63, -38, 34, 24, -33], ![57, 9, -15, 3, 10]]]
  hmulB := by decide  
  f := ![![![491, 333, -27, -124, -148]], ![![81, 55, -4, -20, -24]], ![![469, 320, -23, -116, -140]], ![![298, 203, -15, -74, -89]], ![![443, 303, -21, -109, -132]]]
  g := ![![![-1, -1, 5, 0, -4], ![-1, -6, -3, 8, 0], ![9, 33, -20, -28, 24], ![-11, -38, 34, 24, -33], ![2, 9, -15, 3, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-1, 1, -3, -4, 2]] ![![283, -58, -46, -30, 72]]
  ![![491, 333, -27, -124, -148]] where
 M := ![![![491, 333, -27, -124, -148]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![491, 333, -27, -124, -148]] ![![-23, -1, 5, 0, -4]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-359, -105, 119, -4, -82]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![-359, -105, 119, -4, -82]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![0, 0, 0, 73, 0], ![48, 36, 3, 41, 1]] where
  M :=![![![-359, -105, 119, -4, -82], ![738, 6, -109, 238, -12], ![108, 665, -486, -948, 714], ![-1845, -964, 966, 938, -1065], ![2001, 351, -573, -93, 466]]]
  hmulB := by decide  
  f := ![![![61, 47, 5, -8, -14]], ![![126, 108, 23, -6, -24]], ![![216, 221, 88, 32, -18]], ![![-99, -48, 28, 44, 39]], ![![54, 66, 35, 19, 1]]]
  g := ![![![49, 39, 5, 46, -82], ![18, 6, -1, 10, -12], ![-468, -343, -36, -414, 714], ![675, 512, 57, 611, -1065], ![-279, -225, -27, -263, 466]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 4 2 6 [31, 0, 6, 12, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [57, 69, 72, 3], [7, 56, 62, 61], [70, 20, 12, 9], [0, 1]]
 g := ![![[17, 6, 65, 3], [4, 69, 18], [26, 34, 1], [65, 3, 22, 71], [1], []], ![[72, 26, 48, 9, 72, 19], [37, 40, 1], [52, 47, 35], [63, 22, 70, 28, 61, 55], [8, 41, 16], [50, 32, 9]], ![[49, 29, 14, 38, 56, 1], [54, 20, 32], [6, 37, 50], [0, 18, 65, 19, 66, 8], [19, 9, 65], [5, 69, 71]], ![[60, 47, 69, 12, 51, 35], [22, 26, 16], [57, 34, 67], [29, 59, 28, 46, 68, 46], [13, 25, 35], [38, 47, 8]]]
 h' := ![![[57, 69, 72, 3], [6, 6, 25, 21], [35, 15, 43, 50], [29, 65, 23, 1], [42, 0, 67, 61], [0, 0, 1], [0, 1]], ![[7, 56, 62, 61], [44, 56, 52, 36], [13, 33, 26, 1], [26, 9, 23, 53], [6, 12, 41, 40], [20, 12, 53, 69], [57, 69, 72, 3]], ![[70, 20, 12, 9], [9, 2, 17, 58], [71, 27, 68, 18], [44, 15, 32, 59], [62, 18, 64, 62], [40, 32, 21, 24], [7, 56, 62, 61]], ![[0, 1], [57, 9, 52, 31], [70, 71, 9, 4], [31, 57, 68, 33], [36, 43, 47, 56], [72, 29, 71, 53], [70, 20, 12, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [35, 36, 39], []]
 b := ![[], [], [12, 7, 1, 58], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 4
  hpos := by decide
  P := [31, 0, 6, 12, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-255053467561, -181593701000, 8459625384, 62020306144, 68381604952]
  a := ![1, 26, 22, 17, 121]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-48457130209, -36210020264, -2694317664, -37556513656, 68381604952]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 28398241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-61, -47, -5, 8, 14]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-61, -47, -5, 8, 14]] 
 ![![73, 0, 0, 0, 0], ![23, 1, 0, 0, 0], ![55, 0, 1, 0, 0], ![52, 0, 0, 1, 0], ![68, 0, 0, 0, 1]] where
  M :=![![![-61, -47, -5, 8, 14], ![-126, -108, -23, 6, 24], ![-216, -221, -88, -32, 18], ![99, 48, -28, -44, -39], ![111, 21, -75, -87, -64]]]
  hmulB := by decide  
  f := ![![![359, 105, -119, 4, 82]], ![![103, 33, -36, -2, 26]], ![![269, 70, -83, 16, 52]], ![![281, 88, -98, -10, 73]], ![![307, 93, -103, 5, 70]]]
  g := ![![![-1, -47, -5, 8, 14], ![23, -108, -23, 6, 24], ![139, -221, -88, -32, 18], ![75, 48, -28, -44, -39], ![173, 21, -75, -87, -64]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![-359, -105, 119, -4, -82]] ![![-61, -47, -5, 8, 14]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-22, 0, 6, 1, -7]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![-22, 0, 6, 1, -7]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![77, 43, 58, 1, 0], ![48, 40, 30, 0, 1]] where
  M :=![![![-22, 0, 6, 1, -7], ![63, 5, -10, 1, 3], ![-27, 44, -7, -33, 3], ![-9, -34, 24, 28, -27], ![66, 24, -18, -6, 11]]]
  hmulB := by decide  
  f := ![![![-10, -2, 2, 3, 1]], ![![-9, -11, 2, 5, 9]], ![![-81, -34, 15, 25, 15]], ![![-74, -33, 14, 24, 17]], ![![-42, -20, 8, 14, 11]]]
  g := ![![![3, 3, 2, 1, -7], ![-2, -2, -2, 1, 3], ![30, 17, 23, -33, 3], ![-11, -2, -10, 28, -27], ![0, -2, 0, -6, 11]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [78, 51, 25, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [52, 51, 32], [2, 27, 47], [0, 1]]
 g := ![![[52, 15, 10], [70, 14, 44], [67, 65, 31], [21, 65, 46], [54, 1], []], ![[19, 9, 31, 62], [71, 52, 73, 49], [56, 13, 57, 46], [60, 39, 55, 51], [55, 18], [21, 76]], ![[59, 25, 49, 39], [52, 16, 41, 34], [23, 60, 57, 54], [45, 55, 20, 54], [30, 73], [6, 76]]]
 h' := ![![[52, 51, 32], [70, 64, 57], [67, 12, 53], [21, 14, 30], [54, 12, 21], [0, 0, 1], [0, 1]], ![[2, 27, 47], [12, 27, 32], [72, 47, 77], [23, 29, 73], [75, 14, 3], [39, 43, 27], [52, 51, 32]], ![[0, 1], [57, 67, 69], [68, 20, 28], [33, 36, 55], [51, 53, 55], [10, 36, 51], [2, 27, 47]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 2], []]
 b := ![[], [52, 23, 74], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [78, 51, 25, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11320098, 4031335, -719296, -279613, -2634180]
  a := ![-1, -6, 1, 10, -51]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2016341, 1536986, 1196502, -279613, -2634180]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 493039 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10, 2, -2, -3, -1]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![10, 2, -2, -3, -1]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![26, 7, 1, 0, 0], ![60, 70, 0, 1, 0], ![74, 11, 0, 0, 1]] where
  M :=![![![10, 2, -2, -3, -1], ![9, 11, -2, -5, -9], ![81, 34, -15, -25, -15], ![-9, 8, 4, 0, -9], ![48, 24, -6, -12, -11]]]
  hmulB := by decide  
  f := ![![![22, 0, -6, -1, 7]], ![![-63, -5, 10, -1, -3]], ![![2, -1, -1, 0, 2]], ![![-39, -4, 4, -2, 3]], ![![11, -1, -4, -1, 6]]]
  g := ![![![4, 3, -2, -3, -1], ![13, 6, -2, -5, -9], ![39, 26, -15, -25, -15], ![7, 1, 4, 0, -9], ![22, 13, -6, -12, -11]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P1 : CertificateIrreducibleZModOfList' 79 2 2 6 [78, 51, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 78], [0, 1]]
 g := ![![[28, 76], [61, 31], [30, 73], [12, 62], [73], [1]], ![[23, 3], [60, 48], [20, 6], [10, 17], [73], [1]]]
 h' := ![![[28, 78], [61, 32], [30, 30], [12, 28], [74, 46], [1, 28], [0, 1]], ![[0, 1], [9, 47], [1, 49], [6, 51], [19, 33], [74, 51], [28, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [65, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N1 : CertifiedPrimeIdeal' SI79N1 79 where
  n := 2
  hpos := by decide
  P := [78, 51, 1]
  hirr := P79P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![42630, -2498, -7422, 5012, 5250]
  a := ![0, -2, -14, -36, 42]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5742, -4546, -7422, 5012, 5250]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N1 B_one_repr
lemma NI79N1 : Nat.card (O ⧸ I79N1) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![-22, 0, 6, 1, -7]] ![![10, 2, -2, -3, -1]]
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

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2650, -280, -448, -339, 559]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![2650, -280, -448, -339, 559]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![0, 0, 0, 83, 0], ![38, 58, 43, 72, 1]] where
  M :=![![![2650, -280, -448, -339, 559], ![-5031, 525, 840, 563, -1017], ![9153, -1140, -1409, -817, 1689], ![-7119, 1108, 976, 534, -1203], ![1914, -486, -180, -174, 295]]]
  hmulB := by decide  
  f := ![![![-46, -42, -12, -1, 7]], ![![-63, -79, -44, -25, -3]], ![![27, -98, -151, -135, -75]], ![![171, 94, -36, -66, -63]], ![![101, -42, -147, -147, -94]]]
  g := ![![![-224, -394, -295, -489, 559], ![405, 717, 537, 889, -1017], ![-663, -1194, -892, -1475, 1689], ![465, 854, 635, 1050, -1203], ![-112, -212, -155, -258, 295]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 4 2 6 [51, 28, 51, 68, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 75, 75, 15], [82, 40, 0, 61], [6, 50, 8, 7], [0, 1]]
 g := ![![[47, 20, 66, 31], [57, 34, 5, 30], [10, 50, 40], [71, 58, 64], [15, 1], []], ![[16, 8, 58, 4, 51, 13], [23, 57, 49, 66, 2, 22], [26, 82, 40], [44, 33, 23], [57, 26, 30, 36, 29, 55], [16, 64, 59]], ![[30, 72, 1, 72, 40, 7], [74, 7, 68, 12, 30, 37], [75], [75, 36, 64], [33, 76, 43, 19, 3, 78], [37, 39, 69]], ![[34, 7, 74, 6, 15, 12], [55, 78, 51, 37, 65, 10], [44], [44, 20, 78], [15, 39, 5, 61, 26, 31], [14, 17, 49]]]
 h' := ![![[10, 75, 75, 15], [81, 19, 22, 23], [19, 4, 76, 14], [23, 58, 18, 17], [65, 27, 37, 8], [0, 0, 1], [0, 1]], ![[82, 40, 0, 61], [17, 69, 47, 43], [77, 20, 31, 67], [65, 6, 25, 66], [63, 66, 62, 43], [31, 29, 14, 68], [10, 75, 75, 15]], ![[6, 50, 8, 7], [46, 35, 61, 29], [9, 80, 7, 30], [4, 65, 65], [29, 79, 46, 8], [23, 49, 82, 81], [82, 40, 0, 61]], ![[0, 1], [17, 43, 36, 71], [0, 62, 52, 55], [13, 37, 58], [79, 77, 21, 24], [69, 5, 69, 17], [6, 50, 8, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [76, 41, 61], []]
 b := ![[], [], [57, 51, 81, 82], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 4
  hpos := by decide
  P := [51, 28, 51, 68, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![347148097, -383957198, -113164104, 238594530, -25234376]
  a := ![13, -6, -1, 5, -43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![15735595, 13007670, 11709808, 24764694, -25234376]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 47458321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![46, 42, 12, 1, -7]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![46, 42, 12, 1, -7]] 
 ![![83, 0, 0, 0, 0], ![33, 1, 0, 0, 0], ![73, 0, 1, 0, 0], ![17, 0, 0, 1, 0], ![70, 0, 0, 0, 1]] where
  M :=![![![46, 42, 12, 1, -7], ![63, 79, 44, 25, 3], ![-27, 98, 151, 135, 75], ![-171, -94, 36, 66, 63], ![-312, -138, 108, 156, 133]]]
  hmulB := by decide  
  f := ![![![-2650, 280, 448, 339, -559]], ![![-993, 105, 168, 128, -210]], ![![-2441, 260, 411, 308, -512]], ![![-457, 44, 80, 63, -100]], ![![-2258, 242, 380, 288, -475]]]
  g := ![![![-21, 42, 12, 1, -7], ![-77, 79, 44, 25, 3], ![-263, 98, 151, 135, 75], ![-63, -94, 36, 66, 63], ![-188, -138, 108, 156, 133]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![2650, -280, -448, -339, 559]] ![![46, 42, 12, 1, -7]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6155, 3302, -1252, -2294, -2148]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![6155, 3302, -1252, -2294, -2148]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![0, 0, 0, 89, 0], ![73, 66, 45, 28, 1]] where
  M :=![![![6155, 3302, -1252, -2294, -2148], ![19332, 11347, -3352, -6864, -6882], ![61938, 36626, -9139, -20326, -20592], ![10530, 7494, -368, -2541, -3228], ![37350, 23820, -3420, -10494, -11557]]]
  hmulB := by decide  
  f := ![![![343, -130, 28, 214, -96]], ![![864, 659, -576, -604, 642]], ![![-5778, -1638, 2037, 830, -1812]], ![![6750, 1078, -1832, -1, 1368]], ![![107, -102, 49, 138, -85]]]
  g := ![![![1831, 1630, 1072, 650, -2148], ![5862, 5231, 3442, 2088, -6882], ![17586, 15682, 10309, 6250, -20592], ![2766, 2478, 1628, 987, -3228], ![9899, 8838, 5805, 3518, -11557]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 4 2 6 [69, 52, 55, 66, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [54, 20, 70, 83], [4, 83, 40, 1], [54, 74, 68, 5], [0, 1]]
 g := ![![[65, 45, 36, 47], [32, 63, 81], [31, 13, 73], [7, 8, 6, 40], [23, 1], []], ![[48, 88, 50, 78, 86, 13], [34, 64, 17], [47, 76, 32], [3, 8, 49, 9, 23, 31], [70, 50, 9, 39, 27, 66], [1, 77, 36]], ![[60, 80, 13, 76, 71, 57], [44, 10, 18], [49, 49, 32], [61, 77, 0, 64, 83, 88], [62, 74, 40, 3, 21, 18], [75, 14, 1]], ![[54, 32, 24, 19, 55, 88], [81, 68, 39], [69, 7, 73], [44, 14, 77, 39, 55, 21], [85, 45, 73, 15, 71, 50], [13, 9, 25]]]
 h' := ![![[54, 20, 70, 83], [39, 23, 69, 15], [17, 78, 78, 9], [51, 21, 84, 42], [15, 70, 18, 29], [0, 0, 1], [0, 1]], ![[4, 83, 40, 1], [35, 74, 9, 61], [45, 28, 78, 27], [66, 18, 30, 78], [30, 69, 79, 43], [88, 88, 82, 73], [54, 20, 70, 83]], ![[54, 74, 68, 5], [84, 81, 78, 71], [19, 36, 78, 75], [14, 70, 78, 11], [30, 60, 10, 34], [3, 70, 62, 75], [4, 83, 40, 1]], ![[0, 1], [43, 0, 22, 31], [5, 36, 33, 67], [82, 69, 75, 47], [70, 68, 71, 72], [61, 20, 33, 30], [54, 74, 68, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [69, 25, 44], []]
 b := ![[], [], [56, 38, 77, 45], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 4
  hpos := by decide
  P := [69, 52, 55, 66, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![165085, 347386, -405200, -585024, 506622]
  a := ![-1, 0, -2, -5, 9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-413689, -371794, -260710, -165960, 506622]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 62742241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![343, -130, 28, 214, -96]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![343, -130, 28, 214, -96]] 
 ![![89, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![64, 0, 1, 0, 0], ![87, 0, 0, 1, 0], ![53, 0, 0, 0, 1]] where
  M :=![![![343, -130, 28, 214, -96], ![864, 659, -576, -604, 642], ![-5778, -1638, 2037, 830, -1812], ![6750, 1078, -1832, -1, 1368], ![-1530, 444, -36, -798, 307]]]
  hmulB := by decide  
  f := ![![![6155, 3302, -1252, -2294, -2148]], ![![563, 313, -108, -206, -198]], ![![5122, 2786, -1003, -1878, -1776]], ![![6135, 3312, -1228, -2271, -2136]], ![![4085, 2234, -784, -1484, -1409]]]
  g := ![![![-161, -130, 28, 214, -96], ![595, 659, -576, -604, 642], ![-1170, -1638, 2037, 830, -1812], ![519, 1078, -1832, -1, 1368], ![581, 444, -36, -798, 307]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![6155, 3302, -1252, -2294, -2148]] ![![343, -130, 28, 214, -96]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3167, 291, 481, 406, -570]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-3167, 291, 481, 406, -570]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![8, 76, 1, 0, 0], ![38, 48, 0, 1, 0], ![94, 18, 0, 0, 1]] where
  M :=![![![-3167, 291, 481, 406, -570], ![5130, -976, -863, -598, 1218], ![-10962, 613, 1550, 1398, -1794], ![8235, -1070, -1326, -1044, 1641], ![-3087, 153, 381, 339, -548]]]
  hmulB := by decide  
  f := ![![![5749, -161, -853, 1250, 198]], ![![-1782, 4302, -2523, -5318, 3750]], ![![-1270, 3197, -1884, -3942, 2790]], ![![1919, 2212, -1770, -2210, 2097]], ![![4999, 643, -1255, 179, 874]]]
  g := ![![![321, -469, 481, 406, -570], ![-822, 736, -863, -598, 1218], ![950, -1567, 1550, 1398, -1794], ![-987, 1240, -1326, -1044, 1641], ![335, -363, 381, 339, -548]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [9, 72, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 96], [0, 1]]
 g := ![![[8, 54], [24], [49], [12], [89], [25, 1]], ![[0, 43], [24], [49], [12], [89], [50, 96]]]
 h' := ![![[25, 96], [73, 32], [17, 86], [78, 7], [63, 20], [66, 34], [0, 1]], ![[0, 1], [0, 65], [33, 11], [59, 90], [78, 77], [43, 63], [25, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41]]
 b := ![[], [59, 69]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [9, 72, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-53442, -42049, 15563, 32302, 24117]
  a := ![3, 10, 6, -2, 63]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-37860, -33087, 15563, 32302, 24117]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-224, -33, 59, -3, -43]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![-224, -33, 59, -3, -43]] 
 ![![97, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![81, 0, 1, 0, 0], ![23, 0, 0, 1, 0], ![44, 0, 0, 0, 1]] where
  M :=![![![-224, -33, 59, -3, -43], ![387, -36, -41, 113, -9], ![81, 373, -258, -417, 339], ![-900, -476, 462, 385, -480], ![867, 141, -237, -3, 178]]]
  hmulB := by decide  
  f := ![![![1336, 853, -283, -551, -581]], ![![109, 64, -21, -41, -41]], ![![1269, 808, -259, -512, -540]], ![![350, 221, -69, -138, -145]], ![![701, 449, -137, -277, -294]]]
  g := ![![![-30, -33, 59, -3, -43], ![17, -36, -41, 113, -9], ![146, 373, -258, -417, 339], ![-249, -476, 462, 385, -480], ![121, 141, -237, -3, 178]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1

def I97N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-196, -141, -3, 37, 51]] i)))

def SI97N2: IdealEqSpanCertificate' Table ![![-196, -141, -3, 37, 51]] 
 ![![97, 0, 0, 0, 0], ![48, 1, 0, 0, 0], ![24, 0, 1, 0, 0], ![76, 0, 0, 1, 0], ![39, 0, 0, 0, 1]] where
  M :=![![![-196, -141, -3, 37, 51], ![-459, -352, -31, 67, 111], ![-999, -823, -148, 75, 201], ![162, 62, -66, -89, -72], ![-9, -129, -159, -135, -70]]]
  hmulB := by decide  
  f := ![![![-712, 409, -145, -579, 309]], ![![-381, 184, -55, -271, 135]], ![![-15, 143, -90, -161, 123]], ![![-736, 296, -68, -459, 210]], ![![-255, 150, -54, -210, 113]]]
  g := ![![![19, -141, -3, 37, 51], ![80, -352, -31, 67, 111], ![294, -823, -148, 75, 201], ![86, 62, -66, -89, -72], ![237, -129, -159, -135, -70]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N2 : Nat.card (O ⧸ I97N2) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N2)

lemma isPrimeI97N2 : Ideal.IsPrime I97N2 := prime_ideal_of_norm_prime hp97.out _ NI97N2

def I97N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-277, -227, 195, 212, -220]] i)))

def SI97N3: IdealEqSpanCertificate' Table ![![-277, -227, 195, 212, -220]] 
 ![![97, 0, 0, 0, 0], ![66, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![73, 0, 0, 1, 0], ![30, 0, 0, 0, 1]] where
  M :=![![![-277, -227, 195, 212, -220], ![1980, 578, -709, -304, 636], ![-5724, -637, 1372, -320, -912], ![4419, -230, -586, 1084, 57], ![867, 855, -705, -831, 818]]]
  hmulB := by decide  
  f := ![![![-2689, -95, 629, 688, 4]], ![![-1830, -86, 433, 480, 24]], ![![-441, -68, 99, 124, 36]], ![![-2008, -101, 469, 522, 25]], ![![-951, -87, 213, 249, 32]]]
  g := ![![![42, -227, 195, 212, -220], ![-275, 578, -709, -304, 636], ![770, -637, 1372, -320, -912], ![-577, -230, -586, 1084, 57], ![-135, 855, -705, -831, 818]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N3 : Nat.card (O ⧸ I97N3) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N3)

lemma isPrimeI97N3 : Ideal.IsPrime I97N3 := prime_ideal_of_norm_prime hp97.out _ NI97N3
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-3167, 291, 481, 406, -570]] ![![-224, -33, 59, -3, -43]]
  ![![1396, -178, -220, -173, 281]] where
 M := ![![![1396, -178, -220, -173, 281]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI97N1 : IdealMulLeCertificate' Table 
  ![![1396, -178, -220, -173, 281]] ![![-196, -141, -3, 37, 51]]
  ![![-2689, -95, 629, 688, 4]] where
 M := ![![![-2689, -95, 629, 688, 4]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI97N2 : IdealMulLeCertificate' Table 
  ![![-2689, -95, 629, 688, 4]] ![![-277, -227, 195, 212, -220]]
  ![![97, 0, 0, 0, 0]] where
 M := ![![![97, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2192, -254, -340, -273, 427]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![2192, -254, -340, -273, 427]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![14, 12, 98, 1, 0], ![99, 26, 55, 0, 1]] where
  M :=![![![2192, -254, -340, -273, 427], ![-3843, 571, 620, 467, -819], ![7371, -766, -1113, -911, 1401], ![-5877, 754, 932, 732, -1179], ![2076, -222, -300, -240, 413]]]
  hmulB := by decide  
  f := ![![![100, 48, -48, -37, 49]], ![![-441, -95, 136, 29, -111]], ![![999, 28, -185, 153, 87]], ![![925, 24, -170, 144, 79]], ![![525, 36, -111, 56, 65]]]
  g := ![![![-359, -80, 29, -273, 427], ![700, 161, -1, 467, -819], ![-1174, -260, 110, -911, 1401], ![996, 224, -59, 732, -1179], ![-351, -80, 5, -240, 413]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [6, 35, 94, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [98, 95, 79], [10, 5, 22], [0, 1]]
 g := ![![[51, 61, 56], [67, 80], [3, 64, 5], [61, 68], [55, 49], [1]], ![[67, 51, 22, 17], [28, 9], [81, 30, 64, 88], [92, 76], [66, 9], [30, 59, 77, 58]], ![[12, 13, 98, 19], [8, 19], [7, 56, 7, 14], [34, 56], [30, 16], [48, 23, 87, 43]]]
 h' := ![![[98, 95, 79], [23, 85, 64], [83, 37, 22], [18, 21, 56], [9, 19, 13], [95, 66, 7], [0, 1]], ![[10, 5, 22], [58, 76, 66], [78, 11, 3], [32, 8, 20], [33, 65, 51], [96, 50, 98], [98, 95, 79]], ![[0, 1], [47, 41, 72], [87, 53, 76], [86, 72, 25], [47, 17, 37], [5, 86, 97], [10, 5, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33, 4], []]
 b := ![[], [32, 49, 92], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [6, 35, 94, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3508409, -1986688, 439784, 873531, 1033999]
  a := ![1, 4, 0, -5, 31]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1169344, -389634, -1406299, 873531, 1033999]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 1030301 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-100, -48, 48, 37, -49]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![-100, -48, 48, 37, -49]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![38, 14, 1, 0, 0], ![50, 80, 0, 1, 0], ![9, 38, 0, 0, 1]] where
  M :=![![![-100, -48, 48, 37, -49], ![441, 95, -136, -29, 111], ![-999, -28, 185, -153, -87], ![585, -148, 0, 280, -99], ![354, 186, -180, -150, 185]]]
  hmulB := by decide  
  f := ![![![-2192, 254, 340, 273, -427]], ![![3843, -571, -620, -467, 819]], ![![-365, 24, 53, 47, -61]], ![![2017, -334, -332, -242, 449]], ![![1230, -190, -200, -149, 266]]]
  g := ![![![-33, -18, 48, 37, -49], ![60, 1, -136, -29, 111], ![4, 128, 185, -153, -87], ![-124, -186, 0, 280, -99], ![129, 76, -180, -150, 185]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P1 : CertificateIrreducibleZModOfList' 101 2 2 6 [49, 39, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [62, 100], [0, 1]]
 g := ![![[75, 33], [49], [80, 95], [54], [31], [62, 1]], ![[0, 68], [49], [11, 6], [54], [31], [23, 100]]]
 h' := ![![[62, 100], [81, 72], [19, 7], [45, 14], [60, 85], [93, 58], [0, 1]], ![[0, 1], [0, 29], [49, 94], [4, 87], [78, 16], [53, 43], [62, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [67]]
 b := ![[], [22, 84]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N1 : CertifiedPrimeIdeal' SI101N1 101 where
  n := 2
  hpos := by decide
  P := [49, 39, 1]
  hirr := P101P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-157, -702, 158, 626, -156]
  a := ![4, -1, 0, 2, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-357, -466, 158, 626, -156]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N1 B_one_repr
lemma NI101N1 : Nat.card (O ⧸ I101N1) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![2192, -254, -340, -273, 427]] ![![-100, -48, 48, 37, -49]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0, 0, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0, 0, 0]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![0, 0, 0, 103, 0], ![0, 0, 0, 0, 103]] where
  M :=![![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![0, 0, 0, 103, 0], ![0, 0, 0, 0, 103]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 5 2 6 [48, 83, 50, 70, 12, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [78, 27, 46, 17, 40], [56, 79, 67, 88, 3], [45, 36, 28, 94, 79], [15, 63, 65, 7, 84], [0, 1]]
 g := ![![[37, 94, 102, 44, 56], [94, 49, 43, 9, 59], [41, 40, 20, 11, 16], [30, 58, 17, 17], [91, 1], []], ![[10, 77, 62, 36, 35, 64, 9, 70], [55, 46, 32, 28, 10, 10, 31, 71], [75, 73, 35, 56, 21, 91, 11, 62], [96, 26, 54, 64], [23, 25, 6, 59], [85, 24, 69, 16, 48, 18, 95, 37]], ![[8, 22, 91, 96, 33, 12, 87, 51], [91, 34, 76, 102, 28, 78, 70, 74], [37, 100, 72, 13, 0, 86, 43, 47], [13, 57, 36, 4], [83, 81, 15, 72], [6, 23, 56, 101, 100, 83, 95, 27]], ![[14, 84, 52, 60, 6, 12, 60, 41], [8, 18, 42, 95, 14, 77, 68, 61], [64, 32, 31, 99, 25, 92, 71, 16], [78, 9, 69, 92], [80, 0, 92, 33], [73, 79, 25, 82, 34, 21, 59, 81]], ![[21, 31, 70, 14, 59, 4, 81, 51], [55, 92, 69, 88, 51, 95, 76, 31], [101, 90, 5, 91, 30, 53, 70, 94], [67, 23, 102, 32], [25, 0, 10, 93], [11, 36, 29, 100, 80, 29, 73, 42]]]
 h' := ![![[78, 27, 46, 17, 40], [20, 61, 76, 66, 46], [92, 52, 66, 53, 33], [15, 69, 44, 39, 99], [61, 21, 2, 69, 74], [0, 0, 0, 1], [0, 1]], ![[56, 79, 67, 88, 3], [50, 6, 39, 11, 39], [4, 45, 18, 32, 24], [41, 54, 31, 102, 74], [23, 0, 9, 90, 8], [71, 85, 82, 36, 70], [78, 27, 46, 17, 40]], ![[45, 36, 28, 94, 79], [24, 13, 94, 62, 74], [96, 7, 4, 40, 33], [101, 72, 69, 71, 16], [2, 19, 82, 21, 2], [22, 30, 74, 76, 81], [56, 79, 67, 88, 3]], ![[15, 63, 65, 7, 84], [82, 6, 32, 21, 32], [28, 92, 27, 82, 39], [56, 25, 83, 86, 58], [68, 29, 84, 73, 68], [71, 68, 36, 16, 41], [45, 36, 28, 94, 79]], ![[0, 1], [52, 17, 68, 46, 15], [7, 10, 91, 102, 77], [7, 89, 82, 11, 62], [66, 34, 29, 56, 54], [66, 23, 14, 77, 14], [15, 63, 65, 7, 84]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [82, 59, 96, 86], [], [], []]
 b := ![[], [75, 68, 69, 4, 3], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 5
  hpos := by decide
  P := [48, 83, 50, 70, 12, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1670057502578925, 1493601775108344, 417894291907678, 19281501932567, -299839257441065]
  a := ![7, -46, -47, -48, -205]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![16214150510475, 14500988107848, 4057226135026, 187199047889, -2911060751855]
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



lemma PB242I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB242I2 : PrimesBelowBoundCertificateInterval O 61 103 242 where
  m := 9
  g := ![3, 3, 2, 2, 2, 2, 4, 2, 1]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB242I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0, I67N1, I67N2]
    · exact ![I71N0, I71N1, I71N2]
    · exact ![I73N0, I73N1]
    · exact ![I79N0, I79N1]
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1, I97N2, I97N3]
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
    · exact ![300763, 67, 67]
    · exact ![5041, 5041, 71]
    · exact ![28398241, 73]
    · exact ![493039, 6241]
    · exact ![47458321, 83]
    · exact ![62742241, 89]
    · exact ![9409, 97, 97, 97]
    · exact ![1030301, 10201]
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
      exact NI71N2
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
  β := ![I67N1, I67N2, I71N2, I73N1, I83N1, I89N1, I97N1, I97N2, I97N3]
  Il := ![[I67N1, I67N2], [I71N2], [I73N1], [], [I83N1], [I89N1], [I97N1, I97N2, I97N3], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
