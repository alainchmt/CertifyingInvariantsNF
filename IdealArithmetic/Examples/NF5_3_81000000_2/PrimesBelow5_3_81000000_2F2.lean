
import IdealArithmetic.Examples.NF5_3_81000000_2.RI5_3_81000000_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 62, 52, 2, -8]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![17, 62, 52, 2, -8]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![0, 0, 67, 0, 0], ![2, 24, 10, 1, 0], ![57, 15, 63, 0, 1]] where
  M :=![![![17, 62, 52, 2, -8], ![-48, -103, -56, -4, 4], ![24, 12, -47, -28, -8], ![-48, -96, -136, -103, -56], ![-180, -450, -496, -250, -99]]]
  hmulB := by decide  
  f := ![![![371, 454, 324, 18, -48]], ![![-288, -349, -248, -12, 36]], ![![216, 252, 179, 4, -24]], ![![-62, -76, -54, -3, 8]], ![![453, 543, 387, 16, -55]]]
  g := ![![![7, 2, 8, 2, -8], ![-4, -1, -4, -4, 4], ![8, 12, 11, -28, -8], ![50, 48, 66, -103, -56], ![89, 105, 123, -250, -99]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [25, 45, 58, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 18, 65], [66, 48, 2], [0, 1]]
 g := ![![[13, 14, 26], [42, 38, 54], [47, 23], [0, 23], [9, 1], []], ![[63, 50, 0, 23], [10, 4, 54, 24], [3, 21], [41, 22], [15, 26], [31, 4]], ![[5, 51, 43, 5], [18, 66, 54, 50], [22, 26], [57, 54], [25, 56], [27, 4]]]
 h' := ![![[10, 18, 65], [22, 34, 48], [23, 4, 11], [40, 32, 31], [43, 39, 36], [0, 0, 1], [0, 1]], ![[66, 48, 2], [55, 0, 25], [8, 49, 51], [4, 30, 17], [52, 42, 42], [62, 4, 48], [10, 18, 65]], ![[0, 1], [64, 33, 61], [42, 14, 5], [18, 5, 19], [61, 53, 56], [63, 63, 18], [66, 48, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27, 21], []]
 b := ![[], [13, 25, 44], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [25, 45, 58, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5456099, -14813064, -19006955, -10395411, -4397796]
  a := ![0, -1, -3, -1, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3970285, 4487220, 5403109, -10395411, -4397796]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 300763 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-371, -454, -324, -18, 48]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![-371, -454, -324, -18, 48]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![61, 57, 1, 0, 0], ![7, 28, 0, 1, 0], ![20, 48, 0, 0, 1]] where
  M :=![![![-371, -454, -324, -18, 48], ![288, 349, 248, 12, -36], ![-216, -252, -179, -4, 24], ![144, 144, 104, -11, -8], ![84, 138, 96, 26, -23]]]
  hmulB := by decide  
  f := ![![![-17, -62, -52, -2, 8]], ![![48, 103, 56, 4, -4]], ![![25, 31, 1, 2, 4]], ![![19, 38, 20, 3, 0]], ![![32, 62, 32, 6, 1]]]
  g := ![![![277, 242, -324, -18, 48], ![-212, -185, 248, 12, -36], ![153, 133, -179, -4, 24], ![-89, -76, 104, -11, -8], ![-82, -74, 96, 26, -23]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P1 : CertificateIrreducibleZModOfList' 67 2 2 6 [32, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [66, 66], [0, 1]]
 g := ![![[44, 35], [57, 59], [39], [16], [1], [1]], ![[9, 32], [65, 8], [39], [16], [1], [1]]]
 h' := ![![[66, 66], [52, 13], [22, 27], [59, 21], [54, 63], [35, 66], [0, 1]], ![[0, 1], [39, 54], [62, 40], [38, 46], [58, 4], [36, 1], [66, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [19, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N1 : CertifiedPrimeIdeal' SI67N1 67 where
  n := 2
  hpos := by decide
  P := [32, 1, 1]
  hirr := P67P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2002, -5128, 696, -1604, 1320]
  a := ![3, -64, 2, -1, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-890, -944, 696, -1604, 1320]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N1 B_one_repr
lemma NI67N1 : Nat.card (O ⧸ I67N1) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![17, 62, 52, 2, -8]] ![![-371, -454, -324, -18, 48]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![733, 1555, 1086, 449, -330]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![733, 1555, 1086, 449, -330]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![17, 6, 45, 1, 0], ![8, 51, 56, 0, 1]] where
  M :=![![![733, 1555, 1086, 449, -330], ![-1980, -4217, -2946, -1224, 898], ![5388, 11490, 8029, 3340, -2448], ![-14688, -31332, -21890, -9107, 6680], ![17346, 37011, 25866, 10765, -7883]]]
  hmulB := by decide  
  f := ![![![-49, -71, 18, 9, -4]], ![![-24, -109, -122, -10, 18]], ![![108, 246, 151, 4, -20]], ![![53, 127, 89, 4, -12]], ![![62, 106, 32, -3, -3]]]
  g := ![![![-60, 221, -9, 449, -330], ![164, -601, 26, -1224, 898], ![-448, 1638, -73, 3340, -2448], ![1221, -4470, 195, -9107, 6680], ![-1445, 5274, -241, 10765, -7883]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [64, 63, 13, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 33, 36], [33, 37, 35], [0, 1]]
 g := ![![[34, 56, 25], [44, 23, 37], [3, 41, 36], [5, 18], [58, 1], []], ![[30, 30, 32, 16], [61, 50, 32, 29], [38, 20, 7, 54], [66, 16], [31, 20], [12, 18]], ![[28, 10, 29, 34], [35, 44, 8, 55], [22, 55, 42, 13], [5, 30], [31, 24], [13, 18]]]
 h' := ![![[25, 33, 36], [24, 31, 5], [21, 37, 26], [9, 70, 65], [51, 45, 35], [0, 0, 1], [0, 1]], ![[33, 37, 35], [13, 17, 23], [68, 51, 22], [61, 24, 26], [5, 52, 4], [70, 26, 37], [25, 33, 36]], ![[0, 1], [60, 23, 43], [43, 54, 23], [67, 48, 51], [23, 45, 32], [44, 45, 33], [33, 37, 35]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14, 22], []]
 b := ![[], [21, 15, 27], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [64, 63, 13, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-514263, -1394490, -1783955, -975158, -409702]
  a := ![1, -3, -1, -1, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![272409, 357060, 916077, -975158, -409702]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 357911 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-49, -71, 18, 9, -4]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-49, -71, 18, 9, -4]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![16, 26, 1, 0, 0], ![10, 50, 0, 1, 0], ![18, 52, 0, 0, 1]] where
  M :=![![![-49, -71, 18, 9, -4], ![-24, -109, -122, -10, 18], ![108, 246, 151, 4, -20], ![-120, -192, -50, 11, 8], ![-30, -123, -106, 1, 21]]]
  hmulB := by decide  
  f := ![![![733, 1555, 1086, 449, -330]], ![![-1980, -4217, -2946, -1224, 898]], ![![-484, -1032, -721, -300, 220]], ![![-1498, -3192, -2230, -927, 680]], ![![-1020, -2173, -1518, -631, 463]]]
  g := ![![![-5, -11, 18, 9, -4], ![24, 37, -122, -10, 18], ![-28, -40, 151, 4, -20], ![6, 2, -50, 11, 8], ![18, 21, -106, 1, 21]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P1 : CertificateIrreducibleZModOfList' 71 2 2 6 [28, 66, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 70], [0, 1]]
 g := ![![[48, 15], [65, 49], [49, 29], [27], [25], [1]], ![[52, 56], [26, 22], [52, 42], [27], [25], [1]]]
 h' := ![![[5, 70], [26, 50], [48, 7], [52, 10], [13, 58], [43, 5], [0, 1]], ![[0, 1], [63, 21], [12, 64], [31, 61], [19, 13], [68, 66], [5, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [13, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N1 : CertifiedPrimeIdeal' SI71N1 71 where
  n := 2
  hpos := by decide
  P := [28, 66, 1]
  hirr := P71P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4829, 15386, 20975, 11453, 6363]
  a := ![1, 19, 4, -1, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7885, -20190, 20975, 11453, 6363]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N1 B_one_repr
lemma NI71N1 : Nat.card (O ⧸ I71N1) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![733, 1555, 1086, 449, -330]] ![![-49, -71, 18, 9, -4]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1301, -1588, -1149, -69, 172]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![-1301, -1588, -1149, -69, 172]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![54, 17, 11, 1, 0], ![68, 43, 58, 0, 1]] where
  M :=![![![-1301, -1588, -1149, -69, 172], ![1032, 1279, 923, 55, -138], ![-828, -1038, -736, -43, 110], ![660, 822, 569, 34, -86], ![156, 204, 151, 5, -21]]]
  hmulB := by decide  
  f := ![![![-5, -8, -3, -1, 0]], ![![0, -5, -9, -3, -2]], ![![-12, -30, -38, -23, -6]], ![![-6, -13, -12, -6, -2]], ![![-16, -39, -44, -24, -7]]]
  g := ![![![-127, -107, -142, -69, 172], ![102, 86, 114, 55, -138], ![-82, -69, -91, -43, 110], ![64, 54, 71, 34, -86], ![18, 14, 18, 5, -21]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [50, 53, 29, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [45, 72, 49], [72, 0, 24], [0, 1]]
 g := ![![[21, 54, 65], [26, 55], [47, 70], [47, 38, 6], [44, 1], []], ![[72, 0, 53, 61], [59, 25], [34, 69], [16, 32, 47, 27], [], [61, 65]], ![[46, 5, 37, 2], [37, 12], [15, 4], [67, 60, 17, 61], [38, 1], [13, 65]]]
 h' := ![![[45, 72, 49], [69, 48, 24], [36, 58, 36], [59, 16, 17], [63, 27, 58], [0, 0, 1], [0, 1]], ![[72, 0, 24], [40, 26, 16], [56, 53, 68], [71, 6, 54], [9, 18, 9], [70, 70], [45, 72, 49]], ![[0, 1], [67, 72, 33], [47, 35, 42], [33, 51, 2], [62, 28, 6], [8, 3, 72], [72, 0, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 49], []]
 b := ![[], [27, 32, 72], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [50, 53, 29, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-17169713, -47237556, -61943066, -34085722, -15185375]
  a := ![-1, 0, -4, 2, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![39124175, 16235491, 16352762, -34085722, -15185375]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 389017 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, -4, -3, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-5, -4, -3, 1, 0]] 
 ![![73, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![49, 0, 0, 1, 0], ![70, 0, 0, 0, 1]] where
  M :=![![![-5, -4, -3, 1, 0], ![0, -5, -3, -3, 2], ![12, 30, 22, 11, -6], ![-36, -78, -49, -20, 22], ![60, 132, 105, 47, -17]]]
  hmulB := by decide  
  f := ![![![-197, -32, 279, 45, -44]], ![![-36, -17, 37, 7, -6]], ![![2, 14, 14, 1, -2]], ![![-137, -26, 190, 31, -30]], ![![-194, -44, 259, 43, -41]]]
  g := ![![![0, -4, -3, 1, 0], ![1, -5, -3, -3, 2], ![-7, 30, 22, 11, -6], ![6, -78, -49, -20, 22], ![-39, 132, 105, 47, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1

def I73N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-25, -56, -30, 0, 4]] i)))

def SI73N2: IdealEqSpanCertificate' Table ![![-25, -56, -30, 0, 4]] 
 ![![73, 0, 0, 0, 0], ![50, 1, 0, 0, 0], ![55, 0, 1, 0, 0], ![24, 0, 0, 1, 0], ![66, 0, 0, 0, 1]] where
  M :=![![![-25, -56, -30, 0, 4], ![24, 35, 4, -2, 0], ![0, 24, 33, 4, -4], ![-24, -60, -32, 5, 8], ![24, 36, 16, 10, 7]]]
  hmulB := by decide  
  f := ![![![-5521, -6760, -4830, -288, 724]], ![![-3722, -4557, -3256, -194, 488]], ![![-4207, -5152, -3681, -220, 552]], ![![-1776, -2172, -1552, -91, 232]], ![![-4986, -6108, -4364, -262, 655]]]
  g := ![![![57, -56, -30, 0, 4], ![-26, 35, 4, -2, 0], ![-39, 24, 33, 4, -4], ![56, -60, -32, 5, 8], ![-46, 36, 16, 10, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N2 : Nat.card (O ⧸ I73N2) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N2)

lemma isPrimeI73N2 : Ideal.IsPrime I73N2 := prime_ideal_of_norm_prime hp73.out _ NI73N2
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![-1301, -1588, -1149, -69, 172]] ![![-5, -4, -3, 1, 0]]
  ![![5521, 6760, 4830, 288, -724]] where
 M := ![![![5521, 6760, 4830, 288, -724]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI73N1 : IdealMulLeCertificate' Table 
  ![![5521, 6760, 4830, 288, -724]] ![![-25, -56, -30, 0, 4]]
  ![![73, 0, 0, 0, 0]] where
 M := ![![![-73, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1, I73N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
    exact isPrimeI73N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0 ⊙ MulI73N1)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-691, -838, -590, -26, 96]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![-691, -838, -590, -26, 96]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![51, 50, 3, 1, 0], ![42, 69, 21, 0, 1]] where
  M :=![![![-691, -838, -590, -26, 96], ![576, 749, 576, 82, -52], ![-312, -204, 51, 212, 164], ![984, 2148, 2468, 1199, 424], ![1428, 3774, 4828, 2612, 1117]]]
  hmulB := by decide  
  f := ![![![-757, -1574, -746, 14, 96]], ![![576, 683, -120, -74, 28]], ![![168, 996, 1029, 76, -148]], ![![-129, -572, -533, -35, 76]], ![![150, 27, -233, -38, 37]]]
  g := ![![![-43, -78, -32, -26, 96], ![-18, 3, 18, 82, -52], ![-228, -280, -51, 212, 164], ![-987, -1102, -127, 1199, 424], ![-2262, -2581, -335, 2612, 1117]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [63, 45, 39, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [75, 51, 60], [44, 27, 19], [0, 1]]
 g := ![![[59, 38, 22], [51, 31, 10], [6, 18, 31], [39, 45, 72], [40, 1], []], ![[2, 60, 2, 29], [7, 38, 52, 14], [2, 31, 29, 39], [39, 25, 72, 56], [15, 18], [20, 45]], ![[68, 43, 2, 21], [45, 59, 3, 23], [23, 58, 77, 51], [39, 15, 11, 45], [12, 73], [61, 45]]]
 h' := ![![[75, 51, 60], [26, 70, 38], [17, 3, 57], [71, 56, 30], [8, 33, 54], [0, 0, 1], [0, 1]], ![[44, 27, 19], [32, 28, 12], [39, 54, 60], [52, 68, 62], [8, 30, 41], [20, 44, 27], [75, 51, 60]], ![[0, 1], [2, 60, 29], [75, 22, 41], [72, 34, 66], [76, 16, 63], [68, 35, 51], [44, 27, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61, 30], []]
 b := ![[], [52, 51, 39], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [63, 45, 39, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3170169, -6623520, -4227588, -1642470, 1761258]
  a := ![0, 0, 4, -10, 6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![83835, -582618, -459324, -1642470, 1761258]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 493039 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![757, 1574, 746, -14, -96]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![757, 1574, 746, -14, -96]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![23, 76, 1, 0, 0], ![69, 14, 0, 1, 0], ![25, 57, 0, 0, 1]] where
  M :=![![![757, 1574, 746, -14, -96], ![-576, -683, 120, 74, -28], ![-168, -996, -1029, -76, 148], ![888, 2052, 1148, 7, -152], ![-372, -198, 404, 80, -67]]]
  hmulB := by decide  
  f := ![![![691, 838, 590, 26, -96]], ![![-576, -749, -576, -82, 52]], ![![-349, -474, -383, -74, 20]], ![![489, 572, 382, -7, -80]], ![![-215, -323, -290, -84, -7]]]
  g := ![![![-165, -626, 746, -14, -96], ![-98, -117, 120, 74, -28], ![317, 884, -1029, -76, 148], ![-281, -970, 1148, 7, -152], ![-171, -357, 404, 80, -67]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P1 : CertificateIrreducibleZModOfList' 79 2 2 6 [5, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 78], [0, 1]]
 g := ![![[0, 16], [0, 64], [0, 49], [], [], [1]], ![[0, 63], [0, 15], [0, 30], [], [], [1]]]
 h' := ![![[0, 78], [0, 75], [0, 71], [0, 72], [25], [74], [0, 1]], ![[0, 1], [0, 4], [0, 8], [0, 7], [25], [74], [0, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [0, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N1 : CertifiedPrimeIdeal' SI79N1 79 where
  n := 2
  hpos := by decide
  P := [5, 0, 1]
  hirr := P79P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3420, 10264, 16266, 9457, 5567]
  a := ![13, -1, -3, 1, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-14714, -21211, 16266, 9457, 5567]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N1 B_one_repr
lemma NI79N1 : Nat.card (O ⧸ I79N1) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![-691, -838, -590, -26, 96]] ![![757, 1574, 746, -14, -96]]
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

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25, 29, 14, 1, -6]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![25, 29, 14, 1, -6]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![0, 0, 0, 83, 0], ![65, 9, 53, 69, 1]] where
  M :=![![![25, 29, 14, 1, -6], ![-36, -65, -60, -28, 2], ![12, -6, -63, -46, -56], ![-336, -828, -892, -455, -92], ![-282, -855, -1300, -745, -427]]]
  hmulB := by decide  
  f := ![![![-1, -13, -2, 1, 0]], ![![0, -1, -12, -2, 2]], ![![12, 30, 27, 2, -4]], ![![-24, -48, -28, -1, 4]], ![![-13, -31, -9, 1, 1]]]
  g := ![![![5, 1, 4, 5, -6], ![-2, -1, -2, -2, 2], ![44, 6, 35, 46, -56], ![68, 0, 48, 71, -92], ![331, 36, 257, 346, -427]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 4 2 6 [16, 54, 73, 9, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [36, 33, 77, 3], [79, 1, 38, 79], [42, 48, 51, 1], [0, 1]]
 g := ![![[60, 61, 16, 27], [21, 5, 16, 29], [10, 10, 28], [36, 25, 64], [74, 1], []], ![[50, 35, 80, 0, 65, 30], [11, 4, 52, 73, 65, 61], [71, 63, 21], [47, 57, 27], [37, 49, 8, 20, 40, 70], [49, 49, 9]], ![[11, 77, 41, 80, 27, 79], [47, 27, 72, 10, 62, 8], [63, 4, 9], [38, 25, 1], [75, 76, 62, 11, 7, 39], [67, 50, 16]], ![[32, 21, 17, 37, 46, 49], [64, 20, 23, 25, 54, 26], [54, 76, 3], [61, 70, 70], [70, 22, 19, 38, 68, 75], [44, 10, 1]]]
 h' := ![![[36, 33, 77, 3], [79, 47, 81, 39], [4, 60, 8, 64], [74, 50, 43, 32], [61, 55, 22, 8], [0, 0, 1], [0, 1]], ![[79, 1, 38, 79], [68, 14, 11, 50], [4, 42, 70, 31], [12, 79, 80, 41], [73, 2, 60, 44], [14, 25, 17, 47], [36, 33, 77, 3]], ![[42, 48, 51, 1], [30, 16, 37, 1], [26, 28, 4, 9], [72, 60, 55, 80], [4, 65, 17, 1], [23, 56, 67, 54], [79, 1, 38, 79]], ![[0, 1], [51, 6, 37, 76], [65, 36, 1, 62], [79, 60, 71, 13], [15, 44, 67, 30], [64, 2, 81, 65], [42, 48, 51, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [25, 51, 24], []]
 b := ![[], [], [79, 2, 20, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 4
  hpos := by decide
  P := [16, 54, 73, 9, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![384208485, 1047312804, 1352780797, 741258717, 318683771]
  a := ![-1, -3, 2, -1, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-244942610, -21937845, -187198302, -255999054, 318683771]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 47458321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -13, -2, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-1, -13, -2, 1, 0]] 
 ![![83, 0, 0, 0, 0], ![28, 1, 0, 0, 0], ![46, 0, 1, 0, 0], ![40, 0, 0, 1, 0], ![81, 0, 0, 0, 1]] where
  M :=![![![-1, -13, -2, 1, 0], ![0, -1, -12, -2, 2], ![12, 30, 27, 2, -4], ![-24, -48, -28, -1, 4], ![6, 3, -8, -1, 1]]]
  hmulB := by decide  
  f := ![![![25, 29, 14, 1, -6]], ![![8, 9, 4, 0, -2]], ![![14, 16, 7, 0, -4]], ![![8, 4, -4, -5, -4]], ![![21, 18, -2, -8, -11]]]
  g := ![![![5, -13, -2, 1, 0], ![6, -1, -12, -2, 2], ![-22, 30, 27, 2, -4], ![28, -48, -28, -1, 4], ![3, 3, -8, -1, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![25, 29, 14, 1, -6]] ![![-1, -13, -2, 1, 0]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, -34, -131, -17, 20]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![47, -34, -131, -17, 20]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![15, 53, 68, 1, 0], ![24, 30, 29, 0, 1]] where
  M :=![![![47, -34, -131, -17, 20], ![120, 347, 249, 9, -34], ![-204, -390, -154, 11, 18], ![108, 66, -109, -28, 22], ![168, 414, 261, 17, -37]]]
  hmulB := by decide  
  f := ![![![-185, -226, -161, -9, 24]], ![![144, 175, 125, 7, -18]], ![![-108, -126, -88, -1, 14]], ![![-27, -29, -19, 2, 4]], ![![-36, -42, -29, 0, 5]]]
  g := ![![![-2, 3, 5, -17, 20], ![9, 10, 7, 9, -34], ![-9, -17, -16, 11, 18], ![0, 10, 13, -28, 22], ![9, 7, 2, 17, -37]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [80, 62, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 77, 23], [58, 11, 66], [0, 1]]
 g := ![![[43, 8, 50], [46, 64], [76, 80], [86, 39, 81], [27, 0, 1], []], ![[61, 66, 83, 29], [54, 68], [60, 4], [53, 21, 71, 28], [50, 37, 72, 24], [71, 84]], ![[62, 17, 46, 83], [18, 17], [15, 32], [62, 62, 12, 38], [77, 4, 59, 70], [28, 84]]]
 h' := ![![[31, 77, 23], [1, 79, 53], [78, 75, 81], [62, 45, 76], [65, 17, 9], [0, 0, 1], [0, 1]], ![[58, 11, 66], [30, 7, 86], [16, 44, 35], [59, 15, 2], [40, 69, 45], [87, 60, 11], [31, 77, 23]], ![[0, 1], [75, 3, 39], [64, 59, 62], [75, 29, 11], [42, 3, 35], [56, 29, 77], [58, 11, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55, 22], []]
 b := ![[], [16, 61, 30], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [80, 62, 0, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4623953, 13469838, 19250387, 10834894, 5714489]
  a := ![3, 0, 7, -4, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3315137, -8227126, -9924074, 10834894, 5714489]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 704969 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-923, -1124, -803, -47, 120]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![-923, -1124, -803, -47, 120]] 
 ![![89, 0, 0, 0, 0], ![24, 1, 0, 0, 0], ![47, 0, 1, 0, 0], ![29, 0, 0, 1, 0], ![29, 0, 0, 0, 1]] where
  M :=![![![-923, -1124, -803, -47, 120], ![720, 877, 629, 37, -94], ![-564, -690, -496, -29, 74], ![444, 546, 391, 22, -58], ![108, 132, 97, 7, -15]]]
  hmulB := by decide  
  f := ![![![5, 16, -13, -27, -20]], ![![0, 1, -7, -9, -6]], ![![-1, -2, -21, -22, -14]], ![![-19, -50, -74, -47, -22]], ![![-43, -116, -160, -94, -43]]]
  g := ![![![693, -1124, -803, -47, 120], ![-542, 877, 629, 37, -94], ![427, -690, -496, -29, 74], ![-337, 546, 391, 22, -58], ![-83, 132, 97, 7, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1

def I89N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 14, 18, 10, 4]] i)))

def SI89N2: IdealEqSpanCertificate' Table ![![5, 14, 18, 10, 4]] 
 ![![89, 0, 0, 0, 0], ![86, 1, 0, 0, 0], ![80, 0, 1, 0, 0], ![62, 0, 0, 1, 0], ![53, 0, 0, 0, 1]] where
  M :=![![![5, 14, 18, 10, 4], ![24, 65, 84, 46, 20], ![120, 324, 411, 224, 92], ![552, 1500, 1928, 1055, 448], ![1284, 3474, 4432, 2420, 1009]]]
  hmulB := by decide  
  f := ![![![-635, -1102, -1142, -98, 172]], ![![-602, -1043, -1088, -94, 164]], ![![-584, -1012, -1037, -88, 156]], ![![-434, -760, -796, -69, 120]], ![![-371, -640, -670, -58, 101]]]
  g := ![![![-39, 14, 18, 10, 4], ![-182, 65, 84, 46, 20], ![-892, 324, 411, 224, 92], ![-4178, 1500, 1928, 1055, 448], ![-9613, 3474, 4432, 2420, 1009]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N2 : Nat.card (O ⧸ I89N2) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N2)

lemma isPrimeI89N2 : Ideal.IsPrime I89N2 := prime_ideal_of_norm_prime hp89.out _ NI89N2
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![47, -34, -131, -17, 20]] ![![-923, -1124, -803, -47, 120]]
  ![![635, 1102, 1142, 98, -172]] where
 M := ![![![635, 1102, 1142, 98, -172]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![635, 1102, 1142, 98, -172]] ![![5, 14, 18, 10, 4]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![581, 955, 235, -42, -24]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![581, 955, 235, -42, -24]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![81, 2, 1, 0, 0], ![32, 77, 0, 1, 0], ![42, 35, 0, 0, 1]] where
  M :=![![![581, 955, 235, -42, -24], ![-144, 221, 553, 67, -84], ![-504, -1404, -972, -35, 134], ![804, 1506, 571, -34, -70], ![42, 579, 697, 58, -101]]]
  hmulB := by decide  
  f := ![![![305, 359, 245, 0, -46]], ![![-276, -385, -331, -77, 0]], ![![249, 289, 193, -5, -40]], ![![-128, -211, -212, -77, -22]], ![![12, -38, -82, -65, -35]]]
  g := ![![![-166, 47, 235, -42, -24], ![-449, -32, 553, 67, -84], ![760, -15, -972, -35, 134], ![-427, 56, 571, -34, -70], ![-557, -18, 697, 58, -101]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [15, 88, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 96], [0, 1]]
 g := ![![[77, 64], [32], [47], [93], [88], [9, 1]], ![[71, 33], [32], [47], [93], [88], [18, 96]]]
 h' := ![![[9, 96], [84, 8], [46, 56], [13, 12], [27, 44], [59, 66], [0, 1]], ![[0, 1], [59, 89], [65, 41], [24, 85], [35, 53], [71, 31], [9, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46]]
 b := ![[], [42, 23]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [15, 88, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1526, 4752, 7863, 4379, 3289]
  a := ![1, 1, 2, -1, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9419, -4776, 7863, 4379, 3289]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 108, -105, -25, 18]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![137, 108, -105, -25, 18]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![1, 70, 1, 0, 0], ![27, 48, 0, 1, 0], ![24, 93, 0, 0, 1]] where
  M :=![![![137, 108, -105, -25, 18], ![108, 407, 353, 21, -50], ![-300, -642, -322, 3, 42], ![252, 330, -9, -28, 6], ![168, 492, 357, 15, -49]]]
  hmulB := by decide  
  f := ![![![-127, -192, -135, -29, 30]], ![![180, 323, 229, 75, -58]], ![![125, 224, 159, 52, -40]], ![![63, 126, 90, 35, -24]], ![![132, 243, 174, 60, -43]]]
  g := ![![![5, 72, -105, -25, 18], ![4, -213, 353, 21, -50], ![-11, 184, -322, 3, 42], ![9, 18, -9, -28, 6], ![6, -213, 357, 15, -49]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P1 : CertificateIrreducibleZModOfList' 97 2 2 6 [39, 92, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 96], [0, 1]]
 g := ![![[72, 22], [64], [3], [86], [2], [5, 1]], ![[85, 75], [64], [3], [86], [2], [10, 96]]]
 h' := ![![[5, 96], [20, 33], [73, 8], [53, 10], [20, 38], [96, 83], [0, 1]], ![[0, 1], [88, 64], [16, 89], [6, 87], [16, 59], [26, 14], [5, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [80]]
 b := ![[], [94, 40]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N1 : CertifiedPrimeIdeal' SI97N1 97 where
  n := 2
  hpos := by decide
  P := [39, 92, 1]
  hirr := P97P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![321, -192, -153, 103, 13]
  a := ![4, 0, -1, 1, -1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-27, 45, -153, 103, 13]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N1 B_one_repr
lemma NI97N1 : Nat.card (O ⧸ I97N1) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N1

def I97N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-61, -77, -54, -3, 8]] i)))

def SI97N2: IdealEqSpanCertificate' Table ![![-61, -77, -54, -3, 8]] 
 ![![97, 0, 0, 0, 0], ![25, 1, 0, 0, 0], ![54, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![67, 0, 0, 0, 1]] where
  M :=![![![-61, -77, -54, -3, 8], ![48, 59, 40, 2, -6], ![-36, -42, -29, -2, 4], ![24, 24, 16, -1, -4], ![6, 3, -4, -5, -3]]]
  hmulB := by decide  
  f := ![![![47, 71, 30, 31, -18]], ![![11, 16, 6, 7, -4]], ![![30, 48, 23, 20, -12]], ![![-8, -20, -16, -5, 4]], ![![47, 80, 42, 30, -19]]]
  g := ![![![44, -77, -54, -3, 8], ![-33, 59, 40, 2, -6], ![24, -42, -29, -2, 4], ![-12, 24, 16, -1, -4], ![4, 3, -4, -5, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N2 : Nat.card (O ⧸ I97N2) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N2)

lemma isPrimeI97N2 : Ideal.IsPrime I97N2 := prime_ideal_of_norm_prime hp97.out _ NI97N2
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![581, 955, 235, -42, -24]] ![![137, 108, -105, -25, 18]]
  ![![97621, 274895, 192250, 7051, -26498]] where
 M := ![![![97621, 274895, 192250, 7051, -26498]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI97N1 : IdealMulLeCertificate' Table 
  ![![97621, 274895, 192250, 7051, -26498]] ![![-61, -77, -54, -3, 8]]
  ![![97, 0, 0, 0, 0]] where
 M := ![![![329315, 717218, 367824, -2134, -48112]]]
 hmul := by decide  
 g := ![![![![3395, 7394, 3792, -22, -496]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0, 0, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0, 0, 0]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![0, 0, 0, 101, 0], ![0, 0, 0, 0, 101]] where
  M :=![![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![0, 0, 0, 101, 0], ![0, 0, 0, 0, 101]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 5 2 6 [39, 36, 36, 79, 27, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [71, 24, 61, 90, 46], [52, 38, 79, 33, 7], [15, 45, 46, 45, 50], [37, 94, 16, 34, 99], [0, 1]]
 g := ![![[94, 58, 61, 0, 77], [59, 26, 32, 85], [30, 78, 64, 62, 56], [86, 23, 55, 17], [74, 1], []], ![[24, 20, 10, 27, 66, 23, 42, 69], [42, 43, 66, 87], [28, 43, 79, 67, 2, 49, 71, 32], [28, 29, 45, 77], [51, 47, 64, 4], [72, 5, 52, 22, 30, 97, 12, 73]], ![[4, 97, 65, 43, 28, 1, 27, 39], [58, 68, 74, 70], [14, 84, 39, 94, 90, 86, 95, 8], [25, 50, 13, 85], [97, 80, 54, 96], [77, 13, 97, 20, 57, 3, 34, 40]], ![[3, 27, 90, 10, 35, 21, 27, 46], [34, 14, 71, 100], [0, 8, 73, 40, 6, 35, 98, 83], [100, 26, 82, 79], [33, 47, 42, 19], [9, 47, 43, 71, 82, 95, 75, 63]], ![[46, 60, 61, 47, 89, 25, 32, 61], [7, 41, 68, 65], [55, 36, 20, 84, 42, 9, 54, 57], [75, 40, 10, 24], [21, 33, 71, 58], [76, 42, 99, 62, 28, 68, 18, 93]]]
 h' := ![![[71, 24, 61, 90, 46], [69, 91, 76, 75, 28], [42, 18, 82, 5, 61], [10, 91, 61, 77, 64], [43, 24, 27, 77, 44], [0, 0, 0, 1], [0, 1]], ![[52, 38, 79, 33, 7], [14, 25, 56, 2, 70], [6, 49, 30, 27, 84], [23, 10, 3, 76, 7], [99, 94, 95, 27, 73], [88, 100, 91, 58, 99], [71, 24, 61, 90, 46]], ![[15, 45, 46, 45, 50], [66, 90, 66, 34, 90], [56, 81, 20, 30, 26], [58, 16, 15, 85, 63], [86, 93, 90, 44, 40], [43, 58, 84, 9, 46], [52, 38, 79, 33, 7]], ![[37, 94, 16, 34, 99], [57, 31, 6, 15, 3], [75, 45, 65, 18, 91], [45, 80, 30, 2, 95], [62, 46, 26, 20, 68], [95, 39, 9, 100, 76], [15, 45, 46, 45, 50]], ![[0, 1], [35, 66, 99, 76, 11], [56, 9, 5, 21, 41], [23, 5, 93, 63, 74], [76, 46, 65, 34, 78], [17, 5, 18, 34, 82], [37, 94, 16, 34, 99]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 66, 27, 22], [], [], []]
 b := ![[], [21, 4, 79, 45, 61], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 5
  hpos := by decide
  P := [39, 36, 36, 79, 27, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-18545844774046408, -50261700577248740, -64296922955977031, -35134625138223475, -14749000907221387]
  a := ![7, 2, -24, 0, -23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-183622225485608, -497640599774740, -636603197583931, -347867575625975, -146029711952687]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-55, -195, -261, -156, -64]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![-55, -195, -261, -156, -64]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![0, 0, 0, 103, 0], ![25, 98, 25, 99, 1]] where
  M :=![![![-55, -195, -261, -156, -64], ![-384, -1015, -1311, -709, -312], ![-1872, -5064, -6404, -3495, -1418], ![-8508, -23142, -29829, -16330, -6990], ![-20034, -54147, -68959, -37632, -15621]]]
  hmulB := by decide  
  f := ![![![131, 231, 83, -6, -10]], ![![-60, -19, 75, 13, -12]], ![![-72, -240, -186, -9, 26]], ![![156, 318, 141, -4, -18]], ![![107, 286, 183, 5, -25]]]
  g := ![![![15, 59, 13, 60, -64], ![72, 287, 63, 293, -312], ![326, 1300, 282, 1329, -1418], ![1614, 6426, 1407, 6560, -6990], ![3597, 14337, 3122, 14649, -15621]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 4 2 6 [20, 100, 4, 67, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [91, 49, 14, 69], [42, 85, 26, 45], [6, 71, 63, 92], [0, 1]]
 g := ![![[83, 10, 46, 92], [0, 94, 50, 68], [48, 100, 31, 50], [85, 70, 29], [56, 36, 1], []], ![[61, 56, 32, 4, 101, 87], [70, 13, 88, 32, 91, 27], [86, 57, 32, 87, 13, 75], [6, 12, 18], [73, 55, 15], [83, 54, 93, 20, 6, 42]], ![[59, 87, 66, 40, 86, 5], [70, 43, 88, 75, 36, 53], [58, 6, 43, 78, 11, 95], [10, 10, 79], [36, 99, 7], [17, 31, 95, 91, 1, 73]], ![[34, 14, 93, 26, 83, 49], [87, 21, 10, 44, 74, 4], [19, 52, 63, 81, 2, 16], [97, 31, 17], [78, 43, 64], [79, 25, 54, 0, 85, 8]]]
 h' := ![![[91, 49, 14, 69], [0, 33, 74, 35], [70, 91, 26, 45], [14, 56, 7, 87], [13, 66, 70, 21], [0, 0, 0, 1], [0, 1]], ![[42, 85, 26, 45], [18, 32, 39, 40], [65, 56, 44, 94], [86, 87, 24, 15], [0, 28, 57, 92], [11, 46, 85, 85], [91, 49, 14, 69]], ![[6, 71, 63, 92], [35, 33, 25, 69], [74, 99, 53, 64], [7, 0, 77, 98], [1, 85, 2, 64], [0, 68, 102, 25], [42, 85, 26, 45]], ![[0, 1], [64, 5, 68, 62], [52, 63, 83, 3], [81, 63, 98, 6], [95, 27, 77, 29], [78, 92, 19, 95], [6, 71, 63, 92]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [100, 2, 40], []]
 b := ![[], [], [102, 18, 49, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 4
  hpos := by decide
  P := [20, 100, 4, 67, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![48163533636, 130579804977, 167151168710, 91355566883, 38412018292]
  a := ![1, 3, -7, -1, -8]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-8855698288, -35279592113, -7700478530, -36033342175, 38412018292]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 112550881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 231, 83, -6, -10]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![131, 231, 83, -6, -10]] 
 ![![103, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![39, 0, 1, 0, 0], ![100, 0, 0, 1, 0], ![44, 0, 0, 0, 1]] where
  M :=![![![131, 231, 83, -6, -10], ![-60, -19, 75, 13, -12], ![-72, -240, -186, -9, 26], ![156, 318, 141, -4, -18], ![-18, 63, 115, 12, -17]]]
  hmulB := by decide  
  f := ![![![-55, -195, -261, -156, -64]], ![![-8, -25, -33, -19, -8]], ![![-39, -123, -161, -93, -38]], ![![-136, -414, -543, -310, -130]], ![![-218, -609, -781, -432, -179]]]
  g := ![![![-38, 231, 83, -6, -10], ![-35, -19, 75, 13, -12], ![86, -240, -186, -9, 26], ![-65, 318, 141, -4, -18], ![-53, 63, 115, 12, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![-55, -195, -261, -156, -64]] ![![131, 231, 83, -6, -10]]
  ![![103, 0, 0, 0, 0]] where
 M := ![![![103, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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


lemma PB441I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB441I2 : PrimesBelowBoundCertificateInterval O 61 103 441 where
  m := 9
  g := ![2, 2, 3, 2, 2, 3, 3, 1, 2]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB441I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1, I73N2]
    · exact ![I79N0, I79N1]
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1, I89N2]
    · exact ![I97N0, I97N1, I97N2]
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
    · exact ![357911, 5041]
    · exact ![389017, 73, 73]
    · exact ![493039, 6241]
    · exact ![47458321, 83]
    · exact ![704969, 89, 89]
    · exact ![9409, 9409, 97]
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
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
      exact NI73N2
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
      exact NI89N2
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
      exact NI97N2
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
  β := ![I73N1, I73N2, I83N1, I89N1, I89N2, I97N2, I103N1]
  Il := ![[], [], [I73N1, I73N2], [], [I83N1], [I89N1, I89N2], [I97N2], [], [I103N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
