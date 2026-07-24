
import IdealArithmetic.Examples.NF5_3_1518750000_3.RI5_3_1518750000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2927, -2463, 1087, 3189, -399]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![2927, -2463, 1087, 3189, -399]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![22, 37, 1, 0, 0], ![32, 25, 0, 1, 0], ![37, 23, 0, 0, 1]] where
  M :=![![![2927, -2463, 1087, 3189, -399], ![9576, -3058, -795, 4137, 3189], ![-76536, 57411, -22336, -74583, 4137], ![21720, -31119, 19241, 39836, -14499], ![336600, -231711, 80151, 301845, 476]]]
  hmulB := by decide  
  f := ![![![-43315, 16233, 10841, 7917, 1869]], ![![-44856, -15280, 33363, 7653, 7917]], ![![-41830, -2005, 22663, 7344, 5100]], ![![-36464, 1313, 17648, 6455, 3876]], ![![-39973, 4006, 17573, 7119, 3770]]]
  g := ![![![-1616, -1690, 1087, 3189, -399], ![-3333, -2245, -795, 4137, 3189], ![39529, 39601, -22336, -74583, 4137], ![-17013, -20977, 19241, 39836, -14499], ![-165722, -160513, 80151, 301845, 476]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [40, 66, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 66], [0, 1]]
 g := ![![[5, 62], [3, 64], [60], [10], [1], [1]], ![[0, 5], [0, 3], [60], [10], [1], [1]]]
 h' := ![![[1, 66], [14, 53], [59, 8], [28, 23], [19, 55], [27, 1], [0, 1]], ![[0, 1], [0, 14], [0, 59], [51, 44], [7, 12], [28, 66], [1, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [8, 51]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [40, 66, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3872, 4391, -2642, -5704, 1465]
  a := ![0, -1, -4, -1, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2725, 3150, -2642, -5704, 1465]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-73, 0, 22, 9, 5]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![-73, 0, 22, 9, 5]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![65, 15, 1, 0, 0], ![6, 44, 0, 1, 0], ![37, 29, 0, 0, 1]] where
  M :=![![![-73, 0, 22, 9, 5], ![-120, 2, 37, 15, 9], ![-216, 15, 62, 15, 15], ![48, -6, -10, 2, -5], ![48, -30, 14, 45, 2]]]
  hmulB := by decide  
  f := ![![![197, -222, 52, -39, 19]], ![![-456, 482, -103, 87, -39]], ![![103, -123, 31, -21, 11]], ![![-294, 310, -66, 56, -25]], ![![-85, 82, -15, 15, -6]]]
  g := ![![![-26, -13, 22, 9, 5], ![-44, -22, 37, 15, 9], ![-73, -30, 62, 15, 15], ![13, 3, -10, 2, -5], ![-18, -34, 14, 45, 2]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P1 : CertificateIrreducibleZModOfList' 67 2 2 6 [23, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [63, 66], [0, 1]]
 g := ![![[6, 35], [56, 14], [1], [62], [16], [1]], ![[0, 32], [0, 53], [1], [62], [16], [1]]]
 h' := ![![[63, 66], [52, 13], [36, 9], [40, 1], [27, 53], [44, 63], [0, 1]], ![[0, 1], [0, 54], [0, 58], [36, 66], [16, 14], [60, 4], [63, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60]]
 b := ![[], [60, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N1 : CertifiedPrimeIdeal' SI67N1 67 where
  n := 2
  hpos := by decide
  P := [23, 4, 1]
  hirr := P67P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5492, -3857, 4328, 2620, 307]
  a := ![3, -64, 1, -1, 2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4521, -2880, 4328, 2620, 307]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N1 B_one_repr
lemma NI67N1 : Nat.card (O ⧸ I67N1) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-176117, 189969, -41667, 34230, -15556]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![-176117, 189969, -41667, 34230, -15556]] 
 ![![67, 0, 0, 0, 0], ![15, 1, 0, 0, 0], ![43, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![50, 0, 0, 0, 1]] where
  M :=![![![-176117, 189969, -41667, 34230, -15556], ![373344, -409457, 92962, -72684, 34230], ![-821520, 886794, -194807, 159684, -72684], ![701496, -762027, 169641, -136439, 62956], ![-227976, 246549, -54373, 44322, -20255]]]
  hmulB := by decide  
  f := ![![![-18983, 4215, 3181, -5874, -7970]], ![![-1395, -1124, 1481, 1374, -1872]], ![![-10079, 4245, -58, -5646, -2426]], ![![-13225, 6618, -986, -8729, -2252]], ![![-7714, -13071, 14157, 16230, -16521]]]
  g := ![![![-9363, 189969, -41667, 34230, -15556], ![17459, -409457, 92962, -72684, 34230], ![-43447, 886794, -194807, 159684, -72684], ![35399, -762027, 169641, -136439, 62956], ![-11896, 246549, -54373, 44322, -20255]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![2927, -2463, 1087, 3189, -399]] ![![-73, 0, 22, 9, 5]]
  ![![-18983, 4215, 3181, -5874, -7970]] where
 M := ![![![-18983, 4215, 3181, -5874, -7970]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![-18983, 4215, 3181, -5874, -7970]] ![![-176117, 189969, -41667, 34230, -15556]]
  ![![67, 0, 0, 0, 0]] where
 M := ![![![67, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1756291, 248001, 717833, 312664, 151262]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-1756291, 248001, 717833, 312664, 151262]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![0, 0, 0, 71, 0], ![10, 31, 34, 26, 1]] where
  M :=![![![-1756291, 248001, 717833, 312664, 151262], ![-3630288, 512639, 1483788, 646290, 312664], ![-7503936, 1059672, 3067057, 1335906, 646290], ![1166808, -164767, -476899, -207719, -100494], ![-1591656, 224769, 650591, 283404, 137089]]]
  hmulB := by decide  
  f := ![![![-3869, 4207, -939, 752, -348]], ![![8352, -9089, 2030, -1626, 752]], ![![-18048, 19632, -4381, 3522, -1626]], ![![15528, -16889, 3769, -3025, 1400]], ![![74, -82, 19, -12, 7]]]
  g := ![![![-46041, -62551, -62325, -50988, 151262], ![-95168, -129295, -128828, -105394, 312664], ![-196716, -267258, -266293, -217854, 646290], ![30588, 41557, 41407, 33875, -100494], ![-41726, -56690, -56485, -46210, 137089]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 4 2 6 [41, 41, 36, 2, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 35, 3, 43], [6, 2, 15, 51], [39, 33, 53, 48], [0, 1]]
 g := ![![[15, 15, 23, 25], [67, 66, 44, 8], [38, 53, 25, 12], [50, 65, 4], [1], []], ![[42, 39, 55, 49, 23, 37], [60, 62, 20, 18, 49, 6], [16, 33, 11, 41, 64, 25], [66, 0, 20], [19, 45, 45], [64, 39, 3]], ![[32, 58, 55, 41, 53, 61], [39, 63, 67, 24, 66, 46], [69, 13, 55, 59, 35, 31], [55, 67, 48], [39, 30, 1], [47, 20, 45]], ![[40, 25, 31, 26, 16, 29], [36, 10, 53, 70, 54, 29], [23, 26, 20, 51, 44, 49], [28, 11, 4], [13, 56, 6], [31, 54, 32]]]
 h' := ![![[24, 35, 3, 43], [22, 30, 14, 66], [4, 15, 19, 24], [57, 67, 4, 15], [30, 30, 35, 69], [0, 0, 1], [0, 1]], ![[6, 2, 15, 51], [70, 38, 25, 46], [8, 28, 43, 50], [69, 15, 10, 13], [52, 5, 34, 34], [11, 13, 41, 51], [24, 35, 3, 43]], ![[39, 33, 53, 48], [38, 16, 3, 6], [41, 60, 1, 44], [17, 39, 29, 12], [0, 60, 60, 41], [26, 46, 16, 1], [6, 2, 15, 51]], ![[0, 1], [12, 58, 29, 24], [42, 39, 8, 24], [31, 21, 28, 31], [55, 47, 13, 69], [37, 12, 13, 19], [39, 33, 53, 48]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [22, 29, 66], []]
 b := ![[], [], [51, 69, 62, 53], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 4
  hpos := by decide
  P := [41, 41, 36, 2, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-156720695, 104142653, -34050655, -135802957, -3551269]
  a := ![1, -3, -2, -1, -3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1707155, 3017352, 1221021, -612253, -3551269]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 25411681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3869, 4207, -939, 752, -348]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-3869, 4207, -939, 752, -348]] 
 ![![71, 0, 0, 0, 0], ![45, 1, 0, 0, 0], ![34, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![27, 0, 0, 0, 1]] where
  M :=![![![-3869, 4207, -939, 752, -348], ![8352, -9089, 2030, -1626, 752], ![-18048, 19632, -4381, 3522, -1626], ![15528, -16889, 3769, -3025, 1400], ![-5064, 5493, -1231, 936, -451]]]
  hmulB := by decide  
  f := ![![![-1756291, 248001, 717833, 312664, 151262]], ![![-1164273, 164404, 475863, 207270, 100274]], ![![-946730, 133686, 386949, 168542, 81538]], ![![-280404, 39595, 114607, 49919, 24150]], ![![-690303, 97476, 282142, 122892, 59453]]]
  g := ![![![-2266, 4207, -939, 752, -348], ![4895, -9089, 2030, -1626, 752], ![-10576, 19632, -4381, 3522, -1626], ![9097, -16889, 3769, -3025, 1400], ![-2950, 5493, -1231, 936, -451]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-1756291, 248001, 717833, 312664, 151262]] ![![-3869, 4207, -939, 752, -348]]
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


def P73P0 : CertificateIrreducibleZModOfList' 73 5 2 6 [31, 20, 17, 26, 18, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 40, 27, 69, 64], [47, 35, 41, 32, 33], [17, 1, 24, 24, 65], [31, 69, 54, 21, 57], [0, 1]]
 g := ![![[6, 60, 21, 65, 24], [48, 58, 9, 46], [43, 49, 16, 32], [15, 51, 6, 55, 1], [], []], ![[39, 68, 14, 43, 0, 29, 57, 71], [69, 29, 34, 8], [52, 56, 54, 48], [67, 15, 43, 69, 17, 43, 33, 18], [69, 70, 52, 12], [42, 34, 1, 8]], ![[48, 38, 14, 32, 58, 48, 70, 53], [11, 67, 30, 6], [4, 5, 11, 36], [29, 3, 70, 58, 20, 63, 16, 58], [55, 14, 25, 67], [19, 61, 30, 67]], ![[22, 50, 54, 56, 20, 67, 51, 35], [72, 63, 65, 25], [60, 18, 71, 50], [13, 9, 2, 47, 61, 46, 45, 57], [18, 56, 50, 72], [27, 42, 70, 64]], ![[24, 23, 58, 6, 53, 20, 62, 69], [55, 71, 59, 3], [61, 21, 35, 23], [1, 5, 42, 61, 8, 32, 6, 25], [5, 40, 64, 38], [57, 8, 49, 37]]]
 h' := ![![[33, 40, 27, 69, 64], [7, 58, 33, 27, 43], [53, 61, 34, 49, 51], [46, 17, 72, 57, 18], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[47, 35, 41, 32, 33], [63, 67, 68, 7, 38], [42, 54, 56, 55, 64], [11, 49, 44, 18, 62], [14, 0, 64, 54, 61], [6, 16, 59, 31, 42], [33, 40, 27, 69, 64]], ![[17, 1, 24, 24, 65], [51, 54, 25, 64, 16], [10, 19, 44, 63, 15], [39, 7, 57, 12, 67], [24, 61, 31, 15, 22], [14, 70, 51, 64, 33], [47, 35, 41, 32, 33]], ![[31, 69, 54, 21, 57], [27, 56, 61, 25, 13], [19, 12, 24, 58, 68], [28, 29, 65, 67, 59], [8, 4, 38, 1, 41], [36, 17, 49, 6, 27], [17, 1, 24, 24, 65]], ![[0, 1], [43, 57, 32, 23, 36], [19, 0, 61, 67, 21], [42, 44, 54, 65, 13], [0, 8, 13, 3, 21], [70, 43, 59, 45, 44], [31, 69, 54, 21, 57]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40, 59, 34, 22], [], [], []]
 b := ![[], [62, 55, 57, 53, 43], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 5
  hpos := by decide
  P := [31, 20, 17, 26, 18, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![12511225961, -382925046340, 328897615232, 482932169410, -335936962162]
  a := ![1, 19, 3, -1, 6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![171386657, -5245548580, 4505446784, 6615509170, -4601876194]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-29, 18, -4, -24, -8]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![-29, 18, -4, -24, -8]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![63, 51, 32, 1, 0], ![22, 62, 23, 0, 1]] where
  M :=![![![-29, 18, -4, -24, -8], ![192, -149, 62, 192, -24], ![576, -168, -59, 228, 192], ![-1056, 660, -194, -863, -58], ![-1200, -114, 532, 108, -845]]]
  hmulB := by decide  
  f := ![![![421, -30, -184, -72, -40]], ![![960, -179, -350, -168, -72]], ![![1728, -120, -773, -300, -168]], ![![1653, -189, -684, -287, -146]], ![![1378, -184, -553, -240, -117]]]
  g := ![![![21, 22, 12, -24, -8], ![-144, -107, -70, 192, -24], ![-228, -300, -149, 228, 192], ![691, 611, 364, -863, -58], ![134, 592, 209, 108, -845]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [43, 78, 45, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 10, 6], [3, 68, 73], [0, 1]]
 g := ![![[25, 21, 20], [61, 40, 1], [29, 10, 31], [33, 63, 73], [34, 1], []], ![[8, 16, 35, 28], [65, 51, 76, 57], [41, 1, 39, 68], [43, 3, 6, 75], [18, 42], [1, 36]], ![[2, 75, 70, 67], [71, 73, 16, 11], [76, 64, 68, 26], [1, 47, 63, 64], [57, 21], [13, 36]]]
 h' := ![![[31, 10, 6], [63, 52, 40], [17, 3, 1], [3, 30, 30], [39, 70, 51], [0, 0, 1], [0, 1]], ![[3, 68, 73], [1, 17, 30], [1, 51, 7], [33, 61, 8], [47, 33, 17], [49, 21, 68], [31, 10, 6]], ![[0, 1], [23, 10, 9], [29, 25, 71], [25, 67, 41], [7, 55, 11], [3, 58, 10], [3, 68, 73]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25, 62], []]
 b := ![[], [52, 73, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [43, 78, 45, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7851225, -5827510, 2238100, 7572332, -364648]
  a := ![-1, 0, -2, 2, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5837765, -4676054, -2932780, 7572332, -364648]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 493039 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 5, -33, -12, -8]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![127, 5, -33, -12, -8]] 
 ![![79, 0, 0, 0, 0], ![16, 1, 0, 0, 0], ![60, 0, 1, 0, 0], ![47, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![127, 5, -33, -12, -8], ![192, 7, -50, -18, -12], ![288, 12, -77, -30, -18], ![-72, -3, 19, 7, 4], ![-24, -9, 11, 12, 1]]]
  hmulB := by decide  
  f := ![![![-191, 235, -65, 36, -22]], ![![-32, 41, -12, 6, -4]], ![![-156, 192, -53, 30, -18]], ![![-103, 128, -36, 19, -12]], ![![-10, 11, -3, 0, -1]]]
  g := ![![![33, 5, -33, -12, -8], ![50, 7, -50, -18, -12], ![78, 12, -77, -30, -18], ![-19, -3, 19, 7, 4], ![-14, -9, 11, 12, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1

def I79N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![235, -389, 149, -48, 46]] i)))

def SI79N2: IdealEqSpanCertificate' Table ![![235, -389, 149, -48, 46]] 
 ![![79, 0, 0, 0, 0], ![32, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![22, 0, 0, 1, 0], ![76, 0, 0, 0, 1]] where
  M :=![![![235, -389, 149, -48, 46], ![-1104, 925, -78, 210, -48], ![1152, -1824, 673, -234, 210], ![-1416, 1629, -405, 277, -144], ![360, -513, 171, -72, 55]]]
  hmulB := by decide  
  f := ![![![541, 77, -179, -120, -16]], ![![224, 35, -76, -54, -8]], ![![57, -15, -2, 18, -6]], ![![154, 23, -53, -35, 2]], ![![412, 161, -209, -228, -3]]]
  g := ![![![124, -389, 149, -48, 46], ![-398, 925, -78, 210, -48], ![591, -1824, 673, -234, 210], ![-601, 1629, -405, 277, -144], ![173, -513, 171, -72, 55]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N2 : Nat.card (O ⧸ I79N2) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N2)

lemma isPrimeI79N2 : Ideal.IsPrime I79N2 := prime_ideal_of_norm_prime hp79.out _ NI79N2
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![-29, 18, -4, -24, -8]] ![![127, 5, -33, -12, -8]]
  ![![541, 77, -179, -120, -16]] where
 M := ![![![541, 77, -179, -120, -16]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI79N1 : IdealMulLeCertificate' Table 
  ![![541, 77, -179, -120, -16]] ![![235, -389, 149, -48, 46]]
  ![![79, 0, 0, 0, 0]] where
 M := ![![![79, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53275, -7527, -21781, -9490, -4590]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![53275, -7527, -21781, -9490, -4590]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![12, 82, 71, 1, 0], ![70, 20, 58, 0, 1]] where
  M :=![![![53275, -7527, -21781, -9490, -4590], ![110160, -15575, -45020, -19596, -9490], ![227760, -32190, -93079, -40512, -19596], ![-35496, 5065, 14451, 6221, 3046], ![48168, -6801, -19713, -8634, -4237]]]
  hmulB := by decide  
  f := ![![![161753, -175969, 39291, -31466, 14564]], ![![-349536, 380213, -84886, 67992, -31466]], ![![755184, -821526, 183427, -146904, 67992]], ![![316236, -344047, 76824, -61519, 28476]], ![![582442, -633621, 141475, -113302, 52441]]]
  g := ![![![5885, 10391, 11063, -9490, -4590], ![12164, 21459, 22852, -19596, -9490], ![25128, 44358, 47227, -40512, -19596], ![-3896, -6819, -7276, 6221, 3046], ![5402, 9469, 10109, -8634, -4237]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [44, 55, 19, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 34, 60], [61, 48, 23], [0, 1]]
 g := ![![[32, 67, 69], [5, 17, 63], [21, 37], [31, 1], [57, 64, 1], []], ![[58, 61, 16, 54], [79, 60, 81, 79], [36, 26], [23, 11], [68, 69, 80, 45], [5, 31]], ![[38, 32, 73, 30], [54, 35, 50, 3], [17, 77], [30, 37], [75, 19, 30, 28], [42, 31]]]
 h' := ![![[3, 34, 60], [29, 63, 61], [16, 4, 48], [39, 7, 28], [65, 25, 1], [0, 0, 1], [0, 1]], ![[61, 48, 23], [46, 14, 68], [26, 63, 54], [45, 64, 21], [12, 79, 54], [38, 59, 48], [3, 34, 60]], ![[0, 1], [16, 6, 37], [26, 16, 64], [39, 12, 34], [60, 62, 28], [47, 24, 34], [61, 48, 23]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58, 7], []]
 b := ![[], [35, 26, 40], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [44, 55, 19, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1078708, 329884, 101694, -449358, -374336]
  a := ![0, 0, -6, -10, -4]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![367676, 538120, 647200, -449358, -374336]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 571787 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-161753, 175969, -39291, 31466, -14564]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-161753, 175969, -39291, 31466, -14564]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![2, 75, 1, 0, 0], ![57, 49, 0, 1, 0], ![75, 7, 0, 0, 1]] where
  M :=![![![-161753, 175969, -39291, 31466, -14564], ![349536, -380213, 84886, -67992, 31466], ![-755184, 821526, -183427, 146904, -67992], ![649560, -706607, 157765, -126355, 58480], ![-210024, 228465, -51009, 40854, -18907]]]
  hmulB := by decide  
  f := ![![![-53275, 7527, 21781, 9490, 4590]], ![![-110160, 15575, 45020, 19596, 9490]], ![![-103570, 14643, 42327, 18424, 8922]], ![![-101193, 14303, 41362, 18011, 8718]], ![![-58011, 8197, 23716, 10332, 4999]]]
  g := ![![![-9451, 20276, -39291, 31466, -14564], ![20426, -43799, 84886, -67992, 31466], ![-44126, 94653, -183427, 146904, -67992], ![37955, -81409, 157765, -126355, 58480], ![-12273, 26321, -51009, 40854, -18907]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P1 : CertificateIrreducibleZModOfList' 83 2 2 6 [62, 36, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [47, 82], [0, 1]]
 g := ![![[22, 28], [54, 77], [63], [70], [55, 51], [1]], ![[10, 55], [21, 6], [63], [70], [45, 32], [1]]]
 h' := ![![[47, 82], [55, 32], [39, 49], [25, 48], [76, 30], [21, 47], [0, 1]], ![[0, 1], [65, 51], [18, 34], [40, 35], [75, 53], [72, 36], [47, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [44, 67]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N1 : CertifiedPrimeIdeal' SI83N1 83 where
  n := 2
  hpos := by decide
  P := [62, 36, 1]
  hirr := P83P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4653, 5583, -3074, -7208, 1545]
  a := ![13, -1, -2, 1, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3572, 6970, -3074, -7208, 1545]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N1 B_one_repr
lemma NI83N1 : Nat.card (O ⧸ I83N1) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![53275, -7527, -21781, -9490, -4590]] ![![-161753, 175969, -39291, 31466, -14564]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-35531, -1335, 9039, 3335, 2187]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![-35531, -1335, 9039, 3335, 2187]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![76, 26, 42, 1, 0], ![33, 10, 17, 0, 1]] where
  M :=![![![-35531, -1335, 9039, 3335, 2187], ![-52488, -2726, 13699, 4863, 3335], ![-80040, -2463, 20168, 7575, 4863], ![20568, 49, -4915, -1996, -1169], ![9720, 717, -2601, -873, -640]]]
  hmulB := by decide  
  f := ![![![53, -85, 55, 109, -43]], ![![1032, -592, 143, 777, 109]], ![![-2616, 2667, -1376, -3435, 777]], ![![-908, 1015, -555, -1304, 351]], ![![-195, 265, -160, -339, 118]]]
  g := ![![![-4058, -1235, -1890, 3335, 2187], ![-5979, -1826, -2778, 4863, 3335], ![-9171, -2787, -4277, 7575, 4863], ![2369, 715, 1110, -1996, -1169], ![1092, 335, 505, -873, -640]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [9, 4, 78, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 2, 35], [87, 86, 54], [0, 1]]
 g := ![![[48, 68, 45], [41, 81], [12, 42], [34, 62, 55], [28, 11, 1], []], ![[46, 41, 9, 13], [51, 71], [32, 21], [4, 75, 10, 77], [86, 39, 54, 48], [87, 68]], ![[80, 8, 64, 52], [41, 87], [73, 81], [86, 22, 32, 14], [50, 43, 22, 38], [68, 68]]]
 h' := ![![[13, 2, 35], [19, 47, 57], [78, 22, 9], [50, 65, 65], [15, 56, 77], [0, 0, 1], [0, 1]], ![[87, 86, 54], [75, 47, 50], [0, 60, 31], [56, 28, 33], [12, 61, 38], [9, 71, 86], [13, 2, 35]], ![[0, 1], [68, 84, 71], [80, 7, 49], [5, 85, 80], [79, 61, 63], [15, 18, 2], [87, 86, 54]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30, 4], []]
 b := ![[], [82, 57, 66], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [9, 4, 78, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-161294, 132155, -58285, -179234, 19975]
  a := ![-1, -3, 1, -1, 2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![143835, 51601, 80112, -179234, 19975]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 704969 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-53, 85, -55, -109, 43]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![-53, 85, -55, -109, 43]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![5, 18, 1, 0, 0], ![27, 12, 0, 1, 0], ![26, 43, 0, 0, 1]] where
  M :=![![![-53, 85, -55, -109, 43], ![-1032, 592, -143, -777, -109], ![2616, -2667, 1376, 3435, -777], ![1800, -173, -499, 272, 961], ![-15048, 13029, -5907, -16857, 2378]]]
  hmulB := by decide  
  f := ![![![35531, 1335, -9039, -3335, -2187]], ![![52488, 2726, -13699, -4863, -3335]], ![![13511, 654, -3505, -1256, -852]], ![![17625, 772, -4534, -1645, -1100]], ![![35630, 1699, -9230, -3314, -2243]]]
  g := ![![![23, 6, -55, -109, 43], ![264, 193, -143, -777, -109], ![-863, -396, 1376, 3435, -777], ![-315, -402, -499, 272, 961], ![4582, 2465, -5907, -16857, 2378]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P1 : CertificateIrreducibleZModOfList' 89 2 2 6 [87, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [63, 88], [0, 1]]
 g := ![![[76, 44], [25], [57], [45, 78], [31, 53], [1]], ![[0, 45], [25], [57], [64, 11], [77, 36], [1]]]
 h' := ![![[63, 88], [14, 69], [26, 84], [1, 71], [62, 16], [2, 63], [0, 1]], ![[0, 1], [0, 20], [67, 5], [24, 18], [2, 73], [55, 26], [63, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [20, 70]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N1 : CertifiedPrimeIdeal' SI89N1 89 where
  n := 2
  hpos := by decide
  P := [87, 26, 1]
  hirr := P89P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1674, 1127, -218, -1824, 167]
  a := ![3, 0, 3, -4, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![498, 222, -218, -1824, 167]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N1 B_one_repr
lemma NI89N1 : Nat.card (O ⧸ I89N1) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![-35531, -1335, 9039, 3335, 2187]] ![![-53, 85, -55, -109, 43]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![117107, -127585, 28561, -22788, 10576]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![117107, -127585, 28561, -22788, 10576]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![76, 48, 80, 1, 0], ![26, 72, 54, 0, 1]] where
  M :=![![![117107, -127585, 28561, -22788, 10576], ![-253824, 275747, -61418, 49362, -22788], ![546912, -595644, 133283, -106410, 49362], ![-470904, 512379, -114447, 91607, -42416], ![152184, -165651, 37037, -29604, 13721]]]
  hmulB := by decide  
  f := ![![![-277, 175, -53, -228, -10]], ![![240, -427, 284, 546, -228]], ![![5472, -3180, 791, 4170, 546]], ![![4364, -2657, 735, 3479, 334]], ![![2950, -1939, 621, 2532, 99]]]
  g := ![![![16227, 2111, 13201, -22788, 10576], ![-35184, -4669, -28658, 49362, -22788], ![75780, 9876, 61655, -106410, 49362], ![-65260, -8565, -53119, 91607, -42416], ![21086, 2757, 17159, -29604, 13721]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [83, 92, 94, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [57, 56, 64], [43, 40, 33], [0, 1]]
 g := ![![[11, 70, 94], [2, 8], [34, 11], [2, 89], [57, 9], [1]], ![[14, 76, 80, 75], [70, 2], [45, 33], [21, 18], [23, 85], [25, 63, 63, 50]], ![[71, 19, 54, 62], [19, 18], [74, 18], [72, 64], [90, 18], [87, 66, 65, 47]]]
 h' := ![![[57, 56, 64], [31, 19, 71], [87, 10, 28], [22, 59, 37], [24, 66, 34], [14, 5, 3], [0, 1]], ![[43, 40, 33], [46, 18, 79], [91, 30, 14], [25, 47, 18], [64, 87, 55], [79, 50, 52], [57, 56, 64]], ![[0, 1], [64, 60, 44], [63, 57, 55], [26, 88, 42], [52, 41, 8], [21, 42, 42], [43, 40, 33]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35, 21], []]
 b := ![[], [92, 59, 80], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [83, 92, 94, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1868610, 1477517, -609323, -1916202, 176921]
  a := ![1, 1, 1, -1, 4]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1434668, 832133, 1475599, -1916202, 176921]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 912673 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-113233, -4979, 29053, 10542, 7052]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![-113233, -4979, 29053, 10542, 7052]] 
 ![![97, 0, 0, 0, 0], ![19, 1, 0, 0, 0], ![27, 0, 1, 0, 0], ![95, 0, 0, 1, 0], ![59, 0, 0, 0, 1]] where
  M :=![![![-113233, -4979, 29053, 10542, 7052], ![-169248, -7453, 43430, 15756, 10542], ![-253008, -11118, 64913, 23556, 15756], ![63480, 2781, -16283, -5911, -3952], ![32280, 1425, -8285, -3006, -2011]]]
  hmulB := by decide  
  f := ![![![62015, -8767, -25337, -11022, -5342]], ![![13469, -1904, -5503, -2394, -1160]], ![![19989, -2823, -8170, -3558, -1722]], ![![60313, -8528, -24640, -10717, -5196]], ![![38317, -5426, -15644, -6792, -3299]]]
  g := ![![![-22893, -4979, 29053, 10542, 7052], ![-34217, -7453, 43430, 15756, 10542], ![-51153, -11118, 64913, 23556, 15756], ![12835, 2781, -16283, -5911, -3952], ![6527, 1425, -8285, -3006, -2011]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1

def I97N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2285, 100, -586, -212, -142]] i)))

def SI97N2: IdealEqSpanCertificate' Table ![![2285, 100, -586, -212, -142]] 
 ![![97, 0, 0, 0, 0], ![86, 1, 0, 0, 0], ![73, 0, 1, 0, 0], ![65, 0, 0, 1, 0], ![13, 0, 0, 0, 1]] where
  M :=![![![2285, 100, -586, -212, -142], ![3408, 155, -878, -324, -212], ![5088, 228, -1307, -480, -324], ![-1248, -76, 334, 145, 82], ![-624, -18, 148, 48, 67]]]
  hmulB := by decide  
  f := ![![![-78235, 10792, 32154, 13924, 6786]], ![![-71042, 9811, 29190, 12644, 6160]], ![![-62323, 8596, 25615, 11092, 5406]], ![![-51899, 7168, 21324, 9237, 4500]], ![![-11215, 1546, 4610, 1996, 973]]]
  g := ![![![537, 100, -586, -212, -142], ![804, 155, -878, -324, -212], ![1199, 228, -1307, -480, -324], ![-305, -76, 334, 145, 82], ![-143, -18, 148, 48, 67]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N2 : Nat.card (O ⧸ I97N2) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N2)

lemma isPrimeI97N2 : Ideal.IsPrime I97N2 := prime_ideal_of_norm_prime hp97.out _ NI97N2
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![117107, -127585, 28561, -22788, 10576]] ![![-113233, -4979, 29053, 10542, 7052]]
  ![![1778701, 1971426, -1291842, 4062, -365550]] where
 M := ![![![1778701, 1971426, -1291842, 4062, -365550]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI97N1 : IdealMulLeCertificate' Table 
  ![![1778701, 1971426, -1291842, 4062, -365550]] ![![2285, 100, -586, -212, -142]]
  ![![97, 0, 0, 0, 0]] where
 M := ![![![4433093321, 195172342, -1137538012, -412699886, -276119812]]]
 hmul := by decide  
 g := ![![![![45701993, 2012086, -11727196, -4254638, -2846596]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-227, 183, -71, -223, 45]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![-227, 183, -71, -223, 45]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![62, 66, 3, 1, 0], ![80, 82, 29, 0, 1]] where
  M :=![![![-227, 183, -71, -223, 45], ![-1080, 448, 13, -567, -223], ![5352, -4425, 1946, 5793, -567], ![-408, 1687, -1325, -2146, 1249], ![-25848, 18963, -7167, -24639, 1034]]]
  hmulB := by decide  
  f := ![![![4265, -1867, -187, -581, 11]], ![![-264, 4430, -1891, 423, -581]], ![![13944, -8979, 658, -2157, 423]], ![![2774, 1560, -1345, -129, -366]], ![![7184, -486, -1487, -740, -339]]]
  g := ![![![99, 111, -7, -223, 45], ![514, 556, 81, -567, -223], ![-3054, -3369, 10, 5793, -567], ![324, 405, -308, -2146, 1249], ![14050, 15449, 364, -24639, 1034]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [1, 54, 8, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [45, 14, 3], [48, 86, 98], [0, 1]]
 g := ![![[56, 87, 36], [6, 82], [90, 84, 21], [80, 49], [49, 64], [1]], ![[69, 97, 44, 99], [49, 95], [46, 66, 44, 62], [77, 19], [7, 47], [75, 23, 61, 27]], ![[7, 1, 46, 62], [48, 6], [89, 21, 81, 2], [47, 14], [20, 76], [72, 19, 13, 74]]]
 h' := ![![[45, 14, 3], [14, 95, 95], [11, 9, 48], [2, 94, 83], [53, 24, 94], [100, 47, 93], [0, 1]], ![[48, 86, 98], [89, 35, 72], [80, 83, 14], [15, 57, 47], [71, 54, 76], [49, 76, 59], [45, 14, 3]], ![[0, 1], [49, 72, 35], [81, 9, 39], [29, 51, 72], [50, 23, 32], [26, 79, 50], [48, 86, 98]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [80, 83], []]
 b := ![[], [97, 29, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [1, 54, 8, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1129, -622, 268, 897, -94]
  a := ![4, 0, 0, 1, 0]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-465, -516, 3, 897, -94]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 1030301 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4265, 1867, 187, 581, -11]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![-4265, 1867, 187, 581, -11]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![46, 86, 1, 0, 0], ![92, 45, 0, 1, 0], ![70, 79, 0, 0, 1]] where
  M :=![![![-4265, 1867, 187, 581, -11], ![264, -4430, 1891, -423, 581], ![-13944, 8979, -658, 2157, -423], ![8664, -7871, 1419, -1546, 571], ![-1656, 2595, -753, 393, -256]]]
  hmulB := by decide  
  f := ![![![227, -183, 71, 223, -45]], ![![1080, -448, -13, 567, 223]], ![![970, -421, 2, 527, 175]], ![![692, -383, 72, 477, 46]], ![![1258, -665, 110, 842, 133]]]
  g := ![![![-649, -391, 187, 581, -11], ![-876, -1920, 1891, -423, 581], ![-1510, 19, -658, 2157, -423], ![452, -1044, 1419, -1546, 571], ![146, 692, -753, 393, -256]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P1 : CertificateIrreducibleZModOfList' 101 2 2 6 [54, 44, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [57, 100], [0, 1]]
 g := ![![[27, 58], [76], [78, 88], [24], [56], [57, 1]], ![[0, 43], [76], [44, 13], [24], [56], [13, 100]]]
 h' := ![![[57, 100], [28, 19], [30, 51], [85, 47], [88, 78], [53, 64], [0, 1]], ![[0, 1], [0, 82], [8, 50], [37, 54], [90, 23], [65, 37], [57, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66]]
 b := ![[], [19, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N1 : CertifiedPrimeIdeal' SI101N1 101 where
  n := 2
  hpos := by decide
  P := [54, 44, 1]
  hirr := P101P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-60861, 56351, -26651, -73716, 18751]
  a := ![7, 2, -24, 0, -23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![65687, 41428, -26651, -73716, 18751]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N1 B_one_repr
lemma NI101N1 : Nat.card (O ⧸ I101N1) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![-227, 183, -71, -223, 45]] ![![-4265, 1867, 187, 581, -11]]
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


def P103P0 : CertificateIrreducibleZModOfList' 103 5 2 6 [73, 36, 84, 5, 2, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [32, 47, 30, 90, 97], [75, 6, 33, 76, 94], [24, 7, 94, 52, 47], [73, 42, 49, 91, 71], [0, 1]]
 g := ![![[56, 73, 93, 61, 41], [94, 3, 57, 3, 100], [78, 28, 10, 6, 8], [1, 74, 43, 1], [101, 1], []], ![[59, 101, 11, 83, 75, 23, 61, 56], [2, 1, 33, 50, 5, 3, 72, 59], [77, 49, 16, 8, 20, 1, 9, 92], [16, 93, 35, 23], [19, 7, 60, 23], [61, 36, 74, 21, 4, 29, 58, 93]], ![[3, 18, 76, 66, 80, 1, 33, 27], [52, 73, 77, 89, 42, 99, 37, 85], [11, 0, 55, 54, 93, 89, 73, 62], [43, 85, 37, 100], [96, 24, 21, 59], [78, 64, 78, 49, 99, 24, 47, 95]], ![[17, 89, 74, 10, 3, 44], [87, 81, 84, 66, 73, 51, 30, 43], [68, 20, 36, 19, 74, 79, 52, 73], [39, 42, 86, 4], [63, 3, 2, 33], [97, 36, 52, 97, 15, 21, 71, 102]], ![[30, 25, 83, 61, 58, 37, 89, 22], [100, 84, 68, 51, 75, 68, 5, 71], [43, 97, 11, 86, 90, 30, 31, 88], [64, 14, 44, 14], [62, 22, 17, 25], [41, 0, 20, 10, 21, 17, 38, 89]]]
 h' := ![![[32, 47, 30, 90, 97], [39, 19, 15, 36, 12], [74, 99, 99, 5, 10], [25, 38, 7, 53, 76], [43, 102, 29, 29, 102], [0, 0, 0, 1], [0, 1]], ![[75, 6, 33, 76, 94], [64, 42, 80, 101, 98], [61, 63, 92, 13, 73], [94, 89, 36, 94, 88], [52, 38, 71, 70, 69], [93, 98, 88, 56, 69], [32, 47, 30, 90, 97]], ![[24, 7, 94, 52, 47], [60, 11, 32, 24, 10], [86, 9, 95, 18, 65], [32, 42, 76, 96, 99], [9, 84, 70, 17, 10], [61, 40, 96, 65, 70], [75, 6, 33, 76, 94]], ![[73, 42, 49, 91, 71], [21, 40, 12, 6], [27, 8, 95, 79, 59], [54, 96, 16, 16, 12], [74, 74, 17, 75, 2], [48, 2, 74, 67, 62], [24, 7, 94, 52, 47]], ![[0, 1], [37, 94, 67, 39, 86], [24, 27, 31, 91, 102], [102, 44, 71, 50, 34], [97, 11, 19, 15, 23], [83, 66, 51, 17, 5], [73, 42, 49, 91, 71]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77, 4, 82, 1], [], [], []]
 b := ![[], [69, 69, 54, 68, 86], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 5
  hpos := by decide
  P := [73, 36, 84, 5, 2, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4212453927129, -2214407468714, 406637754698, 2914501066374, 621881828362]
  a := ![1, 3, -8, -1, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![40897610943, -21499101638, 3947939366, 28296126858, 6037687654]
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



lemma PB1906I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB1906I2 : PrimesBelowBoundCertificateInterval O 61 103 1906 where
  m := 9
  g := ![3, 2, 1, 3, 2, 2, 3, 2, 1]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB1906I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0, I67N1, I67N2]
    · exact ![I71N0, I71N1]
    · exact ![I73N0]
    · exact ![I79N0, I79N1, I79N2]
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1, I97N2]
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
    · exact ![4489, 4489, 67]
    · exact ![25411681, 71]
    · exact ![2073071593]
    · exact ![493039, 79, 79]
    · exact ![571787, 6889]
    · exact ![704969, 7921]
    · exact ![912673, 97, 97]
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
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
      exact NI97N2
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
  β := ![I67N2, I71N1, I79N1, I79N2, I97N1, I97N2]
  Il := ![[I67N2], [I71N1], [], [I79N1, I79N2], [], [], [I97N1, I97N2], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
