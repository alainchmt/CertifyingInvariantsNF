
import IdealArithmetic.Examples.NF5_3_2025000000_6.RI5_3_2025000000_6
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1559, 1841, -344, -1239, 4870]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![1559, 1841, -344, -1239, 4870]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![0, 0, 67, 0, 0], ![8, 41, 58, 1, 0], ![44, 17, 5, 0, 1]] where
  M :=![![![1559, 1841, -344, -1239, 4870], ![-17588, -7955, 1118, 4456, -16894], ![47116, 49526, -9079, -32904, 129036], ![-459384, -221240, 32102, 126389, -481224], ![-98930, -44801, 6300, 25105, -95189]]]
  hmulB := by decide  
  f := ![![![-359, -97, 44, 63, -260]], ![![1216, -531, 14, 134, -502]], ![![1260, 3554, -601, -1172, 4544]], ![![1568, 2575, -458, -841, 3254]], ![![106, 32, -1, 7, -37]]]
  g := ![![![-3027, -450, 704, -1239, 4870], ![10300, 1441, -2580, 4456, -16894], ![-80108, -11866, 18719, -32904, 129036], ![294080, 41457, -73020, 126389, -481224], ![58038, 8121, -14535, 25105, -95189]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [15, 23, 65, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 22, 59], [61, 44, 8], [0, 1]]
 g := ![![[62, 28, 9], [42, 15, 65], [57, 22], [25, 26], [2, 1], []], ![[40, 63, 63, 10], [43, 63, 5, 49], [18, 22], [23, 35], [2, 60], [44, 64]], ![[5, 32, 53, 63], [38, 30, 4, 58], [], [64, 19], [22, 15], [28, 64]]]
 h' := ![![[8, 22, 59], [40, 24, 3], [3, 39, 20], [56, 15, 25], [37, 6, 48], [0, 0, 1], [0, 1]], ![[61, 44, 8], [52, 23, 7], [53, 15, 32], [16, 30, 42], [19, 25, 54], [7, 55, 44], [8, 22, 59]], ![[0, 1], [17, 20, 57], [62, 13, 15], [14, 22], [61, 36, 32], [18, 12, 22], [61, 44, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66, 16], []]
 b := ![[], [2, 43, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [15, 23, 65, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5645054969, -2312699646, 513651495, 1901556015, -7983001053]
  a := ![220, -541, 57, 274, -1115]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![5099770943, 827380920, -1042710330, 1901556015, -7983001053]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 300763 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![359, 97, -44, -63, 260]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![359, 97, -44, -63, 260]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![5, 9, 1, 0, 0], ![22, 58, 0, 1, 0], ![14, 26, 0, 0, 1]] where
  M :=![![![359, 97, -44, -63, 260], ![-1216, 531, -14, -134, 502], ![-1260, -3554, 601, 1172, -4544], ![15008, 11060, -3246, -5631, 22872], ![4074, 2331, -764, -1279, 5225]]]
  hmulB := by decide  
  f := ![![![-1559, -1841, 344, 1239, -4870]], ![![17588, 7955, -1118, -4456, 16894]], ![![1543, 192, 11, -15, -20]], ![![21570, 9584, -1334, -5337, 20208]], ![![7976, 3371, -456, -1845, 6959]]]
  g := ![![![-25, -39, -44, -63, 260], ![-78, -69, -14, -134, 502], ![501, 615, 601, 1172, -4544], ![-2464, -3400, -3246, -5631, 22872], ![-554, -783, -764, -1279, 5225]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P1 : CertificateIrreducibleZModOfList' 67 2 2 6 [9, 39, 1] where
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
 g := ![![[49, 15], [6, 62], [25], [64], [47], [1]], ![[0, 52], [0, 5], [25], [64], [47], [1]]]
 h' := ![![[28, 66], [13, 45], [57, 53], [9, 5], [60, 8], [58, 28], [0, 1]], ![[0, 1], [0, 22], [0, 14], [15, 62], [16, 59], [38, 39], [28, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [33, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N1 : CertifiedPrimeIdeal' SI67N1 67 where
  n := 2
  hpos := by decide
  P := [9, 39, 1]
  hirr := P67P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2511597, 2347414, -449317, -1776723, 7320172]
  a := ![-351, 800, -91, -439, 1779]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-950142, -1207213, -449317, -1776723, 7320172]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N1 B_one_repr
lemma NI67N1 : Nat.card (O ⧸ I67N1) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![1559, 1841, -344, -1239, 4870]] ![![359, 97, -44, -63, 260]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1101, 265, -75, -258, 1098]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-1101, 265, -75, -258, 1098]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![0, 0, 0, 71, 0], ![57, 36, 30, 18, 1]] where
  M :=![![![-1101, 265, -75, -258, 1098], ![-5844, 1365, -389, -1341, 5712], ![-30504, 7236, -2064, -7103, 30234], ![-161020, 37650, -10799, -37052, 157802], ![-40562, 9497, -2724, -9345, 39797]]]
  hmulB := by decide  
  f := ![![![1, -5, 1, 2, -8]], ![![32, 9, -3, -3, 12]], ![![-48, 20, 6, 3, -18]], ![![204, -354, 59, 162, -642]], ![![49, -82, 17, 43, -173]]]
  g := ![![![-897, -553, -465, -282, 1098], ![-4668, -2877, -2419, -1467, 5712], ![-24702, -15228, -12804, -7765, 30234], ![-128954, -79482, -66829, -40528, 157802], ![-32521, -20045, -16854, -10221, 39797]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 4 2 6 [55, 42, 65, 6, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [67, 0, 5, 51], [4, 26, 8, 40], [65, 44, 58, 51], [0, 1]]
 g := ![![[53, 40, 2, 30], [29, 41, 38, 37], [7, 1, 0, 57], [70, 67, 36], [1], []], ![[63, 42, 40, 32, 17, 23], [17, 0, 44, 22], [63, 19, 15, 56, 14, 21], [18, 8, 9], [6, 30, 32], [62, 27, 45]], ![[44, 65, 26, 39, 37, 20], [46, 63, 14, 47, 33, 27], [52, 68, 34, 12, 11, 27], [37, 67, 30], [41, 53, 50], [42, 57, 38]], ![[49, 48, 49, 1, 7, 52], [30, 46, 50, 24, 18, 14], [1, 35, 69, 20, 25, 35], [55, 25, 60], [62, 43, 2], [19, 37, 45]]]
 h' := ![![[67, 0, 5, 51], [38, 54, 45, 32], [41, 25, 5, 26], [27, 54, 67, 46], [16, 29, 6, 65], [0, 0, 1], [0, 1]], ![[4, 26, 8, 40], [40, 47, 15, 51], [49, 37, 52], [68, 37, 20, 40], [8, 46, 34, 3], [14, 29, 60, 48], [67, 0, 5, 51]], ![[65, 44, 58, 51], [0, 32, 62, 6], [61, 17, 39, 52], [40, 37, 52, 52], [4, 56, 56, 32], [49, 66, 58, 11], [4, 26, 8, 40]], ![[0, 1], [6, 9, 20, 53], [47, 63, 46, 64], [57, 14, 3, 4], [10, 11, 46, 42], [56, 47, 23, 12], [65, 44, 58, 51]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [47, 9, 4], []]
 b := ![[], [], [64, 30, 67, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 4
  hpos := by decide
  P := [55, 42, 65, 6, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3011389039, 784050670, -196644370, -718929628, 3066550518]
  a := ![15, -39, 4, 18, -76]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2504292515, -1543827718, -1298495210, -787561112, 3066550518]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 25411681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -5, 1, 2, -8]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![1, -5, 1, 2, -8]] 
 ![![71, 0, 0, 0, 0], ![27, 1, 0, 0, 0], ![52, 0, 1, 0, 0], ![16, 0, 0, 1, 0], ![29, 0, 0, 0, 1]] where
  M :=![![![1, -5, 1, 2, -8], ![32, 9, -3, -3, 12], ![-48, 20, 6, 3, -18], ![204, -354, 59, 162, -642], ![38, -89, 16, 41, -163]]]
  hmulB := by decide  
  f := ![![![-1101, 265, -75, -258, 1098]], ![![-501, 120, -34, -117, 498]], ![![-1236, 296, -84, -289, 1230]], ![![-2516, 590, -169, -580, 2470]], ![![-1021, 242, -69, -237, 1009]]]
  g := ![![![4, -5, 1, 2, -8], ![-5, 9, -3, -3, 12], ![-6, 20, 6, 3, -18], ![320, -354, 59, 162, -642], ![80, -89, 16, 41, -163]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-1101, 265, -75, -258, 1098]] ![![1, -5, 1, 2, -8]]
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


def P73P0 : CertificateIrreducibleZModOfList' 73 5 2 6 [33, 20, 25, 51, 7, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 12, 7, 71, 23], [0, 70, 9, 60, 68], [49, 56, 64, 62, 39], [66, 7, 66, 26, 16], [0, 1]]
 g := ![![[59, 33, 8, 21, 48], [70, 3, 66, 46], [55, 31, 46, 4], [25, 54, 71, 66, 1], [], []], ![[51, 70, 48, 43, 63, 17, 15, 49], [19, 39, 36, 4], [60, 29, 22, 6], [72, 60, 68, 43, 61, 54], [26, 14, 35, 25], [55, 58, 1, 18]], ![[14, 36, 70, 63, 56, 22, 65, 68], [34, 11, 46, 27], [54, 47, 61, 12], [45, 72, 16, 23, 29, 19, 22, 39], [49, 19, 19, 46], [41, 68, 28, 25]], ![[64, 60, 58, 22, 17, 43, 11, 44], [36, 49, 40, 71], [9, 68, 55, 54], [36, 41, 54, 37, 67, 4, 35, 59], [22, 1, 6, 8], [65, 47, 29, 61]], ![[32, 39, 47, 26, 70, 40, 34, 32], [23, 64, 39, 12], [2, 63, 55, 72], [40, 61, 29, 36, 23, 38, 19, 2], [30, 71, 30, 32], [23, 29, 62, 37]]]
 h' := ![![[24, 12, 7, 71, 23], [23, 65, 10, 7, 62], [56, 27, 52, 42, 22], [51, 54, 40, 55, 2], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[0, 70, 9, 60, 68], [39, 49, 45, 15, 23], [3, 67, 68, 57, 71], [42, 23, 34, 66, 58], [22, 70, 40, 19], [2, 44, 29, 21, 5], [24, 12, 7, 71, 23]], ![[49, 56, 64, 62, 39], [21, 65, 19, 70, 72], [11, 57, 4, 30, 10], [48, 28, 4, 20, 31], [50, 62, 37, 48, 67], [34, 2, 58, 26, 22], [0, 70, 9, 60, 68]], ![[66, 7, 66, 26, 16], [57, 18, 45, 11, 21], [71, 50, 51, 68, 12], [21, 45, 27, 69, 28], [59, 47, 16, 56, 70], [37, 9, 46, 29, 64], [49, 56, 64, 62, 39]], ![[0, 1], [69, 22, 27, 43, 41], [68, 18, 44, 22, 31], [34, 69, 41, 9, 27], [67, 40, 53, 23, 8], [20, 18, 12, 70, 55], [66, 7, 66, 26, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50, 33, 20, 10], [], [], []]
 b := ![[], [56, 12, 11, 38, 44], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 5
  hpos := by decide
  P := [33, 20, 25, 51, 7, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-330046263419298871, 132622037226235298, -32018899308685132, -114018477422623174, 476689953354253410]
  a := ![-381, 955, -99, -477, 1931]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4521181690675327, 1816740235975826, -438615059023084, -1561896950994838, 6529999361017170]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![889705, -205550, 60219, 204695, -871230]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![889705, -205550, 60219, 204695, -871230]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![0, 0, 0, 79, 0], ![4, 61, 12, 26, 1]] where
  M :=![![![889705, -205550, 60219, 204695, -871230], ![4638820, -1071365, 313845, 1066979, -4541330], ![24180428, -5584206, 1636098, 5562065, -23673666], ![126053596, -29117830, 8530295, 28997930, -123422270], ![31738824, -7331492, 2147836, 7301356, -31076363]]]
  hmulB := by decide  
  f := ![![![-32305, 5710, -2325, -6911, 29290]], ![![-153372, 27289, -11077, -32945, 139594]], ![![-730284, 128990, -52540, -156165, 661870]], ![![-3466100, 617186, -250435, -744880, 3156110]], ![![-1382640, 246019, -99861, -297003, 1258455]]]
  g := ![![![55375, 670120, 133101, 289325, -871230], ![288660, 3493035, 693795, 1508121, -4541330], ![1504748, 18208980, 3616710, 7861739, -23673666], ![7844844, 94932160, 18855665, 40987050, -123422270], ![1975244, 23902869, 4747648, 10320086, -31076363]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 4 2 6 [17, 39, 69, 78, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 73, 53, 51], [57, 52, 5, 21], [72, 32, 21, 7], [0, 1]]
 g := ![![[54, 54, 30, 20], [56, 67, 69, 11], [29, 41, 21, 13], [42, 53, 21, 1], [1], []], ![[3, 21, 36, 16, 55, 20], [70, 48, 32, 32, 43, 26], [29, 27, 75, 71, 61, 21], [48, 19, 45, 33, 8, 31], [32, 30, 76], [32, 28, 73]], ![[42, 67, 44, 21, 57, 73], [44, 1, 58, 47, 61, 16], [69, 42, 71, 74, 57, 9], [70, 42, 14, 50, 65, 19], [4, 21, 13], [2, 19, 46]], ![[7, 73, 66, 34, 68, 57], [46, 8, 65, 10, 67, 74], [62, 65, 64, 10, 49, 61], [40, 29, 38, 10, 4, 78], [45, 24, 19], [63, 27, 49]]]
 h' := ![![[30, 73, 53, 51], [75, 40, 10, 40], [60, 77, 63, 13], [76, 41, 33, 48], [62, 40, 10, 1], [0, 0, 1], [0, 1]], ![[57, 52, 5, 21], [29, 21, 64, 15], [14, 68, 9, 4], [3, 6, 68, 16], [29, 29, 40, 48], [40, 49, 18, 47], [30, 73, 53, 51]], ![[72, 32, 21, 7], [54, 11, 44, 13], [69, 18, 19, 47], [1, 76, 63, 55], [34, 26, 32, 49], [55, 76, 33, 48], [57, 52, 5, 21]], ![[0, 1], [33, 7, 40, 11], [63, 74, 67, 15], [69, 35, 73, 39], [50, 63, 76, 60], [5, 33, 27, 63], [72, 32, 21, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [1, 73, 75], []]
 b := ![[], [], [51, 22, 52, 19], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 4
  hpos := by decide
  P := [17, 39, 69, 78, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-138607687686436, 77764857798464, -17306198231687, -63216439059668, 261816779973097]
  a := ![469, -1152, 123, 588, -2377]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-15011073513656, -201177958488107, -39988703264669, -86967755928610, 261816779973097]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 38950081 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![32305, -5710, 2325, 6911, -29290]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![32305, -5710, 2325, 6911, -29290]] 
 ![![79, 0, 0, 0, 0], ![65, 1, 0, 0, 0], ![41, 0, 1, 0, 0], ![21, 0, 0, 1, 0], ![76, 0, 0, 0, 1]] where
  M :=![![![32305, -5710, 2325, 6911, -29290], ![153372, -27289, 11077, 32945, -139594], ![730284, -128990, 52540, 156165, -661870], ![3466100, -617186, 250435, 744880, -3156110], ![861640, -153316, 62232, 185088, -784251]]]
  hmulB := by decide  
  f := ![![![-889705, 205550, -60219, -204695, 871230]], ![![-790755, 182685, -53520, -181926, 774320]], ![![-767827, 177364, -51963, -176640, 751824]], ![![-1832119, 423220, -123986, -421475, 1793900]], ![![-1257676, 290548, -85120, -289344, 1231517]]]
  g := ![![![30241, -5710, 2325, 6911, -29290], ![144181, -27289, 11077, 32945, -139594], ![683331, -128990, 52540, 156165, -661870], ![3259965, -617186, 250435, 744880, -3156110], ![810024, -153316, 62232, 185088, -784251]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![889705, -205550, 60219, 204695, -871230]] ![![32305, -5710, 2325, 6911, -29290]]
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

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25, -27, 5, 20, -80]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![25, -27, 5, 20, -80]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![53, 12, 58, 1, 0], ![70, 77, 30, 0, 1]] where
  M :=![![![25, -27, 5, 20, -80], ![320, 105, -7, -35, 120], ![-40, -880, 190, 603, -2410], ![9596, 2478, -289, -1070, 3838], ![2202, 469, -48, -181, 625]]]
  hmulB := by decide  
  f := ![![![783, -181, 53, 180, -766]], ![![4076, -935, 275, 935, -3980]], ![![21200, -4904, 1440, 4885, -20790]], ![![17237, -3985, 1170, 3970, -16896]], ![![12440, -2870, 843, 2862, -12181]]]
  g := ![![![55, 71, 15, 20, -80], ![-75, -105, -19, -35, 120], ![1647, 2138, 452, 603, -2410], ![-2438, -3376, -643, -1070, 3838], ![-385, -548, -100, -181, 625]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [52, 0, 18, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [60, 55, 67], [5, 27, 16], [0, 1]]
 g := ![![[18, 41, 75], [14, 49, 49], [], [35, 81], [75, 65, 1], []], ![[37, 65, 73, 47], [32, 77, 58, 53], [78, 49], [1, 21], [45, 46, 9, 39], [23, 7]], ![[75, 19, 31, 25], [55, 18, 24, 30], [20, 49], [76, 10], [17, 63, 33, 11], [74, 7]]]
 h' := ![![[60, 55, 67], [19, 19, 65], [49, 25, 7], [7, 67], [1, 23, 9], [0, 0, 1], [0, 1]], ![[5, 27, 16], [51, 17, 40], [34, 41, 38], [43, 33, 7], [26, 36, 41], [80, 11, 27], [60, 55, 67]], ![[0, 1], [38, 47, 61], [56, 17, 38], [10, 66, 76], [71, 24, 33], [78, 72, 55], [5, 27, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44, 26], []]
 b := ![[], [2, 31, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [52, 0, 18, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6644231220, 5609598384, -899254752, -3425348336, 13299206208]
  a := ![-264, 648, -68, -340, 1338]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-8948876404, -11775001200, -2424159488, -3425348336, 13299206208]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 571787 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-783, 181, -53, -180, 766]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-783, 181, -53, -180, 766]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![80, 25, 1, 0, 0], ![75, 36, 0, 1, 0], ![45, 49, 0, 0, 1]] where
  M :=![![![-783, 181, -53, -180, 766], ![-4076, 935, -275, -935, 3980], ![-21200, 4904, -1440, -4885, 20790], ![-110660, 25510, -7481, -25420, 108190], ![-27858, 6425, -1884, -6401, 27243]]]
  hmulB := by decide  
  f := ![![![-25, 27, -5, -20, 80]], ![![-320, -105, 7, 35, -120]], ![![-120, 5, -5, -16, 70]], ![![-277, -51, 2, 10, -26]], ![![-229, -53, 2, 12, -35]]]
  g := ![![![-211, -356, -53, -180, 766], ![-1097, -1850, -275, -935, 3980], ![-5725, -9662, -1440, -4885, 20790], ![-29810, -50285, -7481, -25420, 108190], ![-7506, -12662, -1884, -6401, 27243]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P1 : CertificateIrreducibleZModOfList' 83 2 2 6 [26, 80, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 82], [0, 1]]
 g := ![![[35, 16], [26, 48], [10], [37], [37, 9], [1]], ![[0, 67], [4, 35], [10], [37], [64, 74], [1]]]
 h' := ![![[3, 82], [71, 4], [26, 52], [28, 33], [34, 55], [57, 3], [0, 1]], ![[0, 1], [0, 79], [16, 31], [44, 50], [33, 28], [66, 80], [3, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [62, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N1 : CertifiedPrimeIdeal' SI83N1 83 where
  n := 2
  hpos := by decide
  P := [26, 80, 1]
  hirr := P83P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16945495, 8131194, -1483060, -6411452, 26931533]
  a := ![-641, 1583, -166, -797, 3249]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7582660, -12573797, -1483060, -6411452, 26931533]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N1 B_one_repr
lemma NI83N1 : Nat.card (O ⧸ I83N1) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![25, -27, 5, 20, -80]] ![![-783, 181, -53, -180, 766]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0, 0, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0, 0, 0]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![0, 0, 0, 89, 0], ![0, 0, 0, 0, 89]] where
  M :=![![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![0, 0, 0, 89, 0], ![0, 0, 0, 0, 89]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 5 2 6 [53, 84, 31, 68, 45, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 48, 75, 46, 79], [19, 66, 87, 41, 6], [83, 64, 25, 63, 74], [2, 88, 80, 28, 19], [0, 1]]
 g := ![![[28, 46, 24, 29, 42], [62, 0, 3, 39], [1, 50, 35, 69], [2, 3, 15, 79, 67], [1], []], ![[0, 85, 13, 17, 35, 86, 14, 11], [62, 66, 53, 45], [15, 79, 58, 53], [80, 48, 23, 28, 68, 0, 59, 25], [38, 73, 37, 41, 44, 66, 10, 8], [49, 86, 9, 11]], ![[46, 7, 54, 76, 2, 51, 59, 56], [80, 32, 85, 9], [27, 49, 39, 20], [15, 1, 53, 38, 55, 58, 38, 43], [78, 0, 72, 32, 40, 60, 28, 51], [12, 40, 29, 36]], ![[34, 0, 86, 65, 29, 36, 16, 61], [24, 5, 53, 85], [13, 25, 43, 44], [6, 30, 74, 46, 49, 29, 47, 24], [55, 13, 34, 3, 70, 60, 87, 26], [73, 23, 0, 47]], ![[10, 34, 35, 84, 78, 51, 19, 63], [83, 17, 12, 72], [33, 65, 49, 79], [37, 7, 81, 82, 7, 18, 71, 70], [34, 46, 71, 48, 26, 55, 45, 58], [15, 83, 38, 5]]]
 h' := ![![[29, 48, 75, 46, 79], [78, 19, 17, 62, 65], [58, 9, 78, 44, 22], [72, 79, 52, 38, 46], [36, 5, 58, 21, 44], [0, 0, 1], [0, 1]], ![[19, 66, 87, 41, 6], [85, 40, 45, 51, 48], [73, 66, 25, 76, 57], [45, 84, 29, 35, 26], [5, 6, 4, 60, 65], [24, 73, 15, 39, 27], [29, 48, 75, 46, 79]], ![[83, 64, 25, 63, 74], [22, 62, 44, 30, 67], [48, 16, 42, 52, 3], [12, 81, 32, 51, 38], [19, 53, 0, 17, 72], [81, 3, 79, 56, 63], [19, 66, 87, 41, 6]], ![[2, 88, 80, 28, 19], [68, 24, 37, 5, 48], [70, 26, 20, 56, 68], [15, 31, 42, 35, 20], [73, 5, 24, 50, 52], [83, 69, 46, 61, 72], [83, 64, 25, 63, 74]], ![[0, 1], [49, 33, 35, 30, 39], [40, 61, 13, 39, 28], [86, 81, 23, 19, 48], [0, 20, 3, 30, 34], [10, 33, 37, 22, 16], [2, 88, 80, 28, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42, 56, 12, 52], [], [], []]
 b := ![[], [0, 43, 45, 74, 23], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 5
  hpos := by decide
  P := [53, 84, 31, 68, 45, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![25970425150420, 20983430456526, -3561557253737, -13304756907494, 51849795534255]
  a := ![-59, 141, -15, -75, 299]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![291802529780, 235768881534, -40017497233, -149491650646, 582581972295]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5045, 3331, -547, -2058, 7962]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![5045, 3331, -547, -2058, 7962]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![70, 58, 1, 0, 0], ![14, 4, 0, 1, 0], ![58, 64, 0, 0, 1]] where
  M :=![![![5045, 3331, -547, -2058, 7962], ![-25908, -17497, 2893, 10859, -42048], ![137656, 91092, -14966, -56301, 217834], ![-709196, -478158, 79011, 296626, -1148506], ![-145846, -98517, 16288, 61137, -236733]]]
  hmulB := by decide  
  f := ![![![31601, -7297, 2135, 7262, -30908]], ![![164552, -37931, 11125, 37831, -161028]], ![![130038, -29992, 8792, 29897, -127254]], ![![57474, -13264, 3885, 13212, -56234]], ![![139080, -32071, 9402, 31973, -136091]]]
  g := ![![![-4017, -4807, -547, -2058, 7962], ![21220, 25385, 2893, 10859, -42048], ![-109906, -131516, -14966, -56301, 217834], ![579594, 693372, 79011, 296626, -1148506], ![119470, 142919, 16288, 61137, -236733]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [16, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [91, 96], [0, 1]]
 g := ![![[61, 91], [85], [31], [31], [12], [91, 1]], ![[0, 6], [85], [31], [31], [12], [85, 96]]]
 h' := ![![[91, 96], [47, 24], [90, 45], [95, 15], [3, 82], [96, 20], [0, 1]], ![[0, 1], [0, 73], [14, 52], [5, 82], [93, 15], [73, 77], [91, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [21, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [16, 6, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5360783, 4948322, -940016, -3851052, 15905189]
  a := ![-527, 1296, -134, -662, 2671]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-8331401, -9722254, -940016, -3851052, 15905189]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-422791, 97650, -28608, -97254, 413938]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![-422791, 97650, -28608, -97254, 413938]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![47, 36, 1, 0, 0], ![54, 12, 0, 1, 0], ![68, 61, 0, 0, 1]] where
  M :=![![![-422791, 97650, -28608, -97254, 413938], ![-2204036, 509059, -149136, -506994, 2157896], ![-11489824, 2653748, -777455, -2642988, 11249236], ![-59897192, 13834276, -4052944, -13778147, 58643312], ![-15081480, 3483322, -1020488, -3469190, 14765759]]]
  hmulB := by decide  
  f := ![![![-1983, 278, -112, -362, 1538]], ![![-8132, 1339, -624, -1818, 7728]], ![![-4401, 722, -319, -946, 4018]], ![![-4194, 636, -272, -839, 3564]], ![![-7024, 1117, -504, -1500, 6375]]]
  g := ![![![-226539, -236656, -28608, -97254, 413938], ![-1180968, -1233709, -149136, -506994, 2157896], ![-6156455, -6431396, -777455, -2642988, 11249236], ![-32094166, -33527464, -4052944, -13778147, 58643312], ![-8080968, -8441857, -1020488, -3469190, 14765759]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P1 : CertificateIrreducibleZModOfList' 97 2 2 6 [38, 52, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [45, 96], [0, 1]]
 g := ![![[32, 49], [94], [3], [88], [75], [45, 1]], ![[6, 48], [94], [3], [88], [75], [90, 96]]]
 h' := ![![[45, 96], [18, 7], [1, 71], [55, 10], [95, 66], [36, 47], [0, 1]], ![[0, 1], [42, 90], [92, 26], [20, 87], [58, 31], [17, 50], [45, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [71]]
 b := ![[], [50, 84]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N1 : CertifiedPrimeIdeal' SI97N1 97 where
  n := 2
  hpos := by decide
  P := [38, 52, 1]
  hirr := P97P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2146487, 1507282, -281421, -1181466, 4905035]
  a := ![-293, 721, -77, -367, 1485]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2666628, -2818465, -281421, -1181466, 4905035]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N1 B_one_repr
lemma NI97N1 : Nat.card (O ⧸ I97N1) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N1

def I97N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![33, -6, 2, 6, -26]] i)))

def SI97N2: IdealEqSpanCertificate' Table ![![33, -6, 2, 6, -26]] 
 ![![97, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![88, 0, 1, 0, 0], ![27, 0, 0, 1, 0], ![67, 0, 0, 0, 1]] where
  M :=![![![33, -6, 2, 6, -26], ![148, -49, 12, 44, -184], ![912, -100, 43, 140, -616], ![3696, -1496, 376, 1275, -5320], ![952, -358, 92, 310, -1297]]]
  hmulB := by decide  
  f := ![![![-26023, 4622, -1878, -5582, 23654]], ![![-2081, 369, -150, -446, 1890]], ![![-29672, 5268, -2141, -6364, 26968]], ![![-36077, 6402, -2602, -7735, 32778]], ![![-25141, 4464, -1814, -5392, 22849]]]
  g := ![![![15, -6, 2, 6, -26], ![107, -49, 12, 44, -184], ![360, -100, 43, 140, -616], ![3063, -1496, 376, 1275, -5320], ![747, -358, 92, 310, -1297]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N2 : Nat.card (O ⧸ I97N2) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N2)

lemma isPrimeI97N2 : Ideal.IsPrime I97N2 := prime_ideal_of_norm_prime hp97.out _ NI97N2
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![5045, 3331, -547, -2058, 7962]] ![![-422791, 97650, -28608, -97254, 413938]]
  ![![-13407, -10621, 1805, 6738, -26244]] where
 M := ![![![-13407, -10621, 1805, 6738, -26244]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI97N1 : IdealMulLeCertificate' Table 
  ![![-13407, -10621, 1805, 6738, -26244]] ![![33, -6, 2, 6, -26]]
  ![![97, 0, 0, 0, 0]] where
 M := ![![![-448819, -264325, 42389, 160244, -616726]]]
 hmul := by decide  
 g := ![![![![-4627, -2725, 437, 1652, -6358]]]]
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


def P101P0 : CertificateIrreducibleZModOfList' 101 5 2 6 [63, 71, 99, 56, 100, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 65, 50, 66, 10], [57, 92, 93, 31, 12], [50, 46, 84, 37, 15], [77, 99, 76, 68, 64], [0, 1]]
 g := ![![[51, 99, 61, 10, 45], [90, 82, 24, 43], [24, 84, 5, 94, 78], [49, 56, 77, 96], [1, 1], []], ![[1, 2, 74, 86, 7, 56, 97, 91], [74, 65, 12, 33], [67, 1, 75, 53, 59, 17, 100, 44], [74, 6, 73, 5], [94, 86, 24, 76], [18, 97, 14, 46, 96, 87, 95, 91]], ![[50, 42, 88, 65, 48, 56, 51, 42], [32, 44, 64, 70], [12, 32, 84, 35, 85, 72], [5, 13, 58, 6], [5, 38, 58, 19], [6, 7, 4, 93, 45, 93, 71, 11]], ![[11, 45, 97, 68, 7, 50, 21, 39], [77, 99, 28, 95], [38, 95, 54, 20, 93, 35, 97, 60], [46, 4, 12, 30], [91, 48, 81, 79], [36, 37, 1, 77, 21, 75, 70, 42]], ![[62, 10, 73, 10, 21, 15, 66, 92], [69, 44, 53, 82], [82, 65, 44, 24, 58, 38, 48, 9], [16, 38, 2, 24], [2, 37, 75, 31], [60, 99, 37, 32, 22, 2, 60, 49]]]
 h' := ![![[19, 65, 50, 66, 10], [96, 29, 63, 99, 34], [3, 96, 54, 5, 89], [74, 80, 44, 39, 52], [38, 68, 32, 47, 46], [0, 0, 0, 1], [0, 1]], ![[57, 92, 93, 31, 12], [1, 75, 14, 65, 10], [44, 52, 46, 23, 72], [60, 93, 77, 33, 60], [51, 69, 92, 98, 56], [69, 83, 99, 49, 51], [19, 65, 50, 66, 10]], ![[50, 46, 84, 37, 15], [60, 70, 34, 58, 16], [64, 51, 3, 4, 75], [8, 54, 70, 62], [11, 65, 83, 68, 39], [86, 88, 81, 23, 25], [57, 92, 93, 31, 12]], ![[77, 99, 76, 68, 64], [51, 67, 66, 71, 12], [85, 33, 65, 95, 14], [30, 66, 14, 84, 2], [10, 58, 92, 29, 38], [17, 46, 28, 52, 68], [50, 46, 84, 37, 15]], ![[0, 1], [32, 62, 25, 10, 29], [95, 71, 34, 75, 53], [47, 10, 98, 85, 88], [67, 43, 4, 61, 23], [71, 86, 95, 77, 58], [77, 99, 76, 68, 64]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47, 67, 29, 47], [], [], []]
 b := ![[], [9, 45, 36, 51, 66], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 5
  hpos := by decide
  P := [63, 71, 99, 56, 100, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-85927029951561033, 23882494734804354, -6245677442347795, -22104506094449246, 93697511226191895]
  a := ![-248, 612, -65, -308, 1257]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-850762672787733, 236460343908954, -61838390518295, -218856495984646, 927698130952395]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-143917, -96209, 15858, 59585, -230632]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![-143917, -96209, 15858, 59585, -230632]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![0, 0, 0, 103, 0], ![91, 76, 14, 79, 1]] where
  M :=![![![-143917, -96209, 15858, 59585, -230632], ![752952, 502947, -82872, -311428, 1205390], ![-3934476, -2629826, 433451, 1628678, -6303988], ![20580024, 13748608, -2265492, -8513453, 32951708], ![4238670, 2831553, -466572, -1753341, 6786377]]]
  hmulB := by decide  
  f := ![![![-103, -139, 30, 55, -218]], ![![828, 223, -96, -134, 550]], ![![-2508, 1034, 5, -206, 736]], ![![-1008, -7996, 1356, 2793, -10916]], ![![-601, -5970, 1000, 2071, -8087]]]
  g := ![![![202365, 169241, 31502, 177471, -230632], ![-1057646, -884531, -164644, -927546, 1205390], ![5531344, 4625954, 861061, 4850910, -6303988], ![-28912868, -24180400, -4500868, -25356295, 32951708], ![-5954579, -4979933, -926950, -5222108, 6786377]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 4 2 6 [96, 82, 81, 41, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 94, 99, 57], [7, 44, 81, 75], [45, 67, 26, 74], [0, 1]]
 g := ![![[75, 52, 33, 13], [29, 5, 28, 83], [90, 47, 71, 30], [26, 75, 56], [55, 62, 1], []], ![[62, 65, 15, 30, 27, 69], [31, 71, 40, 39, 49, 86], [73, 41, 45, 30, 40, 69], [77, 25, 13], [33, 14, 18], [36, 26, 63, 87, 90, 102]], ![[55, 63, 95, 80, 84, 77], [80, 71, 72, 76, 6, 12], [71, 21, 23, 21, 85, 71], [83, 53, 23], [102, 61, 76], [53, 74, 6, 21, 83, 90]], ![[7, 48, 25, 60, 64, 96], [101, 54, 93, 31, 53, 40], [93, 67, 88, 54, 82, 24], [6, 85, 2], [43, 15, 55], [6, 67, 82, 11, 12, 22]]]
 h' := ![![[10, 94, 99, 57], [100, 67, 84, 61], [12, 3, 7, 17], [87, 34, 83, 37], [76, 44, 47, 57], [0, 0, 0, 1], [0, 1]], ![[7, 44, 81, 75], [16, 35, 95, 87], [84, 41, 83, 98], [87, 74, 92, 87], [75, 27, 14, 42], [16, 92, 22, 92], [10, 94, 99, 57]], ![[45, 67, 26, 74], [5, 11, 77, 69], [100, 61, 67, 21], [79, 51, 70, 36], [42, 11, 52, 69], [96, 65, 14, 73], [7, 44, 81, 75]], ![[0, 1], [28, 93, 53, 92], [7, 101, 49, 70], [101, 47, 64, 46], [33, 21, 93, 38], [12, 49, 67, 40], [45, 67, 26, 74]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [12, 78], []]
 b := ![[], [], [71, 31, 69], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 4
  hpos := by decide
  P := [96, 82, 81, 41, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-234766720048087, 138017797725774, -30469247693511, -111305839117846, 460616783567343]
  a := ![501, -1222, 119, 628, -2539]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-409231980822100, -338532599547498, -62903924443071, -354369240203281, 460616783567343]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 112550881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-103, -139, 30, 55, -218]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![-103, -139, 30, 55, -218]] 
 ![![103, 0, 0, 0, 0], ![88, 1, 0, 0, 0], ![84, 0, 1, 0, 0], ![24, 0, 0, 1, 0], ![56, 0, 0, 0, 1]] where
  M :=![![![-103, -139, 30, 55, -218], ![828, 223, -96, -134, 550], ![-2508, 1034, 5, -206, 736], ![-1008, -7996, 1356, 2793, -10916], ![-714, -2001, 372, 729, -2863]]]
  hmulB := by decide  
  f := ![![![-143917, -96209, 15858, 59585, -230632]], ![![-115648, -77315, 12744, 47884, -185342]], ![![-155568, -103994, 17141, 64406, -249292]], ![![166272, 111064, -18300, -68771, 266180]], ![![-37094, -24817, 4092, 15373, -59505]]]
  g := ![![![199, -139, 30, 55, -218], ![-372, 223, -96, -134, 550], ![-1264, 1034, 5, -206, 736], ![11000, -7996, 1356, 2793, -10916], ![2786, -2001, 372, 729, -2863]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![-143917, -96209, 15858, 59585, -230632]] ![![-103, -139, 30, 55, -218]]
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


lemma PB2201I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB2201I2 : PrimesBelowBoundCertificateInterval O 61 103 2201 where
  m := 9
  g := ![2, 2, 1, 2, 2, 1, 3, 1, 2]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB2201I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1]
    · exact ![I73N0]
    · exact ![I79N0, I79N1]
    · exact ![I83N0, I83N1]
    · exact ![I89N0]
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
    · exact ![25411681, 71]
    · exact ![2073071593]
    · exact ![38950081, 79]
    · exact ![571787, 6889]
    · exact ![5584059449]
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
  β := ![I71N1, I79N1, I97N2, I103N1]
  Il := ![[], [I71N1], [], [I79N1], [], [], [I97N2], [], [I103N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
