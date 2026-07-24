
import IdealArithmetic.Examples.NF5_3_1125000000_3.RI5_3_1125000000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-21152, -50618, -28813, 16477, 41578]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![-21152, -50618, -28813, 16477, 41578]] 
 ![![199, 0, 0, 0, 0], ![0, 199, 0, 0, 0], ![0, 0, 199, 0, 0], ![0, 0, 0, 199, 0], ![81, 128, 58, 49, 1]] where
  M :=![![![-21152, -50618, -28813, 16477, 41578], ![-23814, -57731, -33370, 19822, 48660], ![-23612, -62716, -39699, 28484, 61256], ![20353, 45454, 23799, -10612, -32284], ![10061, 19530, 8209, -493, -8961]]]
  hmulB := by decide  
  f := ![![![48, 26, -41, 11, 44]], ![![-114, -69, 70, -118, 0]], ![![-52, -236, 403, 604, -944]], ![![269, 302, -387, -82, 538]], ![![-4, -30, 53, 86, -129]]]
  g := ![![![-17030, -26998, -12263, -10155, 41578], ![-19926, -31589, -14350, -11882, 48660], ![-25052, -39716, -18053, -14940, 61256], ![13243, 20994, 9529, 7896, -32284], ![3698, 5862, 2653, 2204, -8961]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 4 2 7 [90, 112, 156, 177, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [86, 92, 132, 101], [6, 110, 192, 98], [129, 195, 74], [0, 1]]
 g := ![![[30, 44, 42, 112], [95, 161, 120, 145], [89, 89, 64, 29], [25, 39, 7], [154, 142, 140], [129, 22, 1], []], ![[86, 104, 94, 106, 105, 108], [75, 67, 126, 27, 54, 148], [1, 67, 142, 35, 112, 30], [174, 168, 80], [78, 123, 1], [12, 38, 91], [117, 151, 1, 39, 20, 78]], ![[178, 76, 106, 135, 176, 89], [126, 163, 50, 180, 123, 36], [161, 136, 189, 41, 146, 151], [103, 18, 130], [33, 102, 35], [39, 185, 116], [155, 104, 71, 67, 177, 121]], ![[105, 143, 38, 81, 93], [185, 37, 13, 74, 192], [132, 184, 159, 30, 74], [8, 133, 10], [137, 112, 145], [178, 3, 117], [81, 84, 60]]]
 h' := ![![[86, 92, 132, 101], [7, 56, 131, 50], [149, 193, 42, 44], [96, 28, 47, 32], [117, 56, 75, 112], [131, 89, 8, 90], [0, 0, 0, 1], [0, 1]], ![[6, 110, 192, 98], [24, 48, 41, 79], [161, 91, 93, 31], [86, 160, 103, 47], [194, 145, 0, 105], [99, 148, 49, 198], [69, 125, 187, 115], [86, 92, 132, 101]], ![[129, 195, 74], [76, 154, 44, 87], [24, 85, 57, 162], [164, 141, 127, 119], [9, 197, 169, 54], [81, 163, 3, 154], [196, 85, 104, 135], [6, 110, 192, 98]], ![[0, 1], [8, 140, 182, 182], [98, 29, 7, 161], [96, 69, 121, 1], [152, 0, 154, 127], [12, 197, 139, 155], [149, 188, 107, 147], [129, 195, 74]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [190, 143, 98], []]
 b := ![[], [], [102, 150, 122, 198], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 4
  hpos := by decide
  P := [90, 112, 156, 177, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![44590123404719, 44230734649886, -14226010702009, 67107911371387, 60364589978838]
  a := ![-176, -194, 145, -109, -324]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-24346440527041, -38605209963022, -17665187082787, -14526417073325, 60364589978838]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 1568239201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-48, -26, 41, -11, -44]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![-48, -26, 41, -11, -44]] 
 ![![199, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![135, 0, 1, 0, 0], ![73, 0, 0, 1, 0], ![122, 0, 0, 0, 1]] where
  M :=![![![-48, -26, 41, -11, -44], ![114, 69, -70, 118, 0], ![52, 236, -403, -604, 944], ![-269, -302, 387, 82, -538], ![257, 354, -497, -313, 845]]]
  hmulB := by decide  
  f := ![![![21152, 50618, 28813, -16477, -41578]], ![![970, 2325, 1326, -762, -1916]], ![![14468, 34654, 19746, -11321, -28514]], ![![7657, 18340, 10450, -5991, -15090]], ![![12917, 30934, 17623, -10099, -25445]]]
  g := ![![![4, -26, 41, -11, -44], ![2, 69, -70, 118, 0], ![-93, 236, -403, -604, 944], ![48, -302, 387, 82, -538], ![-79, 354, -497, -313, 845]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![-21152, -50618, -28813, 16477, 41578]] ![![-48, -26, 41, -11, -44]]
  ![![199, 0, 0, 0, 0]] where
 M := ![![![-199, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC199 : ContainsPrimesAboveP 199 ![I199N0, I199N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI199N0
    exact isPrimeI199N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 199 (by decide) (𝕀 ⊙ MulI199N0)
instance hp211 : Fact (Nat.Prime 211) := {out := by norm_num}

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-30123, 10791, 8835, -2238, -12620]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![-30123, 10791, 8835, -2238, -12620]] 
 ![![211, 0, 0, 0, 0], ![0, 211, 0, 0, 0], ![0, 0, 211, 0, 0], ![70, 44, 25, 1, 0], ![67, 131, 169, 0, 1]] where
  M :=![![![-30123, 10791, 8835, -2238, -12620], ![18818, -7520, -5497, 584, 7336], ![-15974, 1005, 4816, -6108, -10000], ![5926, -4456, -1674, -1993, 848], ![-5856, -1215, 1809, -3890, -4775]]]
  hmulB := by decide  
  f := ![![![-37, 1, 67, -62, -52]], ![![50, -2, 145, 264, -392]], ![![1142, 1439, -1842, -868, 2896]], ![![130, 167, -162, -69, 240]], ![![939, 1157, -1371, -552, 2069]]]
  g := ![![![4607, 8353, 10415, -2238, -12620], ![-2434, -4712, -5971, 584, 7336], ![5126, 7487, 8756, -6108, -10000], ![420, -132, -451, -1993, 848], ![2779, 3770, 4294, -3890, -4775]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 3 2 7 [143, 35, 194, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [20, 109, 185], [208, 101, 26], [0, 1]]
 g := ![![[112, 77, 87], [14, 116, 24], [26, 125], [157, 136], [41, 156, 6], [136, 78], [1]], ![[156, 202, 134, 172], [115, 150, 90, 44], [209, 137], [194, 100], [43, 204, 159, 154], [84, 163], [171, 50, 119, 148]], ![[199, 36, 33, 29], [101, 130, 20, 135], [86, 117], [199, 182], [149, 44, 155, 74], [0, 95], [129, 152, 174, 63]]]
 h' := ![![[20, 109, 185], [108, 67, 147], [73, 3, 92], [41, 49, 97], [45, 62, 66], [157, 4, 165], [68, 176, 17], [0, 1]], ![[208, 101, 26], [18, 104, 23], [105, 86, 141], [175, 94, 83], [109, 12, 201], [40, 29, 103], [5, 138, 95], [20, 109, 185]], ![[0, 1], [192, 40, 41], [195, 122, 189], [39, 68, 31], [86, 137, 155], [185, 178, 154], [94, 108, 99], [208, 101, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [169, 4], []]
 b := ![[], [121, 130, 130], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 3
  hpos := by decide
  P := [143, 35, 194, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-19691681823661, -19678920333556, 7164855195870, -28168779116590, -27428357085124]
  a := ![-2547, -2778, 1994, -1752, -4457]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![17961245407777, 22809773170368, 25340173841216, -28168779116590, -27428357085124]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 9393931 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, -1, -67, 62, 52]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![37, -1, -67, 62, 52]] 
 ![![211, 0, 0, 0, 0], ![0, 211, 0, 0, 0], ![199, 122, 1, 0, 0], ![17, 113, 0, 1, 0], ![107, 132, 0, 0, 1]] where
  M :=![![![37, -1, -67, 62, 52], ![-50, 2, -145, -264, 392], ![-1142, -1439, 1842, 868, -2896], ![730, 720, -798, 135, 872], ![-1060, -1131, 1467, 210, -1971]]]
  hmulB := by decide  
  f := ![![![30123, -10791, -8835, 2238, 12620]], ![![-18818, 7520, 5497, -584, -7336]], ![![17605, -5834, -5177, 1802, 7708]], ![![-7679, 3179, 2240, -123, -2916]], ![![3531, -762, -1050, 788, 1833]]]
  g := ![![![32, -27, -67, 62, 52], ![-41, -20, -145, -264, 392], ![-344, 275, 1842, 868, -2896], ![303, -153, -798, 135, 872], ![-406, 267, 1467, 210, -1971]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P1 : CertificateIrreducibleZModOfList' 211 2 2 7 [14, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [208, 210], [0, 1]]
 g := ![![[166, 196], [3, 1], [179], [172], [174, 54], [25], [208, 1]], ![[0, 15], [0, 210], [179], [172], [12, 157], [25], [205, 210]]]
 h' := ![![[208, 210], [169, 197], [208, 210], [56, 50], [96, 159], [148, 138], [42, 206], [0, 1]], ![[0, 1], [0, 14], [0, 1], [117, 161], [41, 52], [156, 73], [57, 5], [208, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [27, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N1 : CertifiedPrimeIdeal' SI211N1 211 where
  n := 2
  hpos := by decide
  P := [14, 3, 1]
  hirr := P211P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![461457, 448123, -74266, 814647, 572552]
  a := ![-139, -151, 107, -99, -239]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-283752, -749400, -74266, 814647, 572552]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N1 B_one_repr
lemma NI211N1 : Nat.card (O ⧸ I211N1) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![-30123, 10791, 8835, -2238, -12620]] ![![37, -1, -67, 62, 52]]
  ![![211, 0, 0, 0, 0]] where
 M := ![![![-211, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC211 : ContainsPrimesAboveP 211 ![I211N0, I211N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI211N0
    exact isPrimeI211N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 211 (by decide) (𝕀 ⊙ MulI211N0)
instance hp223 : Fact (Nat.Prime 223) := {out := by norm_num}

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![468, 1183, 742, -411, -1046]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![468, 1183, 742, -411, -1046]] 
 ![![223, 0, 0, 0, 0], ![0, 223, 0, 0, 0], ![0, 0, 223, 0, 0], ![98, 178, 159, 1, 0], ![193, 124, 82, 0, 1]] where
  M :=![![![468, 1183, 742, -411, -1046], ![716, 1488, 735, -286, -1196], ![874, 2051, 240, -1320, 104], ![-835, -1470, -49, 414, 124], ![255, 145, -966, -261, 1525]]]
  hmulB := by decide  
  f := ![![![-20580, 7437, 6034, -1461, -8576]], ![![13208, -4830, -3871, 878, 5464]], ![![-8786, 2829, 2586, -984, -3904]], ![![-4743, 1421, 1399, -642, -2182]], ![![-13709, 4794, 4024, -1140, -5825]]]
  g := ![![![1088, 915, 681, -411, -1046], ![1164, 900, 647, -286, -1196], ![494, 1005, 904, -1320, 104], ![-293, -406, -341, 414, 124], ![-1204, -639, -379, -261, 1525]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 3 2 7 [84, 57, 172, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [183, 216, 68], [91, 6, 155], [0, 1]]
 g := ![![[181, 180, 166], [80, 70, 106], [196, 35, 139], [213, 34, 121], [146, 0, 7], [173, 148], [1]], ![[139, 216, 45, 143], [60, 61, 52, 47], [28, 141, 174, 188], [48, 89, 119, 100], [118, 64, 69, 197], [75, 4], [94, 167, 3, 2]], ![[2, 31, 15, 12], [74, 128, 167, 184], [62, 119, 173, 187], [191, 17, 149, 45], [56, 50, 221, 204], [163, 171], [135, 32, 174, 221]]]
 h' := ![![[183, 216, 68], [193, 147, 122], [38, 188, 38], [171, 168, 129], [1, 15, 11], [106, 217, 197], [139, 166, 51], [0, 1]], ![[91, 6, 155], [47, 81, 24], [102, 57, 78], [183, 5, 156], [141, 134, 194], [16, 65, 105], [133, 88, 221], [183, 216, 68]], ![[0, 1], [165, 218, 77], [150, 201, 107], [179, 50, 161], [108, 74, 18], [121, 164, 144], [87, 192, 174], [91, 6, 155]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35, 73], []]
 b := ![[], [1, 19, 35], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 3
  hpos := by decide
  P := [84, 57, 172, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1283718553037, 1286676484001, -475122193478, 1821917905539, 1806710149096]
  a := ![1030, 1133, -838, 655, 1873]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2358561860831, -2453124525515, -1965517046637, 1821917905539, 1806710149096]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 11089567 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-28, 11, 8, -1, -12]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![-28, 11, 8, -1, -12]] 
 ![![223, 0, 0, 0, 0], ![30, 1, 0, 0, 0], ![215, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![61, 0, 0, 0, 1]] where
  M :=![![![-28, 11, 8, -1, -12], ![20, -4, -9, -2, 16], ![-30, -17, 36, 16, -48], ![21, 10, -15, 8, 18], ![-19, -15, 24, 5, -27]]]
  hmulB := by decide  
  f := ![![![13572, 32385, 18376, -10423, -26458]], ![![1896, 4524, 2567, -1456, -3696]], ![![13166, 31416, 17826, -10111, -25666]], ![![435, 1038, 589, -334, -848]], ![![3693, 8812, 5000, -2836, -7199]]]
  g := ![![![-6, 11, 8, -1, -12], ![5, -4, -9, -2, 16], ![-20, -17, 36, 16, -48], ![8, 10, -15, 8, 18], ![-14, -15, 24, 5, -27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1

def I223N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-629, 218, 178, -40, -252]] i)))

def SI223N2: IdealEqSpanCertificate' Table ![![-629, 218, 178, -40, -252]] 
 ![![223, 0, 0, 0, 0], ![69, 1, 0, 0, 0], ![145, 0, 1, 0, 0], ![30, 0, 0, 1, 0], ![51, 0, 0, 0, 1]] where
  M :=![![![-629, 218, 178, -40, -252], ![404, -151, -126, 40, 184], ![-228, 118, 57, 40, -48], ![180, -32, -48, 35, 84], ![-44, 54, 14, 32, 3]]]
  hmulB := by decide  
  f := ![![![461, 618, -870, -520, 1460]], ![![123, 171, -244, -160, 420]], ![![391, 480, -653, -288, 1020]], ![![54, 84, -124, -101, 228]], ![![149, 172, -228, -72, 335]]]
  g := ![![![-123, 218, 178, -40, -252], ![83, -151, -126, 40, 184], ![-69, 118, 57, 40, -48], ![18, -32, -48, 35, 84], ![-31, 54, 14, 32, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N2 : Nat.card (O ⧸ I223N2) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N2)

lemma isPrimeI223N2 : Ideal.IsPrime I223N2 := prime_ideal_of_norm_prime hp223.out _ NI223N2
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![468, 1183, 742, -411, -1046]] ![![-28, 11, 8, -1, -12]]
  ![![-461, -618, 870, 520, -1460]] where
 M := ![![![-461, -618, 870, 520, -1460]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI223N1 : IdealMulLeCertificate' Table 
  ![![-461, -618, 870, 520, -1460]] ![![-629, 218, 178, -40, -252]]
  ![![223, 0, 0, 0, 0]] where
 M := ![![![-223, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC223 : ContainsPrimesAboveP 223 ![I223N0, I223N1, I223N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI223N0
    exact isPrimeI223N1
    exact isPrimeI223N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 223 (by decide) (𝕀 ⊙ MulI223N0 ⊙ MulI223N1)
instance hp227 : Fact (Nat.Prime 227) := {out := by norm_num}

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1151, 4863, 2827, -1530, -4066]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![1151, 4863, 2827, -1530, -4066]] 
 ![![227, 0, 0, 0, 0], ![0, 227, 0, 0, 0], ![0, 0, 227, 0, 0], ![130, 24, 165, 1, 0], ![94, 161, 154, 0, 1]] where
  M :=![![![1151, 4863, 2827, -1530, -4066], ![2710, 5100, 2851, -1664, -4108], ![2234, 6201, 3540, -1980, -5096], ![-1444, -3980, -2274, 1271, 3274], ![-704, -1443, -815, 470, 1173]]]
  hmulB := by decide  
  f := ![![![25, 25, -13, 30, 34]], ![![110, 114, -27, 176, 172]], ![![886, 851, -246, 1404, 1064]], ![![672, 647, -190, 1059, 814]], ![![692, 671, -192, 1094, 861]]]
  g := ![![![2565, 3067, 3883, -1530, -4066], ![2666, 3112, 4009, -1664, -4108], ![3254, 3851, 4912, -1980, -5096], ![-2090, -2474, -3155, 1271, 3274], ![-758, -888, -1141, 470, 1173]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 3 2 7 [9, 117, 170, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [77, 8, 54], [207, 218, 173], [0, 1]]
 g := ![![[168, 72, 131], [116, 84, 181], [186, 188], [139, 30], [0, 16], [47, 16, 71], [1]], ![[76, 187, 56, 55], [79, 204, 73, 152], [53, 79], [206, 57], [40, 110], [44, 105, 204, 206], [155, 29, 163, 153]], ![[57, 96, 23, 75], [163, 78, 81, 120], [146, 76], [136, 65], [196, 76], [200, 194, 194, 159], [4, 168, 169, 74]]]
 h' := ![![[77, 8, 54], [91, 89, 49], [195, 186, 194], [196, 102, 142], [53, 52, 22], [31, 113, 4], [218, 110, 57], [0, 1]], ![[207, 218, 173], [147, 11, 52], [59, 158, 126], [189, 128, 144], [0, 92, 113], [70, 226, 164], [3, 185, 206], [77, 8, 54]], ![[0, 1], [72, 127, 126], [195, 110, 134], [123, 224, 168], [165, 83, 92], [106, 115, 59], [136, 159, 191], [207, 218, 173]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [143, 205], []]
 b := ![[], [57, 13, 219], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 3
  hpos := by decide
  P := [9, 117, 170, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-14484126357, -14900160386, 5899685388, -19533621958, -22241110290]
  a := ![-241, -275, 228, -100, -509]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![20332824209, 17774121248, 29313120234, -19533621958, -22241110290]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 11697083 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![279, 305, -59, 370, 316]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![279, 305, -59, 370, 316]] 
 ![![227, 0, 0, 0, 0], ![66, 1, 0, 0, 0], ![184, 0, 1, 0, 0], ![96, 0, 0, 1, 0], ![38, 0, 0, 0, 1]] where
  M :=![![![279, 305, -59, 370, 316], ![1758, 1780, -543, 2560, 2328], ![11638, 11611, -3804, 17228, 15824], ![5606, 5552, -1882, 8365, 7720], ![8100, 8047, -2689, 12046, 11095]]]
  hmulB := by decide  
  f := ![![![-3967, 1023, 1477, -190, -2076]], ![![-1136, 300, 419, -52, -592]], ![![-3242, 819, 1210, -180, -1680]], ![![-1678, 424, 634, -71, -896]], ![![-670, 173, 243, -50, -329]]]
  g := ![![![-249, 305, -59, 370, 316], ![-1542, 1780, -543, 2560, 2328], ![-10176, 11611, -3804, 17228, 15824], ![-4894, 5552, -1882, 8365, 7720], ![-7076, 8047, -2689, 12046, 11095]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N1 : Nat.card (O ⧸ I227N1) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N1)

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := prime_ideal_of_norm_prime hp227.out _ NI227N1

def I227N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2174, -5185, -2942, 1669, 4236]] i)))

def SI227N2: IdealEqSpanCertificate' Table ![![-2174, -5185, -2942, 1669, 4236]] 
 ![![227, 0, 0, 0, 0], ![224, 1, 0, 0, 0], ![218, 0, 1, 0, 0], ![113, 0, 0, 1, 0], ![40, 0, 0, 0, 1]] where
  M :=![![![-2174, -5185, -2942, 1669, 4236], ![-2504, -5972, -3389, 1922, 4880], ![-2886, -6881, -3900, 2216, 5616], ![1855, 4422, 2507, -1422, -3610], ![699, 1669, 950, -537, -1367]]]
  hmulB := by decide  
  f := ![![![46982, -16999, -13770, 3319, 19566]], ![![46228, -16726, -13549, 3266, 19252]], ![![45206, -16355, -13250, 3194, 18828]], ![![23335, -8443, -6839, 1649, 9718]], ![![8303, -3003, -2434, 587, 3459]]]
  g := ![![![6355, -5185, -2942, 1669, 4236], ![7320, -5972, -3389, 1922, 4880], ![8430, -6881, -3900, 2216, 5616], ![-5419, 4422, 2507, -1422, -3610], ![-2048, 1669, 950, -537, -1367]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N2 : Nat.card (O ⧸ I227N2) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N2)

lemma isPrimeI227N2 : Ideal.IsPrime I227N2 := prime_ideal_of_norm_prime hp227.out _ NI227N2
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![1151, 4863, 2827, -1530, -4066]] ![![279, 305, -59, 370, 316]]
  ![![259129, 617830, 350508, -198780, -504642]] where
 M := ![![![259129, 617830, 350508, -198780, -504642]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI227N1 : IdealMulLeCertificate' Table 
  ![![259129, 617830, 350508, -198780, -504642]] ![![-2174, -5185, -2942, 1669, 4236]]
  ![![227, 0, 0, 0, 0]] where
 M := ![![![-3843440512, -9166362831, -5200915948, 2950339203, 7488575186]]]
 hmul := by decide  
 g := ![![![![-16931456, -40380453, -22911524, 12997089, 32989318]]]]
 hle2 := by decide  


def PBC227 : ContainsPrimesAboveP 227 ![I227N0, I227N1, I227N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI227N0
    exact isPrimeI227N1
    exact isPrimeI227N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 227 (by decide) (𝕀 ⊙ MulI227N0 ⊙ MulI227N1)
instance hp229 : Fact (Nat.Prime 229) := {out := by norm_num}

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0, 0, 0]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![229, 0, 0, 0, 0]] 
 ![![229, 0, 0, 0, 0], ![0, 229, 0, 0, 0], ![0, 0, 229, 0, 0], ![0, 0, 0, 229, 0], ![0, 0, 0, 0, 229]] where
  M :=![![![229, 0, 0, 0, 0], ![0, 229, 0, 0, 0], ![0, 0, 229, 0, 0], ![0, 0, 0, 229, 0], ![0, 0, 0, 0, 229]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 5 2 7 [195, 60, 197, 38, 205, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [156, 179, 143, 39, 72], [85, 128, 147, 27, 151], [6, 5, 201, 138, 39], [6, 145, 196, 25, 196], [0, 1]]
 g := ![![[45, 10, 17, 44, 64], [32, 212, 68, 187], [181, 144, 150, 122, 100], [148, 48, 108, 58], [8, 79, 223, 33], [80, 24, 1], []], ![[23, 47, 122, 190, 221, 47, 169, 73], [48, 179, 118, 203], [56, 24, 11, 169, 228, 202, 140, 39], [33, 161, 153, 130], [204, 66, 150, 55], [26, 148, 81, 51, 153, 178, 51, 143], [65, 101, 7, 62, 180, 168, 66, 207]], ![[14, 197, 64, 17, 135, 189, 158, 165], [148, 91, 174, 43], [57, 54, 18, 129, 120, 200, 147, 14], [23, 145, 49, 213], [127, 64, 129, 180], [157, 163, 194, 23, 184, 31, 33, 147], [94, 64, 211, 77, 217, 150, 63, 165]], ![[98, 184, 62, 76, 192, 204, 226, 79], [4, 162, 19, 204], [63, 61, 71, 167, 8, 146, 50, 216], [167, 151, 59, 68], [132, 121, 17, 62], [138, 4, 47, 199, 40, 157, 227, 77], [77, 125, 21, 183, 208, 208, 136, 8]], ![[184, 143, 188, 222, 129, 157, 180, 210], [163, 10, 74, 3], [49, 53, 221, 9, 80, 224, 220, 172], [136, 2, 178, 178], [175, 193, 144, 43], [19, 60, 227, 13, 67, 127, 20, 49], [60, 142, 218, 76, 207, 98, 77, 16]]]
 h' := ![![[156, 179, 143, 39, 72], [97, 200, 180, 36, 221], [200, 143, 10, 105, 88], [129, 128, 8, 91, 219], [140, 203, 112, 69, 150], [201, 138, 9, 187, 124], [0, 0, 0, 1], [0, 1]], ![[85, 128, 147, 27, 151], [40, 22, 197, 9, 6], [195, 195, 224, 191, 165], [48, 146, 6, 61, 137], [23, 206, 197, 3, 78], [84, 58, 65, 177, 183], [203, 81, 224, 16, 14], [156, 179, 143, 39, 72]], ![[6, 5, 201, 138, 39], [179, 220, 33, 162, 78], [177, 114, 212, 113, 57], [186, 177, 41, 44, 75], [159, 29, 193, 134, 199], [119, 201, 160, 176, 167], [166, 36, 122, 128, 211], [85, 128, 147, 27, 151]], ![[6, 145, 196, 25, 196], [74, 111, 31, 75, 222], [204, 181, 36, 178, 77], [140, 215, 145, 55, 166], [88, 163, 112, 109, 143], [62, 8, 83, 203, 156], [86, 170, 203, 224, 118], [6, 5, 201, 138, 39]], ![[0, 1], [207, 134, 17, 176, 160], [42, 54, 205, 100, 71], [49, 21, 29, 207, 90], [163, 86, 73, 143, 117], [25, 53, 141, 173, 57], [195, 171, 138, 89, 115], [6, 145, 196, 25, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [123, 179, 33, 222], [], [], []]
 b := ![[], [87, 4, 189, 208, 16], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 5
  hpos := by decide
  P := [195, 60, 197, 38, 205, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1603859373708751, 2140415199390048, 6100491707225204, 12696009658115648, 4154481056210432]
  a := ![98, 126, -136, -32, 304]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![7003752723619, 9346791263712, 26639701778276, 55441090210112, 18141838673408]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 629763392149 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def PBC229 : ContainsPrimesAboveP 229 ![I229N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI229N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![229, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 229 (by decide) 𝕀

instance hp233 : Fact (Nat.Prime 233) := {out := by norm_num}

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11623, 27864, 15814, -8966, -22770]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![11623, 27864, 15814, -8966, -22770]] 
 ![![233, 0, 0, 0, 0], ![0, 233, 0, 0, 0], ![0, 0, 233, 0, 0], ![0, 0, 0, 233, 0], ![127, 115, 167, 173, 1]] where
  M :=![![![11623, 27864, 15814, -8966, -22770], ![13480, 32059, 18188, -10324, -26188], ![15456, 36936, 20979, -11896, -30216], ![-9940, -23744, -13478, 7637, 19402], ![-3778, -8980, -5078, 2882, 7307]]]
  hmulB := by decide  
  f := ![![![-5, 0, 2, -2, -2]], ![![0, -5, 4, 4, -12]], ![![16, 24, -45, -40, 56]], ![![-24, -24, 22, -15, -30]], ![![-9, -3, -13, -39, 11]]]
  g := ![![![12461, 11358, 16388, 16868, -22770], ![14332, 13063, 18848, 19400, -26188], ![16536, 15072, 21747, 22384, -30216], ![-10618, -9678, -13964, -14373, 19402], ![-3999, -3645, -5259, -5413, 7307]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 4 2 7 [60, 37, 173, 65, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 126, 65, 52], [97, 140, 131, 79], [49, 199, 37, 102], [0, 1]]
 g := ![![[54, 22, 96, 232], [137, 99, 13], [90, 45, 177], [154, 79, 159, 50], [195, 167, 208], [167, 91, 168, 1], []], ![[176, 13, 0, 132, 29, 175], [151, 129, 1], [124, 216, 203], [5, 98, 126, 61, 92, 184], [188, 110, 207], [138, 126, 140, 52, 172, 110], [33, 136, 77, 185, 139, 109]], ![[126, 62, 106, 28, 128, 180], [42, 105, 23], [9, 108, 120], [13, 197, 174, 145, 92, 44], [62, 135, 171], [19, 94, 221, 166, 200, 164], [108, 70, 207, 125, 139, 11]], ![[195, 130, 153, 227, 232, 162], [110, 129, 46], [167, 191, 129], [202, 33, 64, 109, 231, 182], [165, 113, 205], [10, 216, 90, 185, 34, 105], [228, 54, 128, 187, 61, 126]]]
 h' := ![![[22, 126, 65, 52], [132, 42, 98, 144], [68, 35, 101, 180], [80, 118, 111, 115], [184, 218, 16, 41], [232, 11, 68, 212], [0, 0, 0, 1], [0, 1]], ![[97, 140, 131, 79], [202, 70, 72, 122], [116, 117, 136, 232], [223, 107, 197, 160], [218, 208, 55, 96], [9, 221, 168, 48], [47, 219, 47, 31], [22, 126, 65, 52]], ![[49, 199, 37, 102], [93, 30, 73, 169], [192, 188, 50, 16], [158, 104, 125, 54], [45, 31, 22, 158], [152, 9, 96, 95], [56, 59, 111, 194], [97, 140, 131, 79]], ![[0, 1], [94, 91, 223, 31], [50, 126, 179, 38], [98, 137, 33, 137], [208, 9, 140, 171], [97, 225, 134, 111], [51, 188, 75, 7], [49, 199, 37, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [188, 151, 173], []]
 b := ![[], [], [208, 207, 138, 45], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 4
  hpos := by decide
  P := [60, 37, 173, 65, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![914131518023441, 906321217255830, -292129509120905, 1375182494101179, 1235475869004028]
  a := ![374, 413, -313, 219, 701]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-669490574444155, -605894436558830, -886766522029157, -911425505766505, 1235475869004028]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 2947295521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, -2, 2, 2]] i)))

def SI233N1: IdealEqSpanCertificate' Table ![![5, 0, -2, 2, 2]] 
 ![![233, 0, 0, 0, 0], ![16, 1, 0, 0, 0], ![210, 0, 1, 0, 0], ![141, 0, 0, 1, 0], ![188, 0, 0, 0, 1]] where
  M :=![![![5, 0, -2, 2, 2], ![0, 5, -4, -4, 12], ![-16, -24, 45, 40, -56], ![24, 24, -22, 15, 30], ![-18, -20, 34, 18, -35]]]
  hmulB := by decide  
  f := ![![![-11623, -27864, -15814, 8966, 22770]], ![![-856, -2051, -1164, 660, 1676]], ![![-10542, -25272, -14343, 8132, 20652]], ![![-6991, -16760, -9512, 5393, 13696]], ![![-9362, -22444, -12738, 7222, 18341]]]
  g := ![![![-1, 0, -2, 2, 2], ![-4, 5, -4, -4, 12], ![-18, -24, 45, 40, -56], ![-15, 24, -22, 15, 30], ![-12, -20, 34, 18, -35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N1 : Nat.card (O ⧸ I233N1) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N1)

lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := prime_ideal_of_norm_prime hp233.out _ NI233N1
def MulI233N0 : IdealMulLeCertificate' Table 
  ![![11623, 27864, 15814, -8966, -22770]] ![![5, 0, -2, 2, 2]]
  ![![233, 0, 0, 0, 0]] where
 M := ![![![-233, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC233 : ContainsPrimesAboveP 233 ![I233N0, I233N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI233N0
    exact isPrimeI233N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 233 (by decide) (𝕀 ⊙ MulI233N0)
instance hp239 : Fact (Nat.Prime 239) := {out := by norm_num}

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2980, 1071, 874, -219, -1242]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![-2980, 1071, 874, -219, -1242]] 
 ![![239, 0, 0, 0, 0], ![0, 239, 0, 0, 0], ![0, 0, 239, 0, 0], ![210, 199, 36, 1, 0], ![107, 128, 73, 0, 1]] where
  M :=![![![-2980, 1071, 874, -219, -1242], ![1884, -728, -537, 114, 732], ![-1302, 387, 280, -360, -552], ![633, -390, -153, -86, 168], ![-377, 81, 46, -189, -191]]]
  hmulB := by decide  
  f := ![![![12940, 30861, 17510, -9933, -25212]], ![![14904, 35546, 20169, -11442, -29040]], ![![17166, 40941, 23234, -13176, -33456]], ![![26319, 62770, 35616, -20204, -51282]], ![![19001, 45317, 25714, -14586, -37025]]]
  g := ![![![736, 852, 416, -219, -1242], ![-420, -490, -243, 114, 732], ![558, 597, 224, -360, -552], ![3, -20, -39, -86, 168], ![250, 260, 87, -189, -191]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 3 2 7 [167, 155, 20, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [107, 230, 204], [112, 8, 35], [0, 1]]
 g := ![![[38, 65, 85], [153, 9, 32], [12, 64, 213], [194, 16, 127], [74, 135], [164, 112, 161], [1]], ![[195, 161, 107, 45], [125, 216, 17, 201], [234, 122, 108, 218], [57, 51, 85, 1], [117, 132], [202, 136, 36, 197], [61, 31, 114, 145]], ![[45, 20, 221, 209], [94, 190, 59, 86], [68, 184, 145, 143], [51, 76, 215, 79], [166, 220], [112, 188, 40, 179], [2, 96, 35, 94]]]
 h' := ![![[107, 230, 204], [22, 215, 18], [147, 122, 82], [106, 109, 90], [158, 114, 137], [97, 17, 180], [72, 84, 219], [0, 1]], ![[112, 8, 35], [70, 76, 28], [103, 70, 210], [232, 231, 12], [161, 86, 213], [113, 120, 128], [19, 90, 7], [107, 230, 204]], ![[0, 1], [162, 187, 193], [112, 47, 186], [164, 138, 137], [167, 39, 128], [167, 102, 170], [230, 65, 13], [112, 8, 35]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [232, 212], []]
 b := ![[], [2, 48, 88], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 3
  hpos := by decide
  P := [167, 155, 20, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1223818914, -1217815761, 428297244, -1779950601, -1678481440]
  a := ![-100, -107, 72, -79, -161]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2310306784, 2375891122, 782576000, -1779950601, -1678481440]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N0 B_one_repr
lemma NI239N0 : Nat.card (O ⧸ I239N0) = 13651919 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N0

def I239N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-12940, -30861, -17510, 9933, 25212]] i)))

def SI239N1: IdealEqSpanCertificate' Table ![![-12940, -30861, -17510, 9933, 25212]] 
 ![![239, 0, 0, 0, 0], ![0, 239, 0, 0, 0], ![186, 46, 1, 0, 0], ![124, 218, 0, 1, 0], ![13, 165, 0, 0, 1]] where
  M :=![![![-12940, -30861, -17510, 9933, 25212], ![-14904, -35546, -20169, 11442, 29040], ![-17166, -40941, -23234, 13176, 33456], ![11031, 26310, 14931, -8468, -21498], ![4171, 9945, 5638, -3201, -8117]]]
  hmulB := by decide  
  f := ![![![2980, -1071, -874, 219, 1242]], ![![-1884, 728, 537, -114, -732]], ![![1962, -695, -578, 150, 828]], ![![-175, 110, 37, 10, -24]], ![![-1137, 444, 323, -66, -437]]]
  g := ![![![7048, -23225, -17510, 9933, 25212], ![8118, -26752, -20169, 11442, 29040], ![9354, -30815, -23234, 13176, 33456], ![-6011, 19802, 14931, -8468, -21498], ![-2268, 7480, 5638, -3201, -8117]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P1 : CertificateIrreducibleZModOfList' 239 2 2 7 [230, 196, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [43, 238], [0, 1]]
 g := ![![[111, 44], [117, 182], [105, 183], [214, 32], [25], [181, 48], [43, 1]], ![[91, 195], [56, 57], [87, 56], [156, 207], [25], [94, 191], [86, 238]]]
 h' := ![![[43, 238], [97, 98], [228, 144], [14, 30], [10, 157], [195, 5], [148, 185], [0, 1]], ![[0, 1], [9, 141], [206, 95], [109, 209], [69, 82], [171, 234], [216, 54], [43, 238]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [202, 124]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N1 : CertifiedPrimeIdeal' SI239N1 239 where
  n := 2
  hpos := by decide
  P := [230, 196, 1]
  hirr := P239P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2443945, 2260354, -193426, 4678822, 2479057]
  a := ![325, 365, -289, 164, 647]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2401592, -5932509, -193426, 4678822, 2479057]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N1 : Ideal.IsPrime I239N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N1 B_one_repr
lemma NI239N1 : Nat.card (O ⧸ I239N1) = 57121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N1
def MulI239N0 : IdealMulLeCertificate' Table 
  ![![-2980, 1071, 874, -219, -1242]] ![![-12940, -30861, -17510, 9933, 25212]]
  ![![239, 0, 0, 0, 0]] where
 M := ![![![-239, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC239 : ContainsPrimesAboveP 239 ![I239N0, I239N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI239N0
    exact isPrimeI239N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 239 (by decide) (𝕀 ⊙ MulI239N0)
instance hp241 : Fact (Nat.Prime 241) := {out := by norm_num}

def I241N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1718, 4097, 2324, -1319, -3346]] i)))

def SI241N0: IdealEqSpanCertificate' Table ![![1718, 4097, 2324, -1319, -3346]] 
 ![![241, 0, 0, 0, 0], ![0, 241, 0, 0, 0], ![126, 161, 1, 0, 0], ![238, 60, 0, 1, 0], ![23, 33, 0, 0, 1]] where
  M :=![![![1718, 4097, 2324, -1319, -3346], ![1976, 4716, 2681, -1518, -3860], ![2294, 5449, 3068, -1744, -4424], ![-1467, -3494, -1981, 1120, 2856], ![-545, -1313, -756, 431, 1083]]]
  hmulB := by decide  
  f := ![![![2382, -851, -700, 177, 1000]], ![![-1492, 590, 441, -46, -584]], ![![254, -51, -73, 64, 136]], ![![1979, -692, -581, 164, 842]], ![![25, 0, -7, 12, 17]]]
  g := ![![![414, -749, 2324, -1319, -3346], ![474, -865, 2681, -1518, -3860], ![550, -987, 3068, -1744, -4424], ![-349, 639, -1981, 1120, 2856], ![-136, 244, -756, 431, 1083]]]
  hle1 := by decide   
  hle2 := by decide  


def P241P0 : CertificateIrreducibleZModOfList' 241 2 2 7 [73, 135, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [106, 240], [0, 1]]
 g := ![![[124, 191], [8], [212], [72], [238, 81], [39, 145], [106, 1]], ![[126, 50], [8], [212], [72], [148, 160], [226, 96], [212, 240]]]
 h' := ![![[106, 240], [39, 51], [83, 197], [48, 137], [219, 132], [45, 9], [215, 77], [0, 1]], ![[0, 1], [143, 190], [239, 44], [110, 104], [233, 109], [35, 232], [183, 164], [106, 240]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [152, 129]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 2
  hpos := by decide
  P := [73, 135, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![863690, 792915, -57228, 1673805, 847278]
  a := ![194, 219, -176, 93, 393]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1700326, -491211, -57228, 1673805, 847278]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI241N0 : Ideal.IsPrime I241N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI241N0 B_one_repr
lemma NI241N0 : Nat.card (O ⧸ I241N0) = 58081 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI241N0

def I241N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6949, -15930, -9018, 5138, 12986]] i)))

def SI241N1: IdealEqSpanCertificate' Table ![![-6949, -15930, -9018, 5138, 12986]] 
 ![![241, 0, 0, 0, 0], ![0, 241, 0, 0, 0], ![118, 23, 1, 0, 0], ![176, 167, 0, 1, 0], ![143, 205, 0, 0, 1]] where
  M :=![![![-6949, -15930, -9018, 5138, 12986], ![-7584, -18501, -10510, 5948, 15132], ![-9004, -21210, -12029, 6832, 17320], ![5784, 13632, 7730, -4391, -11130], ![2138, 5170, 2934, -1662, -4225]]]
  hmulB := by decide  
  f := ![![![1135, 1130, -386, 1670, 1554]], ![![7472, 7439, -2442, 11140, 10252]], ![![1478, 1471, -491, 2192, 2024]], ![![6108, 6081, -2008, 9089, 8378]], ![![7175, 7143, -2354, 10684, 9841]]]
  g := ![![![-7071, -13812, -9018, 5138, 12986], ![-8208, -16067, -10510, 5948, 15132], ![-9414, -18407, -12029, 6832, 17320], ![6050, 11829, 7730, -4391, -11130], ![2293, 4487, 2934, -1662, -4225]]]
  hle1 := by decide   
  hle2 := by decide  


def P241P1 : CertificateIrreducibleZModOfList' 241 2 2 7 [219, 207, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [34, 240], [0, 1]]
 g := ![![[133, 20], [134], [214], [181], [32, 12], [59, 6], [34, 1]], ![[90, 221], [134], [214], [181], [199, 229], [22, 235], [68, 240]]]
 h' := ![![[34, 240], [154, 35], [154, 80], [5, 148], [222, 120], [93, 112], [25, 214], [0, 1]], ![[0, 1], [139, 206], [223, 161], [217, 93], [205, 121], [45, 129], [71, 27], [34, 240]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [210]]
 b := ![[], [143, 105]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N1 : CertifiedPrimeIdeal' SI241N1 241 where
  n := 2
  hpos := by decide
  P := [219, 207, 1]
  hirr := P241P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![550649, 523679, -76181, 994872, 628684]
  a := ![151, 167, -127, 88, 284]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1059997, -1214722, -76181, 994872, 628684]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI241N1 : Ideal.IsPrime I241N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI241N1 B_one_repr
lemma NI241N1 : Nat.card (O ⧸ I241N1) = 58081 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI241N1

def I241N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 590, 342, -186, -492]] i)))

def SI241N2: IdealEqSpanCertificate' Table ![![151, 590, 342, -186, -492]] 
 ![![241, 0, 0, 0, 0], ![57, 1, 0, 0, 0], ![125, 0, 1, 0, 0], ![106, 0, 0, 1, 0], ![36, 0, 0, 0, 1]] where
  M :=![![![151, 590, 342, -186, -492], ![324, 625, 350, -204, -504], ![276, 754, 433, -240, -624], ![-178, -484, -278, 155, 400], ![-86, -178, -98, 58, 141]]]
  hmulB := by decide  
  f := ![![![-4757, -4726, 1574, -7062, -6492]], ![![-1257, -1249, 416, -1866, -1716]], ![![-3349, -3328, 1107, -4974, -4572]], ![![-2520, -2504, 834, -3741, -3440]], ![![-1326, -1318, 438, -1970, -1811]]]
  g := ![![![-161, 590, 342, -186, -492], ![-163, 625, 350, -204, -504], ![-203, 754, 433, -240, -624], ![130, -484, -278, 155, 400], ![46, -178, -98, 58, 141]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI241N2 : Nat.card (O ⧸ I241N2) = 241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI241N2)

lemma isPrimeI241N2 : Ideal.IsPrime I241N2 := prime_ideal_of_norm_prime hp241.out _ NI241N2
def MulI241N0 : IdealMulLeCertificate' Table 
  ![![1718, 4097, 2324, -1319, -3346]] ![![-6949, -15930, -9018, 5138, 12986]]
  ![![-78718170, -187737805, -106520824, 60426389, 153374752]] where
 M := ![![![-78718170, -187737805, -106520824, 60426389, 153374752]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI241N1 : IdealMulLeCertificate' Table 
  ![![-78718170, -187737805, -106520824, 60426389, 153374752]] ![![151, 590, 342, -186, -492]]
  ![![241, 0, 0, 0, 0]] where
 M := ![![![-126059365828, -300643627853, -170582624520, 96766915511, 245614583168]]]
 hmul := by decide  
 g := ![![![![-523067908, -1247483933, -707811720, 401522471, 1019147648]]]]
 hle2 := by decide  


def PBC241 : ContainsPrimesAboveP 241 ![I241N0, I241N1, I241N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI241N0
    exact isPrimeI241N1
    exact isPrimeI241N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 241 (by decide) (𝕀 ⊙ MulI241N0 ⊙ MulI241N1)
instance hp251 : Fact (Nat.Prime 251) := {out := by norm_num}

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![874, 844, -1017, 149, 1146]] i)))

def SI251N0: IdealEqSpanCertificate' Table ![![874, 844, -1017, 149, 1146]] 
 ![![251, 0, 0, 0, 0], ![0, 251, 0, 0, 0], ![0, 0, 251, 0, 0], ![0, 0, 0, 251, 0], ![91, 112, 235, 222, 1]] where
  M :=![![![874, 844, -1017, 149, 1146], ![-3214, -2469, 2540, -2738, -1100], ![2088, -2566, 6283, 16204, -19704], ![6161, 7158, -9449, -3086, 13972], ![-4463, -7192, 10673, 9195, -19947]]]
  hmulB := by decide  
  f := ![![![326, 40, -1, -25, 0]], ![![-106, 221, 140, -62, -200]], ![![192, 146, 69, -44, -96]], ![![-115, -90, -47, 36, 70]], ![![149, 170, 85, -46, -117]]]
  g := ![![![-412, -508, -1077, -1013, 1146], ![386, 481, 1040, 962, -1100], ![7152, 8782, 18473, 17492, -19704], ![-5041, -6206, -13119, -12370, 13972], ![7214, 8872, 18718, 17679, -19947]]]
  hle1 := by decide   
  hle2 := by decide  


def P251P0 : CertificateIrreducibleZModOfList' 251 4 2 7 [136, 75, 55, 179, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [7, 230, 182, 158], [149, 245, 206, 222], [167, 26, 114, 122], [0, 1]]
 g := ![![[83, 129, 87, 48], [193, 43, 143, 58], [62, 243, 192], [172, 87, 219, 241], [238, 196, 240, 92], [48, 109, 72, 1], []], ![[235, 84, 7, 123, 169, 134], [133, 37, 236, 33, 57, 157], [207, 87, 152], [120, 14, 52, 84, 68, 72], [229, 109, 104, 122, 113, 170], [13, 76, 194, 12, 170, 159], [74, 50, 165, 15, 68, 98]], ![[70, 193, 203, 198, 204, 39], [241, 92, 157, 85, 243, 51], [44, 134, 49], [148, 249, 178, 194, 147, 73], [135, 87, 205, 136, 221, 114], [18, 144, 129, 225, 196, 237], [190, 106, 199, 188, 156, 209]], ![[149, 115, 154, 207, 131, 48], [18, 92, 140, 241, 62, 214], [14, 166, 119], [149, 228, 96, 27, 104, 207], [114, 226, 174, 225, 205, 85], [237, 145, 152, 181, 160, 92], [41, 75, 172, 232, 224, 114]]]
 h' := ![![[7, 230, 182, 158], [107, 57, 250, 53], [244, 222, 160, 178], [202, 238, 20, 106], [11, 176, 214, 201], [249, 150, 226, 208], [0, 0, 0, 1], [0, 1]], ![[149, 245, 206, 222], [128, 68, 98, 221], [179, 202, 130, 84], [113, 243, 191, 34], [105, 64, 11, 243], [229, 43, 91, 44], [68, 125, 233, 236], [7, 230, 182, 158]], ![[167, 26, 114, 122], [1, 30, 31, 50], [124, 7, 144, 96], [142, 82, 99, 244], [137, 141, 129, 232], [177, 146, 179, 53], [33, 173, 51, 149], [149, 245, 206, 222]], ![[0, 1], [47, 96, 123, 178], [48, 71, 68, 144], [137, 190, 192, 118], [215, 121, 148, 77], [223, 163, 6, 197], [104, 204, 218, 116], [167, 26, 114, 122]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [213, 80, 186], []]
 b := ![[], [], [1, 214, 190, 67], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI251N0 : CertifiedPrimeIdeal' SI251N0 251 where
  n := 4
  hpos := by decide
  P := [136, 75, 55, 179, 1]
  hirr := P251P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![634452041531766, 630801323116688, -206662752370802, 947456361027588, 866197065760874]
  a := ![-333, -359, 248, -250, -557]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-311511876265768, -383997091801200, -811804674128192, -762343793776440, 866197065760874]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI251N0 : Ideal.IsPrime I251N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI251N0 B_one_repr
lemma NI251N0 : Nat.card (O ⧸ I251N0) = 3969126001 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI251N0

def I251N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![326, 40, -1, -25, 0]] i)))

def SI251N1: IdealEqSpanCertificate' Table ![![326, 40, -1, -25, 0]] 
 ![![251, 0, 0, 0, 0], ![234, 1, 0, 0, 0], ![213, 0, 1, 0, 0], ![142, 0, 0, 1, 0], ![68, 0, 0, 0, 1]] where
  M :=![![![326, 40, -1, -25, 0], ![-106, 221, 140, -62, -200], ![192, 146, 69, -44, -96], ![-115, -90, -47, 36, 70], ![15, -52, -35, 21, 53]]]
  hmulB := by decide  
  f := ![![![874, 844, -1017, 149, 1146]], ![![802, 777, -938, 128, 1064]], ![![750, 706, -838, 191, 894]], ![![519, 506, -613, 72, 704]], ![![219, 200, -233, 77, 231]]]
  g := ![![![-21, 40, -1, -25, 0], ![-236, 221, 140, -62, -200], ![-143, 146, 69, -44, -96], ![84, -90, -47, 36, 70], ![52, -52, -35, 21, 53]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N1 : Nat.card (O ⧸ I251N1) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N1)

lemma isPrimeI251N1 : Ideal.IsPrime I251N1 := prime_ideal_of_norm_prime hp251.out _ NI251N1
def MulI251N0 : IdealMulLeCertificate' Table 
  ![![874, 844, -1017, 149, 1146]] ![![326, 40, -1, -25, 0]]
  ![![251, 0, 0, 0, 0]] where
 M := ![![![251, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC251 : ContainsPrimesAboveP 251 ![I251N0, I251N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI251N0
    exact isPrimeI251N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 251 (by decide) (𝕀 ⊙ MulI251N0)


lemma PB1640I5_primes (p : ℕ) :
  p ∈ Set.range ![199, 211, 223, 227, 229, 233, 239, 241, 251] ↔ Nat.Prime p ∧ 197 < p ∧ p ≤ 251 := by
  rw [← List.mem_ofFn']
  convert primes_range 197 251 (by omega)

def PB1640I5 : PrimesBelowBoundCertificateInterval O 197 251 1640 where
  m := 9
  g := ![2, 2, 3, 3, 1, 2, 2, 3, 2]
  P := ![199, 211, 223, 227, 229, 233, 239, 241, 251]
  hP := PB1640I5_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I199N0, I199N1]
    · exact ![I211N0, I211N1]
    · exact ![I223N0, I223N1, I223N2]
    · exact ![I227N0, I227N1, I227N2]
    · exact ![I229N0]
    · exact ![I233N0, I233N1]
    · exact ![I239N0, I239N1]
    · exact ![I241N0, I241N1, I241N2]
    · exact ![I251N0, I251N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC199
    · exact PBC211
    · exact PBC223
    · exact PBC227
    · exact PBC229
    · exact PBC233
    · exact PBC239
    · exact PBC241
    · exact PBC251
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![1568239201, 199]
    · exact ![9393931, 44521]
    · exact ![11089567, 223, 223]
    · exact ![11697083, 227, 227]
    · exact ![629763392149]
    · exact ![2947295521, 233]
    · exact ![13651919, 57121]
    · exact ![58081, 58081, 241]
    · exact ![3969126001, 251]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI199N0
      exact NI199N1
    · dsimp ; intro j
      fin_cases j
      exact NI211N0
      exact NI211N1
    · dsimp ; intro j
      fin_cases j
      exact NI223N0
      exact NI223N1
      exact NI223N2
    · dsimp ; intro j
      fin_cases j
      exact NI227N0
      exact NI227N1
      exact NI227N2
    · dsimp ; intro j
      fin_cases j
      exact NI229N0
    · dsimp ; intro j
      fin_cases j
      exact NI233N0
      exact NI233N1
    · dsimp ; intro j
      fin_cases j
      exact NI239N0
      exact NI239N1
    · dsimp ; intro j
      fin_cases j
      exact NI241N0
      exact NI241N1
      exact NI241N2
    · dsimp ; intro j
      fin_cases j
      exact NI251N0
      exact NI251N1
  β := ![I199N1, I223N1, I223N2, I227N1, I227N2, I233N1, I241N2, I251N1]
  Il := ![[I199N1], [], [I223N1, I223N2], [I227N1, I227N2], [], [I233N1], [], [I241N2], [I251N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
