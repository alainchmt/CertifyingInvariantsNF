
import IdealArithmetic.Examples.NF5_3_480000000_1.RI5_3_480000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5081, -1619, 3191, 849, -960]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![5081, -1619, 3191, 849, -960]] 
 ![![199, 0, 0, 0, 0], ![0, 199, 0, 0, 0], ![80, 36, 1, 0, 0], ![105, 38, 0, 1, 0], ![118, 88, 0, 0, 1]] where
  M :=![![![5081, -1619, 3191, 849, -960], ![-7680, 2623, -4936, -1187, 1587], ![6348, -1747, 3810, 1212, -987], ![-108, 694, -491, 343, 531], ![3052, 512, 965, 1324, 568]]]
  hmulB := by decide  
  f := ![![![2279, -412, -2629, -209, 630]], ![![5040, 3009, -406, -639, 3]], ![![1828, 392, -1112, -200, 249]], ![![2133, 347, -1450, -229, 330]], ![![3570, 1085, -1731, -405, 373]]]
  g := ![![![-1136, -323, 3191, 849, -960], ![1631, 431, -4936, -1187, 1587], ![-1554, -493, 3810, 1212, -987], ![-299, -208, -491, 343, 531], ![-1408, -676, 965, 1324, 568]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 2 2 7 [188, 142, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [57, 198], [0, 1]]
 g := ![![[168, 18], [130, 16], [131, 57], [49], [184], [5], [57, 1]], ![[0, 181], [47, 183], [196, 142], [49], [184], [5], [114, 198]]]
 h' := ![![[57, 198], [37, 139], [48, 195], [114, 16], [42, 192], [159, 69], [30, 76], [0, 1]], ![[0, 1], [0, 60], [19, 4], [31, 183], [41, 7], [112, 130], [183, 123], [57, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31]]
 b := ![[], [6, 115]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 2
  hpos := by decide
  P := [188, 142, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1588, 1207, -74, 689, 997]
  a := ![0, 1, 1, 0, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-917, -553, -74, 689, 997]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-649, -672, 156, -590, -556]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![-649, -672, 156, -590, -556]] 
 ![![199, 0, 0, 0, 0], ![0, 199, 0, 0, 0], ![144, 72, 1, 0, 0], ![179, 162, 0, 1, 0], ![192, 80, 0, 0, 1]] where
  M :=![![![-649, -672, 156, -590, -556], ![-4448, -2683, -164, -2990, -2326], ![-9304, -6626, 307, -6810, -5648], ![-20368, -13872, 266, -14561, -11876], ![-46144, -31576, 698, -33070, -27019]]]
  hmulB := by decide  
  f := ![![![-1327, -1232, -504, 170, 164]], ![![1312, -1181, -2804, -30, 674]], ![![-472, -1314, -1385, 110, 364]], ![![-123, -2058, -2722, 129, 692]], ![![-752, -1660, -1610, 150, 429]]]
  g := ![![![951, 644, 156, -590, -556], ![5030, 3415, -164, -2990, -2326], ![11306, 7670, 307, -6810, -5648], ![24261, 16462, 266, -14561, -11876], ![55078, 37372, 698, -33070, -27019]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P1 : CertificateIrreducibleZModOfList' 199 2 2 7 [62, 70, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [129, 198], [0, 1]]
 g := ![![[91, 61], [173, 188], [], [], [29], [63], [129, 1]], ![[0, 138], [147, 11], [], [], [29], [63], [59, 198]]]
 h' := ![![[129, 198], [20, 114], [0, 63], [62], [96], [125, 32], [161, 62], [0, 1]], ![[0, 1], [0, 85], [167, 136], [62], [96], [74, 167], [0, 137], [129, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [122]]
 b := ![[], [145, 61]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N1 : CertifiedPrimeIdeal' SI199N1 199 where
  n := 2
  hpos := by decide
  P := [62, 70, 1]
  hirr := P199P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![135945, 99894, -17532, 73046, 161306]
  a := ![3, -2, 0, -3, -61]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-207967, -117466, -17532, 73046, 161306]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N1 B_one_repr
lemma NI199N1 : Nat.card (O ⧸ I199N1) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N1

def I199N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 6, 2, 0, 0]] i)))

def SI199N2: IdealEqSpanCertificate' Table ![![7, 6, 2, 0, 0]] 
 ![![199, 0, 0, 0, 0], ![182, 1, 0, 0, 0], ![154, 0, 1, 0, 0], ![24, 0, 0, 1, 0], ![42, 0, 0, 0, 1]] where
  M :=![![![7, 6, 2, 0, 0], ![0, 9, 12, 4, 0], ![0, 4, 5, 10, 6], ![24, 8, -12, 19, 18], ![56, 36, -4, 42, 35]]]
  hmulB := by decide  
  f := ![![![769, -286, 494, 92, -132]], ![![698, -259, 448, 84, -120]], ![![598, -224, 385, 70, -102]], ![![96, -32, 60, 15, -18]], ![![158, -64, 104, 14, -25]]]
  g := ![![![-7, 6, 2, 0, 0], ![-18, 9, 12, 4, 0], ![-10, 4, 5, 10, 6], ![-4, 8, -12, 19, 18], ![-42, 36, -4, 42, 35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N2 : Nat.card (O ⧸ I199N2) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N2)

lemma isPrimeI199N2 : Ideal.IsPrime I199N2 := prime_ideal_of_norm_prime hp199.out _ NI199N2
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![5081, -1619, 3191, 849, -960]] ![![-649, -672, 156, -590, -556]]
  ![![1220487, -1678589, 1593543, -502779, -1226494]] where
 M := ![![![1220487, -1678589, 1593543, -502779, -1226494]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI199N1 : IdealMulLeCertificate' Table 
  ![![1220487, -1678589, 1593543, -502779, -1226494]] ![![7, 6, 2, 0, 0]]
  ![![199, 0, 0, 0, 0]] where
 M := ![![![-72206951, -49586223, 1204945, -51844475, -42416054]]]
 hmul := by decide  
 g := ![![![![-362849, -249177, 6055, -260525, -213146]]]]
 hle2 := by decide  


def PBC199 : ContainsPrimesAboveP 199 ![I199N0, I199N1, I199N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI199N0
    exact isPrimeI199N1
    exact isPrimeI199N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 199 (by decide) (𝕀 ⊙ MulI199N0 ⊙ MulI199N1)
instance hp211 : Fact (Nat.Prime 211) := {out := by norm_num}

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![337, 263, 64, 366, -204]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![337, 263, 64, 366, -204]] 
 ![![211, 0, 0, 0, 0], ![0, 211, 0, 0, 0], ![0, 0, 211, 0, 0], ![0, 0, 0, 211, 0], ![18, 128, 190, 203, 1]] where
  M :=![![![337, 263, 64, 366, -204], ![-1632, -985, -206, -1666, 894], ![3576, 2149, 681, 3756, -2052], ![-7392, -4387, -1504, -7546, 4161], ![10472, 6127, 1990, 10655, -5842]]]
  hmulB := by decide  
  f := ![![![19, 13, -2, 14, 12]], ![![96, 63, -2, 66, 54]], ![![216, 149, -3, 154, 126]], ![![456, 313, -4, 328, 267]], ![![698, 478, -8, 499, 407]]]
  g := ![![![19, 125, 184, 198, -204], ![-84, -547, -806, -868, 894], ![192, 1255, 1851, 1992, -2052], ![-390, -2545, -3754, -4039, 4161], ![548, 3573, 5270, 5671, -5842]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 4 2 7 [167, 201, 72, 175, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [109, 157, 22, 106], [185, 161, 177, 56], [164, 103, 12, 49], [0, 1]]
 g := ![![[84, 60, 157, 161], [199, 172, 173, 43], [183, 49, 169], [5, 41, 11], [114, 126, 170, 51], [169, 36, 1], []], ![[166, 97, 147, 198, 50, 146], [132, 108, 101, 22, 31, 97], [205, 174, 30], [110, 173, 109], [44, 56, 128, 128, 49, 168], [40, 210, 148], [98, 92, 44, 61, 21, 132]], ![[148, 83, 165, 145, 24, 99], [183, 142, 138, 43, 27, 58], [183, 49, 169], [101, 83, 169], [123, 78, 82, 137, 116, 21], [87, 147, 54], [184, 210, 36, 206, 198, 64]], ![[126, 174, 69, 75, 122, 81], [22, 85, 42, 118, 87, 30], [205, 174, 30], [87, 209, 203], [2, 82, 176, 172, 12, 78], [173, 86, 196], [208, 11, 157, 120, 98, 122]]]
 h' := ![![[109, 157, 22, 106], [105, 172, 122, 168], [98, 123, 75, 26], [203, 70, 13, 198], [163, 1, 45, 125], [51, 109, 52, 126], [0, 0, 0, 1], [0, 1]], ![[185, 161, 177, 56], [169, 48, 91, 9], [23, 64, 183, 163], [42, 51, 5, 36], [107, 67, 25, 98], [81, 49, 125, 114], [3, 195, 113, 123], [109, 157, 22, 106]], ![[164, 103, 12, 49], [116, 48, 134, 93], [17, 156, 54, 47], [163, 141, 198, 13], [19, 142, 37, 13], [44, 15, 146, 94], [15, 199, 151, 73], [185, 161, 177, 56]], ![[0, 1], [10, 154, 75, 152], [56, 79, 110, 186], [113, 160, 206, 175], [111, 1, 104, 186], [209, 38, 99, 88], [68, 28, 158, 14], [164, 103, 12, 49]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [98, 43, 166], []]
 b := ![[], [], [37, 101, 190, 95], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 4
  hpos := by decide
  P := [167, 201, 72, 175, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![107238376, 72976763, -937376, 77570188, 59609736]
  a := ![1, 0, 1, -1, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4576952, -35815495, -53681456, -56982020, 59609736]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 1982119441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 13, -2, 14, 12]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![19, 13, -2, 14, 12]] 
 ![![211, 0, 0, 0, 0], ![23, 1, 0, 0, 0], ![52, 0, 1, 0, 0], ![129, 0, 0, 1, 0], ![81, 0, 0, 0, 1]] where
  M :=![![![19, 13, -2, 14, 12], ![96, 63, -2, 66, 54], ![216, 149, -3, 154, 126], ![456, 313, -4, 328, 267], ![1040, 711, -14, 745, 608]]]
  hmulB := by decide  
  f := ![![![337, 263, 64, 366, -204]], ![![29, 24, 6, 32, -18]], ![![100, 75, 19, 108, -60]], ![![171, 140, 32, 188, -105]], ![![179, 130, 34, 191, -106]]]
  g := ![![![-14, 13, -2, 14, 12], ![-67, 63, -2, 66, 54], ![-157, 149, -3, 154, 126], ![-334, 313, -4, 328, 267], ![-758, 711, -14, 745, 608]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![337, 263, 64, 366, -204]] ![![19, 13, -2, 14, 12]]
  ![![211, 0, 0, 0, 0]] where
 M := ![![![211, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-161, -168, -85, 21, 24]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![-161, -168, -85, 21, 24]] 
 ![![223, 0, 0, 0, 0], ![0, 223, 0, 0, 0], ![70, 206, 1, 0, 0], ![75, 81, 0, 1, 0], ![157, 215, 0, 0, 1]] where
  M :=![![![-161, -168, -85, 21, 24], ![192, -147, -378, -23, 87], ![348, 136, -124, -62, 9], ![-60, 239, 387, -50, -132], ![-76, 27, 113, -99, -103]]]
  hmulB := by decide  
  f := ![![![4489, 2561, 899, 4499, -2478]], ![![-19824, -11501, -3876, -20047, 11019]], ![![-16706, -9705, -3260, -16906, 9291]], ![![-6087, -3548, -1182, -6171, 3390]], ![![-15393, -8958, -2996, -15592, 8567]]]
  g := ![![![2, 47, -85, 21, 24], ![66, 273, -378, -23, 87], ![55, 129, -124, -62, 9], ![-12, -211, 387, -50, -132], ![70, 31, 113, -99, -103]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 2 2 7 [110, 154, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [69, 222], [0, 1]]
 g := ![![[46, 148], [116, 64], [142, 152], [75, 177], [43, 69], [132], [69, 1]], ![[0, 75], [72, 159], [149, 71], [23, 46], [121, 154], [132], [138, 222]]]
 h' := ![![[69, 222], [174, 172], [213, 215], [1, 179], [176, 20], [39, 31], [215, 191], [0, 1]], ![[0, 1], [0, 51], [107, 8], [87, 44], [218, 203], [171, 192], [14, 32], [69, 222]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [138]]
 b := ![[], [184, 69]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 2
  hpos := by decide
  P := [110, 154, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![12153, 9618, -4925, 1024, 36440]
  a := ![1, -4, -2, -5, 28]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-24399, -30912, -4925, 1024, 36440]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 49729 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-113, -81, 4, -83, -69]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![-113, -81, 4, -83, -69]] 
 ![![223, 0, 0, 0, 0], ![52, 1, 0, 0, 0], ![209, 0, 1, 0, 0], ![115, 0, 0, 1, 0], ![60, 0, 0, 0, 1]] where
  M :=![![![-113, -81, 4, -83, -69], ![-552, -371, 4, -392, -318], ![-1272, -873, 21, -913, -747], ![-2712, -1851, 38, -1941, -1584], ![-6160, -4207, 88, -4410, -3601]]]
  hmulB := by decide  
  f := ![![![1057, 783, 154, -119, -69]], ![![244, 187, 44, -28, -18]], ![![983, 732, 149, -110, -66]], ![![541, 396, 72, -62, -33]], ![![284, 209, 40, -30, -19]]]
  g := ![![![76, -81, 4, -83, -69], ![368, -371, 4, -392, -318], ![850, -873, 21, -913, -747], ![1811, -1851, 38, -1941, -1584], ![4114, -4207, 88, -4410, -3601]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1

def I223N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2953, -603, -3503, -272, 843]] i)))

def SI223N2: IdealEqSpanCertificate' Table ![![2953, -603, -3503, -272, 843]] 
 ![![223, 0, 0, 0, 0], ![71, 1, 0, 0, 0], ![44, 0, 1, 0, 0], ![75, 0, 0, 1, 0], ![87, 0, 0, 0, 1]] where
  M :=![![![2953, -603, -3503, -272, 843], ![6744, 3937, -662, -833, 27], ![108, 3525, 4770, -151, -1236], ![-8316, -2544, 4007, 936, -858], ![-2740, -364, 1975, 291, -451]]]
  hmulB := by decide  
  f := ![![![-127289, -76878, -23429, -131564, 71973]], ![![-37945, -22949, -6969, -39249, 21468]], ![![-30904, -18570, -5734, -31853, 17436]], ![![-31161, -19035, -5632, -32409, 17706]], ![![-66109, -39625, -12314, -68046, 37259]]]
  g := ![![![659, -603, -3503, -272, 843], ![-823, 3937, -662, -833, 27], ![-1530, 3525, 4770, -151, -1236], ![2, -2544, 4007, 936, -858], ![-208, -364, 1975, 291, -451]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N2 : Nat.card (O ⧸ I223N2) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N2)

lemma isPrimeI223N2 : Ideal.IsPrime I223N2 := prime_ideal_of_norm_prime hp223.out _ NI223N2

def I223N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1105, 607, -161, -135, 18]] i)))

def SI223N3: IdealEqSpanCertificate' Table ![![1105, 607, -161, -135, 18]] 
 ![![223, 0, 0, 0, 0], ![134, 1, 0, 0, 0], ![165, 0, 1, 0, 0], ![28, 0, 0, 1, 0], ![177, 0, 0, 0, 1]] where
  M :=![![![1105, 607, -161, -135, 18], ![144, 1169, 1484, -61, -387], ![-1548, -123, 1230, 160, -285], ![-1212, -1536, -1025, 183, 291], ![-612, -526, -173, 82, 58]]]
  hmulB := by decide  
  f := ![![![3799, 100, 1543, 1347, 312]], ![![2294, 85, 916, 827, 207]], ![![2889, 114, 1149, 1045, 267]], ![![616, 109, 191, 270, 120]], ![![3333, 293, 1222, 1294, 433]]]
  g := ![![![-238, 607, -161, -135, 18], ![-1485, 1169, 1484, -61, -387], ![-637, -123, 1230, 160, -285], ![1422, -1536, -1025, 183, 291], ![385, -526, -173, 82, 58]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N3 : Nat.card (O ⧸ I223N3) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N3)

lemma isPrimeI223N3 : Ideal.IsPrime I223N3 := prime_ideal_of_norm_prime hp223.out _ NI223N3
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![-161, -168, -85, 21, 24]] ![![-113, -81, 4, -83, -69]]
  ![![14257, 9735, -191, 10223, 8340]] where
 M := ![![![14257, 9735, -191, 10223, 8340]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI223N1 : IdealMulLeCertificate' Table 
  ![![14257, 9735, -191, 10223, 8340]] ![![2953, -603, -3503, -272, 843]]
  ![![-132935, 13377, 137150, 37350, -15102]] where
 M := ![![![-132935, 13377, 137150, 37350, -15102]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI223N2 : IdealMulLeCertificate' Table 
  ![![-132935, 13377, 137150, 37350, -15102]] ![![1105, 607, -161, -135, 18]]
  ![![223, 0, 0, 0, 0]] where
 M := ![![![-393300863, -131349230, 174277399, 44670914, -36664545]]]
 hmul := by decide  
 g := ![![![![-1763681, -589010, 781513, 200318, -164415]]]]
 hle2 := by decide  


def PBC223 : ContainsPrimesAboveP 223 ![I223N0, I223N1, I223N2, I223N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI223N0
    exact isPrimeI223N1
    exact isPrimeI223N2
    exact isPrimeI223N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 223 (by decide) (𝕀 ⊙ MulI223N0 ⊙ MulI223N1 ⊙ MulI223N2)
instance hp227 : Fact (Nat.Prime 227) := {out := by norm_num}

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1137, 371, -705, -188, 215]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![-1137, 371, -705, -188, 215]] 
 ![![227, 0, 0, 0, 0], ![0, 227, 0, 0, 0], ![0, 0, 227, 0, 0], ![0, 0, 0, 227, 0], ![38, 215, 2, 167, 1]] where
  M :=![![![-1137, 371, -705, -188, 215], ![1720, -579, 1118, 283, -349], ![-1396, 405, -862, -245, 250], ![140, -92, 91, -6, -68], ![-492, 12, -229, -167, -1]]]
  hmulB := by decide  
  f := ![![![-3, -4, -3, 0, 1]], ![![8, -1, -8, 1, 1]], ![![4, 2, -2, -5, 2]], ![![4, 9, 11, 7, -7]], ![![10, 5, 0, 6, -4]]]
  g := ![![![-41, -202, -5, -159, 215], ![66, 328, 8, 258, -349], ![-48, -235, -6, -185, 250], ![12, 64, 1, 50, -68], ![-2, 1, -1, 0, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 4 2 7 [75, 123, 129, 153, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [127, 69, 179, 61], [71, 128, 115, 52], [103, 29, 160, 114], [0, 1]]
 g := ![![[77, 13, 79, 23], [69, 174, 89, 75], [170, 9, 43], [40, 118, 161], [38, 208, 57], [109, 126, 74, 1], []], ![[48, 135, 149, 11, 209, 140], [82, 46, 185, 63, 117, 164], [91, 43, 1], [117, 34, 122], [56, 29, 161], [134, 109, 97, 124, 187, 187], [212, 137, 77, 27, 79, 208]], ![[188, 185, 179, 82, 89, 98], [10, 82, 161, 18, 159, 39], [171, 64, 53], [176, 150, 219], [89, 45, 84], [143, 12, 56, 223, 202, 56], [29, 89, 111, 24, 130, 95]], ![[53, 93, 220, 71, 112, 5], [225, 161, 5, 71, 156, 215], [114, 136, 21], [186, 78, 155], [10, 89, 100], [152, 117, 150, 66, 28, 94], [152, 169, 93, 215, 186, 142]]]
 h' := ![![[127, 69, 179, 61], [46, 93, 49, 134], [135, 27, 173, 204], [20, 109, 12, 161], [110, 190, 101, 36], [224, 70, 76, 114], [0, 0, 0, 1], [0, 1]], ![[71, 128, 115, 52], [105, 94, 210, 46], [174, 200, 14, 186], [125, 73, 98, 1], [71, 139, 68, 24], [171, 157, 143, 191], [152, 183, 38, 147], [127, 69, 179, 61]], ![[103, 29, 160, 114], [34, 135, 17, 111], [112, 46, 105, 202], [15, 53, 11, 31], [220, 192, 141, 30], [174, 210, 17, 159], [27, 88, 133, 221], [71, 128, 115, 52]], ![[0, 1], [161, 132, 178, 163], [31, 181, 162, 89], [78, 219, 106, 34], [33, 160, 144, 137], [97, 17, 218, 217], [126, 183, 56, 85], [103, 29, 160, 114]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [103, 164, 207], []]
 b := ![[], [], [131, 95, 31, 175], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 4
  hpos := by decide
  P := [75, 123, 129, 153, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1527903911, -822682774, -447531136, -1773794786, 1693469622]
  a := ![-1, 7, 6, 9, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-290219161, -1607571152, -16891940, -1253670580, 1693469622]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 2655237841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 4, 3, 0, -1]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![3, 4, 3, 0, -1]] 
 ![![227, 0, 0, 0, 0], ![179, 1, 0, 0, 0], ![210, 0, 1, 0, 0], ![70, 0, 0, 1, 0], ![208, 0, 0, 0, 1]] where
  M :=![![![3, 4, 3, 0, -1], ![-8, 1, 8, -1, -1], ![-4, -2, 2, 5, -2], ![-4, -9, -11, -7, 7], ![12, 5, -1, 12, -4]]]
  hmulB := by decide  
  f := ![![![1137, -371, 705, 188, -215]], ![![889, -290, 551, 147, -168]], ![![1058, -345, 656, 175, -200]], ![![350, -114, 217, 58, -66]], ![![1044, -340, 647, 173, -197]]]
  g := ![![![-5, 4, 3, 0, -1], ![-7, 1, 8, -1, -1], ![0, -2, 2, 5, -2], ![13, -9, -11, -7, 7], ![-3, 5, -1, 12, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N1 : Nat.card (O ⧸ I227N1) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N1)

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := prime_ideal_of_norm_prime hp227.out _ NI227N1
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![-1137, 371, -705, -188, 215]] ![![3, 4, 3, 0, -1]]
  ![![227, 0, 0, 0, 0]] where
 M := ![![![-227, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC227 : ContainsPrimesAboveP 227 ![I227N0, I227N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI227N0
    exact isPrimeI227N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 227 (by decide) (𝕀 ⊙ MulI227N0)
instance hp229 : Fact (Nat.Prime 229) := {out := by norm_num}

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1801, 978, -1390, -80, 654]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![-1801, 978, -1390, -80, 654]] 
 ![![229, 0, 0, 0, 0], ![0, 229, 0, 0, 0], ![0, 0, 229, 0, 0], ![0, 0, 0, 229, 0], ![6, 12, 56, 51, 1]] where
  M :=![![![-1801, 978, -1390, -80, 654], ![5232, 159, 2116, 1878, 414], ![1656, 3770, -1719, 2626, 3024], ![9480, 6136, 86, 6613, 5244], ![19992, 14336, -730, 14670, 12263]]]
  hmulB := by decide  
  f := ![![![-157, -110, -10, 20, 6]], ![![48, -157, -260, 2, 66]], ![![264, 58, -159, -30, 36]], ![![120, 236, 218, -19, -60]], ![![90, 56, -4, -11, -1]]]
  g := ![![![-25, -30, -166, -146, 654], ![12, -21, -92, -84, 414], ![-72, -142, -747, -662, 3024], ![-96, -248, -1282, -1139, 5244], ![-234, -580, -3002, -2667, 12263]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 4 2 7 [201, 182, 128, 125, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [193, 215, 224, 147], [59, 183, 95, 77], [81, 59, 139, 5], [0, 1]]
 g := ![![[195, 87, 170, 25], [185, 225, 224], [212, 9, 82, 11], [24, 160, 161], [91, 195, 43], [3, 154, 104, 1], []], ![[203, 85, 196, 59, 109, 185], [53, 70, 85], [121, 29, 135, 57, 60, 100], [110, 49, 16], [153, 175, 183], [13, 227, 211, 67, 109, 17], [133, 38, 76, 125, 144, 64]], ![[109, 211, 184, 129, 63, 131], [183, 220, 220], [151, 62, 163, 4, 97, 35], [6, 132, 176], [30, 156, 147], [27, 25, 68, 52, 183, 166], [85, 111, 190, 123, 149, 136]], ![[140, 181, 164, 135, 156, 159], [212, 23, 100], [115, 88, 142, 53, 225, 15], [142, 228, 148], [67, 6, 149], [0, 184, 68, 161, 18, 193], [203, 46, 108, 103, 67, 125]]]
 h' := ![![[193, 215, 224, 147], [8, 62, 14, 224], [211, 154, 106, 37], [181, 162, 45, 34], [215, 80, 97, 42], [84, 102, 148, 172], [0, 0, 0, 1], [0, 1]], ![[59, 183, 95, 77], [127, 40, 176, 154], [186, 22, 193, 90], [112, 86, 64, 12], [3, 69, 113, 4], [191, 116, 202, 99], [120, 57, 97, 189], [193, 215, 224, 147]], ![[81, 59, 139, 5], [25, 54, 21, 178], [54, 184, 71, 92], [71, 92, 4, 25], [210, 42, 78, 136], [61, 197, 35, 39], [56, 68, 60, 132], [59, 183, 95, 77]], ![[0, 1], [166, 73, 18, 131], [118, 98, 88, 10], [46, 118, 116, 158], [119, 38, 170, 47], [103, 43, 73, 148], [120, 104, 72, 136], [81, 59, 139, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [136, 92, 45], []]
 b := ![[], [], [181, 106, 70, 47], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 4
  hpos := by decide
  P := [201, 182, 128, 125, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6384263607, -3734089288, -1239613536, -6500550116, 3606460644]
  a := ![0, -12, 0, -22, 6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-122371299, -205290904, -887342400, -831572240, 3606460644]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 2750058481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 110, 10, -20, -6]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![157, 110, 10, -20, -6]] 
 ![![229, 0, 0, 0, 0], ![75, 1, 0, 0, 0], ![50, 0, 1, 0, 0], ![34, 0, 0, 1, 0], ![212, 0, 0, 0, 1]] where
  M :=![![![157, 110, 10, -20, -6], ![-48, 157, 260, -2, -66], ![-264, -58, 159, 30, -36], ![-120, -236, -218, 19, 60], ![-72, -84, -50, 14, 13]]]
  hmulB := by decide  
  f := ![![![1801, -978, 1390, 80, -654]], ![![567, -321, 446, 18, -216]], ![![386, -230, 311, 6, -156]], ![![226, -172, 206, -17, -120]], ![![1580, -968, 1290, 10, -659]]]
  g := ![![![-29, 110, 10, -20, -6], ![-47, 157, 260, -2, -66], ![12, -58, 159, 30, -36], ![66, -236, -218, 19, 60], ![24, -84, -50, 14, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N1 : Nat.card (O ⧸ I229N1) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N1)

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := prime_ideal_of_norm_prime hp229.out _ NI229N1
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![-1801, 978, -1390, -80, 654]] ![![157, 110, 10, -20, -6]]
  ![![229, 0, 0, 0, 0]] where
 M := ![![![-229, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC229 : ContainsPrimesAboveP 229 ![I229N0, I229N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI229N0
    exact isPrimeI229N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 229 (by decide) (𝕀 ⊙ MulI229N0)
instance hp233 : Fact (Nat.Prime 233) := {out := by norm_num}

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-247, 86, -160, -36, 48]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![-247, 86, -160, -36, 48]] 
 ![![233, 0, 0, 0, 0], ![0, 233, 0, 0, 0], ![0, 0, 233, 0, 0], ![69, 213, 206, 1, 0], ![100, 113, 190, 0, 1]] where
  M :=![![![-247, 86, -160, -36, 48], ![384, -131, 244, 52, -60], ![-240, 138, -183, 8, 48], ![0, -30, 8, -45, 66], ![144, 166, -28, 182, 11]]]
  hmulB := by decide  
  f := ![![![97, 58, -8, -12, 0]], ![![0, 101, 140, -4, -36]], ![![-144, -18, 105, 16, -24]], ![![-99, 93, 218, 7, -54]], ![![-76, 59, 150, 6, -37]]]
  g := ![![![-11, 10, -8, -36, 48], ![12, -19, 4, 52, -60], ![-24, -30, -47, 8, 48], ![-15, 9, -14, -45, 66], ![-58, -171, -170, 182, 11]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 3 2 7 [197, 163, 210, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [196, 187, 69], [60, 45, 164], [0, 1]]
 g := ![![[109, 137, 38], [43, 58], [172, 30], [200, 82, 109], [92, 16], [222, 9, 63], [1]], ![[165, 113, 21, 39], [99, 25], [36, 187], [11, 7, 180, 97], [101, 169], [188, 110, 74, 191], [208, 215, 25, 212]], ![[38, 181, 10, 61], [181, 104], [194, 28], [191, 11, 57, 88], [75, 56], [165, 19, 136, 147], [139, 215, 138, 21]]]
 h' := ![![[196, 187, 69], [48, 142, 182], [197, 30, 161], [210, 163, 27], [57, 196, 80], [70, 151, 229], [36, 70, 23], [0, 1]], ![[60, 45, 164], [73, 145, 47], [2, 1, 228], [156, 110, 113], [21, 64, 115], [87, 56, 220], [173, 206, 40], [196, 187, 69]], ![[0, 1], [159, 179, 4], [213, 202, 77], [174, 193, 93], [104, 206, 38], [151, 26, 17], [120, 190, 170], [60, 45, 164]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [93, 140], []]
 b := ![[], [111, 101, 52], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 3
  hpos := by decide
  P := [197, 163, 210, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![343579, 112349, 287800, 634840, -1321502]
  a := ![13, 5, 5, 6, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![380643, 61035, 517580, 634840, -1321502]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 12649337 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-529, -360, 9, -378, -309]] i)))

def SI233N1: IdealEqSpanCertificate' Table ![![-529, -360, 9, -378, -309]] 
 ![![233, 0, 0, 0, 0], ![18, 1, 0, 0, 0], ![71, 0, 1, 0, 0], ![51, 0, 0, 1, 0], ![75, 0, 0, 0, 1]] where
  M :=![![![-529, -360, 9, -378, -309], ![-2472, -1687, 36, -1767, -1443], ![-5772, -3942, 80, -4131, -3372], ![-12252, -8367, 171, -8773, -7161], ![-27852, -19017, 393, -19938, -16276]]]
  hmulB := by decide  
  f := ![![![-2057, 99, -1035, -828, 609]], ![![-138, 11, -72, -51, 39]], ![![-659, 18, -325, -279, 201]], ![![-399, 51, -216, -130, 105]], ![![-735, -9, -348, -339, 236]]]
  g := ![![![205, -360, 9, -378, -309], ![960, -1687, 36, -1767, -1443], ![2245, -3942, 80, -4131, -3372], ![4767, -8367, 171, -8773, -7161], ![10833, -19017, 393, -19938, -16276]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N1 : Nat.card (O ⧸ I233N1) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N1)

lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := prime_ideal_of_norm_prime hp233.out _ NI233N1

def I233N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -19, -19, 6, 3]] i)))

def SI233N2: IdealEqSpanCertificate' Table ![![-1, -19, -19, 6, 3]] 
 ![![233, 0, 0, 0, 0], ![36, 1, 0, 0, 0], ![51, 0, 1, 0, 0], ![229, 0, 0, 1, 0], ![15, 0, 0, 0, 1]] where
  M :=![![![-1, -19, -19, 6, 3], ![24, -11, -50, -23, 21], ![84, 51, 12, 35, -24], ![-108, -24, 41, -78, 30], ![108, 76, 41, 113, -67]]]
  hmulB := by decide  
  f := ![![![-54233, -37046, 781, -38832, -31707]], ![![-9468, -6467, 136, -6779, -5535]], ![![-14415, -9846, 207, -10321, -8427]], ![![-58705, -40099, 844, -42033, -34320]], ![![-15771, -10769, 224, -11290, -9217]]]
  g := ![![![1, -19, -19, 6, 3], ![34, -11, -50, -23, 21], ![-43, 51, 12, 35, -24], ![69, -24, 41, -78, 30], ![-127, 76, 41, 113, -67]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N2 : Nat.card (O ⧸ I233N2) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N2)

lemma isPrimeI233N2 : Ideal.IsPrime I233N2 := prime_ideal_of_norm_prime hp233.out _ NI233N2
def MulI233N0 : IdealMulLeCertificate' Table 
  ![![-247, 86, -160, -36, 48]] ![![-529, -360, 9, -378, -309]]
  ![![-54233, -37046, 781, -38832, -31707]] where
 M := ![![![-54233, -37046, 781, -38832, -31707]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI233N1 : IdealMulLeCertificate' Table 
  ![![-54233, -37046, 781, -38832, -31707]] ![![-1, -19, -19, 6, 3]]
  ![![233, 0, 0, 0, 0]] where
 M := ![![![233, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC233 : ContainsPrimesAboveP 233 ![I233N0, I233N1, I233N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI233N0
    exact isPrimeI233N1
    exact isPrimeI233N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 233 (by decide) (𝕀 ⊙ MulI233N0 ⊙ MulI233N1)
instance hp239 : Fact (Nat.Prime 239) := {out := by norm_num}

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, -699, -1030, -6, 246]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![73, -699, -1030, -6, 246]] 
 ![![239, 0, 0, 0, 0], ![0, 239, 0, 0, 0], ![0, 0, 239, 0, 0], ![0, 0, 0, 239, 0], ![147, 105, 126, 204, 1]] where
  M :=![![![73, -699, -1030, -6, 246], ![1968, 279, -1386, -332, 228], ![912, 1027, 611, -422, -384], ![-2520, -127, 2142, -356, -939], ![-2080, -837, 812, -1155, -1162]]]
  hmulB := by decide  
  f := ![![![-265, 79, -164, -50, 54]], ![![432, -109, 258, 100, -96]], ![![-384, 55, -209, -128, 102]], ![![192, 77, 54, 162, -93]], ![![-13, 95, -52, 83, -34]]]
  g := ![![![-151, -111, -134, -210, 246], ![-132, -99, -126, -196, 228], ![240, 173, 205, 326, -384], ![567, 412, 504, 800, -939], ![706, 507, 616, 987, -1162]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 4 2 7 [125, 206, 27, 34, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [216, 30, 106, 119], [183, 225, 125, 38], [45, 222, 8, 82], [0, 1]]
 g := ![![[178, 81, 89, 166], [209, 18, 173, 127], [205, 217, 187, 174], [58, 110, 58, 202], [60, 201, 187], [88, 173, 205, 1], []], ![[213, 113, 122, 209, 96, 74], [139, 61, 160, 224, 42, 74], [200, 59, 188, 207, 222, 111], [227, 215, 167, 216, 86, 178], [199, 168, 200], [85, 117, 47, 137, 53, 214], [101, 159, 127, 12, 24, 209]], ![[192, 108, 89, 62, 41, 205], [232, 205, 149, 91, 114, 141], [94, 50, 118, 143, 112, 21], [11, 229, 207, 167, 97, 152], [188, 131, 153], [98, 60, 185, 222, 53, 35], [15, 200, 25, 182, 151, 141]], ![[183, 48, 167, 165, 212, 140], [218, 6, 142, 208, 114, 23], [103, 233, 223, 198, 9, 158], [125, 80, 213, 67, 89, 103], [58, 135, 108], [212, 23, 166, 143, 200, 37], [192, 120, 182, 41, 221, 234]]]
 h' := ![![[216, 30, 106, 119], [165, 181, 9, 199], [187, 141, 138, 102], [159, 32, 118, 37], [184, 30, 131, 218], [233, 160, 174, 172], [0, 0, 0, 1], [0, 1]], ![[183, 225, 125, 38], [73, 145, 213, 42], [67, 75, 93, 197], [168, 147, 167, 223], [77, 75, 133, 220], [88, 77, 229, 34], [64, 237, 35, 222], [216, 30, 106, 119]], ![[45, 222, 8, 82], [213, 220, 235, 118], [202, 113, 159, 38], [75, 40, 17, 157], [32, 96, 165, 2], [189, 24, 171, 191], [86, 89, 137, 33], [183, 225, 125, 38]], ![[0, 1], [50, 171, 21, 119], [232, 149, 88, 141], [112, 20, 176, 61], [100, 38, 49, 38], [186, 217, 143, 81], [205, 152, 67, 222], [45, 222, 8, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [163, 30, 93], []]
 b := ![[], [], [48, 5, 3, 29], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 4
  hpos := by decide
  P := [125, 206, 27, 34, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-436191, -211185, -179332, -582553, 769071]
  a := ![-1, -2, 0, -3, 0]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-474852, -338760, -406202, -658883, 769071]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N0 B_one_repr
lemma NI239N0 : Nat.card (O ⧸ I239N0) = 3262808641 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N0

def I239N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![265, -79, 164, 50, -54]] i)))

def SI239N1: IdealEqSpanCertificate' Table ![![265, -79, 164, 50, -54]] 
 ![![239, 0, 0, 0, 0], ![104, 1, 0, 0, 0], ![89, 0, 1, 0, 0], ![100, 0, 0, 1, 0], ![166, 0, 0, 0, 1]] where
  M :=![![![265, -79, 164, 50, -54], ![-432, 109, -258, -100, 96], ![384, -55, 209, 128, -102], ![-192, -77, -54, -162, 93], ![296, 101, 92, 233, -136]]]
  hmulB := by decide  
  f := ![![![-73, 699, 1030, 6, -246]], ![![-40, 303, 454, 4, -108]], ![![-31, 256, 381, 4, -90]], ![![-20, 293, 422, 4, -99]], ![![-42, 489, 712, 9, -166]]]
  g := ![![![-9, -79, 164, 50, -54], ![22, 109, -258, -100, 96], ![-35, -55, 209, 128, -102], ![56, -77, -54, -162, 93], ![-80, 101, 92, 233, -136]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N1 : Nat.card (O ⧸ I239N1) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N1)

lemma isPrimeI239N1 : Ideal.IsPrime I239N1 := prime_ideal_of_norm_prime hp239.out _ NI239N1
def MulI239N0 : IdealMulLeCertificate' Table 
  ![![73, -699, -1030, -6, 246]] ![![265, -79, 164, 50, -54]]
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

def I241N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-92809, 30101, -58624, -15215, 17933]] i)))

def SI241N0: IdealEqSpanCertificate' Table ![![-92809, 30101, -58624, -15215, 17933]] 
 ![![241, 0, 0, 0, 0], ![0, 241, 0, 0, 0], ![167, 228, 1, 0, 0], ![2, 156, 0, 1, 0], ![96, 30, 0, 0, 1]] where
  M :=![![![-92809, 30101, -58624, -15215, 17933], ![143464, -46553, 90632, 23498, -27712], ![-110848, 36019, -70051, -18109, 21391], ![13832, -4641, 8812, 2123, -2612], ![-28432, 9435, -18062, -4460, 5405]]]
  hmulB := by decide  
  f := ![![![-6985, -2913, 2294, 815, -445]], ![![-3560, -7731, -7456, 658, 2000]], ![![-8175, -9336, -5499, 1184, 1592]], ![![-2322, -4991, -4792, 427, 1286]], ![![-3208, -2111, -14, 404, 71]]]
  g := ![![![33221, 63203, -58624, -15215, 17933], ![-51364, -97697, 90632, 23498, -27712], ![39711, 75481, -70051, -18109, 21391], ![-5026, -9405, 8812, 2123, -2612], ![10282, 19341, -18062, -4460, 5405]]]
  hle1 := by decide   
  hle2 := by decide  


def P241P0 : CertificateIrreducibleZModOfList' 241 2 2 7 [120, 125, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [116, 240], [0, 1]]
 g := ![![[232, 239], [154], [16], [125], [162, 54], [236, 54], [116, 1]], ![[0, 2], [154], [16], [125], [160, 187], [234, 187], [232, 240]]]
 h' := ![![[116, 240], [171, 38], [24, 201], [237, 237], [81, 208], [118, 160], [58, 81], [0, 1]], ![[0, 1], [0, 203], [204, 40], [14, 4], [109, 33], [121, 81], [55, 160], [116, 240]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [165]]
 b := ![[], [35, 203]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 2
  hpos := by decide
  P := [120, 125, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-840, -1349, 708, -2537, 1107]
  a := ![3, -4, 7, -8, 0]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-914, 829, 708, -2537, 1107]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI241N0 : Ideal.IsPrime I241N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI241N0 B_one_repr
lemma NI241N0 : Nat.card (O ⧸ I241N0) = 58081 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI241N0

def I241N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15, -28, -51, 4, 11]] i)))

def SI241N1: IdealEqSpanCertificate' Table ![![15, -28, -51, 4, 11]] 
 ![![241, 0, 0, 0, 0], ![0, 241, 0, 0, 0], ![177, 185, 1, 0, 0], ![31, 86, 0, 1, 0], ![22, 79, 0, 0, 1]] where
  M :=![![![15, -28, -51, 4, 11], ![88, 15, -64, -29, 23], ![92, 84, 44, 31, -32], ![-172, -35, 85, -69, 19], ![84, 75, 59, 112, -70]]]
  hmulB := by decide  
  f := ![![![831, -287, 537, 126, -175]], ![![-1400, 367, -826, -277, 203]], ![![-461, 69, -237, -120, 26]], ![![-395, 93, -226, -84, 49]], ![![-386, 91, -221, -82, 48]]]
  g := ![![![36, 34, -51, 4, 11], ![49, 52, -64, -29, 23], ![-33, -34, 44, 31, -32], ![-56, -47, 85, -69, 19], ![-51, -62, 59, 112, -70]]]
  hle1 := by decide   
  hle2 := by decide  


def P241P1 : CertificateIrreducibleZModOfList' 241 2 2 7 [212, 221, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [20, 240], [0, 1]]
 g := ![![[9, 108], [141], [50], [212], [105, 49], [2, 158], [20, 1]], ![[0, 133], [141], [50], [212], [121, 192], [29, 83], [40, 240]]]
 h' := ![![[20, 240], [213, 146], [170, 158], [155, 131], [153, 137], [58, 7], [98, 188], [0, 1]], ![[0, 1], [0, 95], [197, 83], [124, 110], [1, 104], [198, 234], [2, 53], [20, 240]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [170]]
 b := ![[], [114, 85]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N1 : CertifiedPrimeIdeal' SI241N1 241 where
  n := 2
  hpos := by decide
  P := [212, 221, 1]
  hirr := P241P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-846, -1426, -1621, -3107, 5638]
  a := ![1, -4, -4, -5, 10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1072, 499, -1621, -3107, 5638]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI241N1 : Ideal.IsPrime I241N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI241N1 B_one_repr
lemma NI241N1 : Nat.card (O ⧸ I241N1) = 58081 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI241N1

def I241N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, -34, -41, 8, 15]] i)))

def SI241N2: IdealEqSpanCertificate' Table ![![-7, -34, -41, 8, 15]] 
 ![![241, 0, 0, 0, 0], ![138, 1, 0, 0, 0], ![118, 0, 1, 0, 0], ![224, 0, 0, 1, 0], ![178, 0, 0, 0, 1]] where
  M :=![![![-7, -34, -41, 8, 15], ![120, 19, -84, 15, 39], ![156, 108, 4, 45, 42], ![108, 153, 105, 121, 69], ![364, 275, 31, 266, 208]]]
  hmulB := by decide  
  f := ![![![-13303, 3251, -7889, -3178, 2997]], ![![-7518, 1849, -4464, -1785, 1689]], ![![-6622, 1583, -3910, -1615, 1506]], ![![-12260, 3076, -7309, -2854, 2730]], ![![-9978, 2326, -5863, -2489, 2293]]]
  g := ![![![21, -34, -41, 8, 15], ![-12, 19, -84, 15, 39], ![-136, 108, 4, 45, 42], ![-302, 153, 105, 121, 69], ![-572, 275, 31, 266, 208]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI241N2 : Nat.card (O ⧸ I241N2) = 241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI241N2)

lemma isPrimeI241N2 : Ideal.IsPrime I241N2 := prime_ideal_of_norm_prime hp241.out _ NI241N2
def MulI241N0 : IdealMulLeCertificate' Table 
  ![![-92809, 30101, -58624, -15215, 17933]] ![![15, -28, -51, 4, 11]]
  ![![-13303, 3251, -7889, -3178, 2997]] where
 M := ![![![-13303, 3251, -7889, -3178, 2997]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI241N1 : IdealMulLeCertificate' Table 
  ![![-13303, 3251, -7889, -3178, 2997]] ![![-7, -34, -41, 8, 15]]
  ![![241, 0, 0, 0, 0]] where
 M := ![![![241, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 101, 122, -35, -19]] i)))

def SI251N0: IdealEqSpanCertificate' Table ![![11, 101, 122, -35, -19]] 
 ![![251, 0, 0, 0, 0], ![0, 251, 0, 0, 0], ![0, 0, 251, 0, 0], ![114, 247, 106, 1, 0], ![14, 187, 155, 0, 1]] where
  M :=![![![11, 101, 122, -35, -19], ![-152, 73, 272, 146, -124], ![-496, -323, -73, -235, 157], ![704, 189, -224, 521, -212], ![-712, -495, -254, -752, 443]]]
  hmulB := by decide  
  f := ![![![1681, -543, 1060, 277, -323]], ![![-2584, 849, -1640, -418, 508]], ![![2032, -633, 1267, 347, -373]], ![![-922, 322, -598, -139, 196]], ![![-574, 211, -379, -81, 130]]]
  g := ![![![17, 49, 27, -35, -19], ![-60, -51, 16, 146, -124], ![96, 113, 2, -235, 157], ![-222, -354, -90, 521, -212], ![314, 408, 43, -752, 443]]]
  hle1 := by decide   
  hle2 := by decide  


def P251P0 : CertificateIrreducibleZModOfList' 251 3 2 7 [213, 45, 105, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [156, 34, 136], [241, 216, 115], [0, 1]]
 g := ![![[123, 183, 214], [139, 233, 155], [168, 118], [200, 149, 118], [224, 201, 21], [234, 150, 232], [1]], ![[19, 17, 23, 160], [247, 70, 196, 96], [35, 112], [139, 184, 229, 33], [71, 234, 81, 87], [31, 169, 200, 61], [178, 170, 229, 185]], ![[50, 177, 56, 161], [106, 63, 163, 124], [212, 86], [31, 197, 38, 13], [24, 22, 48, 113], [172, 83, 8, 17], [70, 41, 5, 66]]]
 h' := ![![[156, 34, 136], [11, 210, 88], [240, 219, 197], [70, 158, 143], [229, 222, 143], [107, 128, 180], [38, 206, 146], [0, 1]], ![[241, 216, 115], [27, 242, 129], [144, 53, 48], [123, 124, 168], [226, 41, 87], [241, 214, 64], [28, 89, 65], [156, 34, 136]], ![[0, 1], [230, 50, 34], [44, 230, 6], [219, 220, 191], [240, 239, 21], [45, 160, 7], [154, 207, 40], [241, 216, 115]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [193, 242], []]
 b := ![[], [187, 86, 216], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI251N0 : CertifiedPrimeIdeal' SI251N0 251 where
  n := 3
  hpos := by decide
  P := [213, 45, 105, 1]
  hirr := P251P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2281, 1277, -1381, 207, 5595]
  a := ![4, 1, -1, 2, 0]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-397, -4367, -3548, 207, 5595]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI251N0 : Ideal.IsPrime I251N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI251N0 B_one_repr
lemma NI251N0 : Nat.card (O ⧸ I251N0) = 15813251 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI251N0

def I251N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5827, 3398, 1131, 5909, -3246]] i)))

def SI251N1: IdealEqSpanCertificate' Table ![![5827, 3398, 1131, 5909, -3246]] 
 ![![251, 0, 0, 0, 0], ![101, 1, 0, 0, 0], ![45, 0, 1, 0, 0], ![187, 0, 0, 1, 0], ![189, 0, 0, 0, 1]] where
  M :=![![![5827, 3398, 1131, 5909, -3246], ![-25968, -15181, -5022, -26369, 14481], ![57924, 33892, 11188, 58846, -32313], ![-116268, -68059, -22443, -118146, 64872], ![164196, 96113, 31695, 166847, -91613]]]
  hmulB := by decide  
  f := ![![![2081, -595, -2709, 23, 804]], ![![863, -226, -1095, 10, 327]], ![![387, -88, -473, 11, 147]], ![![1549, -433, -2004, 36, 609]], ![![1611, -413, -2034, 55, 634]]]
  g := ![![![-3505, 3398, 1131, 5909, -3246], ![15647, -15181, -5022, -26369, 14481], ![-34923, 33892, 11188, 58846, -32313], ![70120, -68059, -22443, -118146, 64872], ![-99024, 96113, 31695, 166847, -91613]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N1 : Nat.card (O ⧸ I251N1) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N1)

lemma isPrimeI251N1 : Ideal.IsPrime I251N1 := prime_ideal_of_norm_prime hp251.out _ NI251N1

def I251N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 1848, 2513, -78, -651]] i)))

def SI251N2: IdealEqSpanCertificate' Table ![![43, 1848, 2513, -78, -651]] 
 ![![251, 0, 0, 0, 0], ![189, 1, 0, 0, 0], ![86, 0, 1, 0, 0], ![187, 0, 0, 1, 0], ![115, 0, 0, 0, 1]] where
  M :=![![![43, 1848, 2513, -78, -651], ![-5208, -621, 3852, 547, -885], ![-3540, -3164, -1168, 481, 378], ![4116, -1339, -5571, -359, 1353], ![884, -873, -2005, -54, 500]]]
  hmulB := by decide  
  f := ![![![-1063615, 344887, -671813, -174452, 205581]], ![![-794337, 257572, -501729, -130285, 153534]], ![![-369490, 119811, -233382, -60603, 71418]], ![![-791771, 256743, -500110, -129862, 153039]], ![![-488619, 158443, -308630, -80141, 94448]]]
  g := ![![![-1896, 1848, 2513, -78, -651], ![-875, -621, 3852, 547, -885], ![2237, -3164, -1168, 481, 378], ![2581, -1339, -5571, -359, 1353], ![1159, -873, -2005, -54, 500]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N2 : Nat.card (O ⧸ I251N2) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N2)

lemma isPrimeI251N2 : Ideal.IsPrime I251N2 := prime_ideal_of_norm_prime hp251.out _ NI251N2
def MulI251N0 : IdealMulLeCertificate' Table 
  ![![11, 101, 122, -35, -19]] ![![5827, 3398, 1131, 5909, -3246]]
  ![![5457713, 3194839, 1053455, 5545959, -3045184]] where
 M := ![![![5457713, 3194839, 1053455, 5545959, -3045184]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI251N1 : IdealMulLeCertificate' Table 
  ![![5457713, 3194839, 1053455, 5545959, -3045184]] ![![43, 1848, 2513, -78, -651]]
  ![![251, 0, 0, 0, 0]] where
 M := ![![![1954035, 1133516, 373488, 2027829, -1107161]]]
 hmul := by decide  
 g := ![![![![7785, 4516, 1488, 8079, -4411]]]]
 hle2 := by decide  


def PBC251 : ContainsPrimesAboveP 251 ![I251N0, I251N1, I251N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI251N0
    exact isPrimeI251N1
    exact isPrimeI251N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 251 (by decide) (𝕀 ⊙ MulI251N0 ⊙ MulI251N1)


lemma PB1072I5_primes (p : ℕ) :
  p ∈ Set.range ![199, 211, 223, 227, 229, 233, 239, 241, 251] ↔ Nat.Prime p ∧ 197 < p ∧ p ≤ 251 := by
  rw [← List.mem_ofFn']
  convert primes_range 197 251 (by omega)

def PB1072I5 : PrimesBelowBoundCertificateInterval O 197 251 1072 where
  m := 9
  g := ![3, 2, 4, 2, 2, 3, 2, 3, 3]
  P := ![199, 211, 223, 227, 229, 233, 239, 241, 251]
  hP := PB1072I5_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I199N0, I199N1, I199N2]
    · exact ![I211N0, I211N1]
    · exact ![I223N0, I223N1, I223N2, I223N3]
    · exact ![I227N0, I227N1]
    · exact ![I229N0, I229N1]
    · exact ![I233N0, I233N1, I233N2]
    · exact ![I239N0, I239N1]
    · exact ![I241N0, I241N1, I241N2]
    · exact ![I251N0, I251N1, I251N2]
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
    · exact ![39601, 39601, 199]
    · exact ![1982119441, 211]
    · exact ![49729, 223, 223, 223]
    · exact ![2655237841, 227]
    · exact ![2750058481, 229]
    · exact ![12649337, 233, 233]
    · exact ![3262808641, 239]
    · exact ![58081, 58081, 241]
    · exact ![15813251, 251, 251]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI199N0
      exact NI199N1
      exact NI199N2
    · dsimp ; intro j
      fin_cases j
      exact NI211N0
      exact NI211N1
    · dsimp ; intro j
      fin_cases j
      exact NI223N0
      exact NI223N1
      exact NI223N2
      exact NI223N3
    · dsimp ; intro j
      fin_cases j
      exact NI227N0
      exact NI227N1
    · dsimp ; intro j
      fin_cases j
      exact NI229N0
      exact NI229N1
    · dsimp ; intro j
      fin_cases j
      exact NI233N0
      exact NI233N1
      exact NI233N2
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
      exact NI251N2
  β := ![I199N2, I211N1, I223N1, I223N2, I223N3, I227N1, I229N1, I233N1, I233N2, I239N1, I241N2, I251N1, I251N2]
  Il := ![[I199N2], [I211N1], [I223N1, I223N2, I223N3], [I227N1], [I229N1], [I233N1, I233N2], [I239N1], [I241N2], [I251N1, I251N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
