
import IdealArithmetic.Examples.NF5_1_27000000_1.RI5_1_27000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![237, 85, -28, -15, -46]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![237, 85, -28, -15, -46]] 
 ![![199, 0, 0, 0, 0], ![0, 199, 0, 0, 0], ![0, 0, 199, 0, 0], ![146, 121, 143, 1, 0], ![90, 175, 140, 0, 1]] where
  M :=![![![237, 85, -28, -15, -46], ![368, 324, 108, 51, -30], ![-64, 187, 189, 87, 66], ![-448, -93, 112, 54, 102], ![-328, 196, 308, 148, 141]]]
  hmulB := by decide  
  f := ![![![3, -7, 0, -9, 6]], ![![-48, 14, 16, -3, -18]], ![![96, -13, -9, 37, 6]], ![![42, -6, 3, 18, -2]], ![![26, 0, 8, 19, -9]]]
  g := ![![![33, 50, 43, -15, -46], ![-22, -3, -15, 51, -30], ![-94, -110, -108, 87, 66], ![-88, -123, -110, 54, 102], ![-174, -213, -204, 148, 141]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 3 2 7 [32, 178, 120, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [45, 139, 76], [34, 59, 123], [0, 1]]
 g := ![![[67, 96, 1], [157, 91, 4], [180, 191, 13], [59, 151], [22, 184], [51, 72], [1]], ![[49, 9, 81, 118], [47, 0, 92, 168], [5, 114, 28, 186], [187, 47], [88, 10], [51, 182], [101, 63, 66, 181]], ![[30, 93, 139, 106], [49, 137, 78, 4], [180, 186, 181, 51], [31, 53], [95, 9], [24, 29], [186, 5, 118, 18]]]
 h' := ![![[45, 139, 76], [150, 108, 1], [11, 106, 197], [99, 106, 150], [14, 125, 56], [188, 10, 130], [167, 21, 79], [0, 1]], ![[34, 59, 123], [73, 153, 108], [128, 75, 177], [22, 157, 190], [6, 176, 68], [6, 20, 72], [134, 173, 88], [45, 139, 76]], ![[0, 1], [117, 137, 90], [80, 18, 24], [178, 135, 58], [162, 97, 75], [60, 169, 196], [119, 5, 32], [34, 59, 123]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [88, 158], []]
 b := ![[], [48, 38, 66], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 3
  hpos := by decide
  P := [32, 178, 120, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1893848, -367592, -1230548, 332644, 691924]
  a := ![0, 8, 5, -1, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-547464, -812584, -732000, 332644, 691924]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 7880599 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 7, 0, 9, -6]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![-3, 7, 0, 9, -6]] 
 ![![199, 0, 0, 0, 0], ![0, 199, 0, 0, 0], ![120, 57, 1, 0, 0], ![125, 24, 0, 1, 0], ![188, 68, 0, 0, 1]] where
  M :=![![![-3, 7, 0, 9, -6], ![48, -14, -16, 3, 18], ![-96, 13, 9, -37, -6], ![0, 7, 52, 32, -46], ![136, 0, -52, 64, 21]]]
  hmulB := by decide  
  f := ![![![-237, -85, 28, 15, 46]], ![![-368, -324, -108, -51, 30]], ![![-248, -145, -15, -6, 36]], ![![-191, -92, 4, 3, 32]], ![![-348, -192, -12, -4, 53]]]
  g := ![![![0, 1, 0, 9, -6], ![-9, -2, -16, 3, 18], ![23, 4, 9, -37, -6], ![-8, -3, 52, 32, -46], ![-28, 0, -52, 64, 21]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P1 : CertificateIrreducibleZModOfList' 199 2 2 7 [56, 122, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [77, 198], [0, 1]]
 g := ![![[123, 32], [110, 62], [85, 140], [58], [46], [56], [77, 1]], ![[0, 167], [108, 137], [119, 59], [58], [46], [56], [154, 198]]]
 h' := ![![[77, 198], [9, 80], [16, 103], [76, 109], [90, 156], [26, 65], [66, 102], [0, 1]], ![[0, 1], [0, 119], [186, 96], [111, 90], [162, 43], [56, 134], [159, 97], [77, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [187]]
 b := ![[], [32, 193]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N1 : CertifiedPrimeIdeal' SI199N1 199 where
  n := 2
  hpos := by decide
  P := [56, 122, 1]
  hirr := P199P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-39129, -9254, -2533, -26732, -1434]
  a := ![3, -5, -3, -1, -52]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![19477, 4393, -2533, -26732, -1434]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N1 B_one_repr
lemma NI199N1 : Nat.card (O ⧸ I199N1) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N1
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![237, 85, -28, -15, -46]] ![![-3, 7, 0, 9, -6]]
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

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-431, 254, 393, 189, 181]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![-431, 254, 393, 189, 181]] 
 ![![211, 0, 0, 0, 0], ![0, 211, 0, 0, 0], ![0, 0, 211, 0, 0], ![0, 0, 0, 211, 0], ![148, 90, 8, 57, 1]] where
  M :=![![![-431, 254, 393, 189, 181], ![-1448, -162, 492, 235, 378], ![-788, -713, -265, -121, 46], ![540, -681, -792, -368, -310], ![-726, -1314, -792, -368, -99]]]
  hmulB := by decide  
  f := ![![![-3, 4, -3, 3, -1]], ![![8, -8, 0, -7, 6]], ![![-28, 11, 5, 1, -10]], ![![36, -3, 0, 18, -2]], ![![10, -1, -2, 4, 1]]]
  g := ![![![-129, -76, -5, -48, 181], ![-272, -162, -12, -101, 378], ![-36, -23, -3, -13, 46], ![220, 129, 8, 82, -310], ![66, 36, 0, 25, -99]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 4 2 7 [70, 133, 147, 8, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [153, 23, 69, 122], [85, 131, 154, 65], [176, 56, 199, 24], [0, 1]]
 g := ![![[37, 181, 21, 163], [109, 106, 129, 47], [58, 125, 122], [183, 164, 209], [176, 132, 140, 150], [128, 203, 1], []], ![[141, 135, 156, 210, 154, 45], [153, 158, 21, 153, 110, 49], [189, 80, 55], [193, 120, 44], [170, 24, 145, 205, 117, 71], [74, 204, 185], [70, 23, 147, 14, 110, 193]], ![[69, 166, 14, 42, 77, 47], [135, 91, 42, 7, 4, 114], [112, 70, 54], [54, 35, 148], [13, 204, 130, 189, 61, 34], [98, 201, 107], [119, 63, 176, 109, 132, 114]], ![[49, 156, 72, 164, 200, 100], [47, 55, 149, 194, 36, 51], [185, 130, 194], [12, 148, 119], [165, 177, 180, 152, 16, 203], [145, 178, 120], [80, 1, 34, 16, 125, 109]]]
 h' := ![![[153, 23, 69, 122], [177, 105, 43, 116], [194, 76, 192, 70], [33, 46, 184, 132], [129, 166, 65, 118], [113, 205, 113, 19], [0, 0, 0, 1], [0, 1]], ![[85, 131, 154, 65], [26, 32, 72, 83], [107, 40, 104, 56], [39, 143, 108, 104], [195, 65, 190, 39], [140, 209, 7, 193], [16, 68, 202, 94], [153, 23, 69, 122]], ![[176, 56, 199, 24], [39, 51, 139, 191], [74, 64, 112, 146], [23, 129, 196, 138], [65, 41, 71, 123], [88, 169, 42, 130], [14, 17, 55, 188], [85, 131, 154, 65]], ![[0, 1], [18, 23, 168, 32], [196, 31, 14, 150], [8, 104, 145, 48], [209, 150, 96, 142], [49, 50, 49, 80], [55, 126, 165, 139], [176, 56, 199, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [95, 194, 14], []]
 b := ![[], [], [31, 91, 209, 29], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 4
  hpos := by decide
  P := [70, 133, 147, 8, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10654971, 4164113, 18689154, 8403993, -17105343]
  a := ![1, 3, 2, -1, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![11947563, 7315853, 737118, 4660704, -17105343]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 1982119441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, -4, 3, -3, 1]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![3, -4, 3, -3, 1]] 
 ![![211, 0, 0, 0, 0], ![97, 1, 0, 0, 0], ![100, 0, 1, 0, 0], ![60, 0, 0, 1, 0], ![60, 0, 0, 0, 1]] where
  M :=![![![3, -4, 3, -3, 1], ![-8, 8, 0, 7, -6], ![28, -11, -5, -1, 10], ![-36, 3, 0, -18, 2], ![-6, 0, 18, 4, -13]]]
  hmulB := by decide  
  f := ![![![431, -254, -393, -189, -181]], ![![205, -116, -183, -88, -85]], ![![208, -117, -185, -89, -86]], ![![120, -69, -108, -52, -50]], ![![126, -66, -108, -52, -51]]]
  g := ![![![1, -4, 3, -3, 1], ![-4, 8, 0, 7, -6], ![5, -11, -5, -1, 10], ![3, 3, 0, -18, 2], ![-6, 0, 18, 4, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![-431, 254, 393, 189, 181]] ![![3, -4, 3, -3, 1]]
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

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1035, 2520, 8945, 8233, -9249]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![1035, 2520, 8945, 8233, -9249]] 
 ![![223, 0, 0, 0, 0], ![0, 223, 0, 0, 0], ![0, 0, 223, 0, 0], ![0, 0, 0, 223, 0], ![26, 73, 187, 17, 1]] where
  M :=![![![1035, 2520, 8945, 8233, -9249], ![73992, -3966, -29924, 28155, 16466], ![-102860, -6121, -693, -74545, 19922], ![-116684, 21691, 103308, 2580, -82778], ![243902, 2336, -42630, 139696, -2421]]]
  hmulB := by decide  
  f := ![![![-797, 442, -139, 147, -119]], ![![952, -788, 352, -187, 294]], ![![-1652, 839, -483, 245, -334]], ![![860, -499, 84, -178, 98]], ![![-1104, 460, -301, 148, -191]]]
  g := ![![![1083, 3039, 7796, 742, -9249], ![-1588, -5408, -13942, -1129, 16466], ![-2784, -6549, -16709, -1853, 19922], ![9128, 27195, 69878, 6322, -82778], ![1376, 803, 1839, 811, -2421]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 4 2 7 [49, 70, 10, 55, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [181, 116, 151, 35], [111, 4, 64, 195], [99, 102, 8, 216], [0, 1]]
 g := ![![[192, 170, 144, 32], [108, 10, 117, 203], [145, 6, 7, 58], [28, 140, 192, 68], [197, 52, 2, 146], [116, 168, 1], []], ![[15, 205, 3, 195, 43, 194], [212, 3, 45, 94, 64, 35], [99, 165, 211, 15, 91, 165], [20, 145, 49, 97, 171, 45], [55, 1, 118, 181, 211, 214], [114, 141, 29], [124, 193, 211, 75, 201, 59]], ![[112, 129, 97, 94, 167, 12], [119, 148, 192, 142, 161, 160], [196, 215, 215, 201, 114, 198], [124, 76, 208, 201, 182, 45], [67, 181, 181, 119, 215, 174], [122, 133, 217], [18, 5, 58, 130, 41, 125]], ![[204, 127, 38, 94, 171, 140], [102, 176, 165, 183, 0, 42], [217, 32, 34, 162, 56, 186], [25, 67, 101, 220, 9, 27], [161, 205, 15, 183, 161, 35], [176, 66, 89], [19, 135, 200, 166, 194, 103]]]
 h' := ![![[181, 116, 151, 35], [60, 47, 222, 163], [31, 78, 129, 42], [189, 182, 198, 110], [159, 3, 171, 108], [114, 150, 188, 121], [0, 0, 0, 1], [0, 1]], ![[111, 4, 64, 195], [174, 192, 50, 159], [56, 66, 39, 1], [31, 89, 107, 155], [39, 111, 157, 180], [65, 78, 50, 136], [116, 102, 206, 67], [181, 116, 151, 35]], ![[99, 102, 8, 216], [140, 173, 141, 166], [213, 86, 97, 110], [131, 122, 36, 150], [175, 134, 200, 106], [144, 213, 43, 210], [205, 59, 220, 70], [111, 4, 64, 195]], ![[0, 1], [103, 34, 33, 181], [67, 216, 181, 70], [217, 53, 105, 31], [198, 198, 141, 52], [19, 5, 165, 202], [210, 62, 20, 85], [99, 102, 8, 216]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [50, 56, 185], []]
 b := ![[], [], [215, 175, 13, 142], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 4
  hpos := by decide
  P := [49, 70, 10, 55, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-650978313, 884272201, 3375231041, 2377532628, -3272936523]
  a := ![1, -11, -7, -1, 47]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![378678795, 1075375060, 2759705654, 260167953, -3272936523]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 2472973441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![797, -442, 139, -147, 119]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![797, -442, 139, -147, 119]] 
 ![![223, 0, 0, 0, 0], ![189, 1, 0, 0, 0], ![108, 0, 1, 0, 0], ![69, 0, 0, 1, 0], ![55, 0, 0, 0, 1]] where
  M :=![![![797, -442, 139, -147, 119], ![-952, 788, -352, 187, -294], ![1652, -839, 483, -245, 334], ![-860, 499, -84, 178, -98], ![662, -202, 312, -44, 169]]]
  hmulB := by decide  
  f := ![![![-1035, -2520, -8945, -8233, 9249]], ![![-1209, -2118, -7447, -7104, 7765]], ![![-40, -1193, -4329, -3653, 4390]], ![![203, -877, -3231, -2559, 3233]], ![![-1349, -632, -2015, -2657, 2292]]]
  g := ![![![327, -442, 139, -147, 119], ![-487, 788, -352, 187, -294], ![478, -839, 483, -245, 334], ![-417, 499, -84, 178, -98], ![-5, -202, 312, -44, 169]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![1035, 2520, 8945, 8233, -9249]] ![![797, -442, 139, -147, 119]]
  ![![223, 0, 0, 0, 0]] where
 M := ![![![-223, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC223 : ContainsPrimesAboveP 223 ![I223N0, I223N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI223N0
    exact isPrimeI223N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 223 (by decide) (𝕀 ⊙ MulI223N0)
instance hp227 : Fact (Nat.Prime 227) := {out := by norm_num}

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0, 0, 0]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![227, 0, 0, 0, 0]] 
 ![![227, 0, 0, 0, 0], ![0, 227, 0, 0, 0], ![0, 0, 227, 0, 0], ![0, 0, 0, 227, 0], ![0, 0, 0, 0, 227]] where
  M :=![![![227, 0, 0, 0, 0], ![0, 227, 0, 0, 0], ![0, 0, 227, 0, 0], ![0, 0, 0, 227, 0], ![0, 0, 0, 0, 227]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 5 2 7 [82, 168, 66, 181, 180, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [117, 220, 208, 181, 100], [117, 82, 121, 52, 212], [10, 21, 72, 48, 116], [30, 130, 53, 173, 26], [0, 1]]
 g := ![![[101, 133, 107, 100, 112], [39, 45, 194, 63, 79], [219, 43, 97, 19], [220, 89, 9, 97], [140, 226, 73, 160], [212, 47, 1], []], ![[85, 66, 86, 121, 90, 180, 35, 147], [176, 2, 170, 127, 48, 119, 166, 1], [159, 189, 18, 4], [193, 178, 141, 116], [221, 207, 188, 33], [61, 197, 145, 143, 226, 203, 126, 77], [91, 138, 31, 12, 159, 67, 37, 65]], ![[10, 106, 23, 110, 193, 201, 83, 133], [171, 146, 41, 144, 47, 90, 189, 195], [6, 176, 190, 190], [82, 222, 142, 207], [93, 201, 56, 186], [121, 86, 12, 26, 187, 15, 95, 90], [180, 3, 144, 177, 23, 42, 190, 30]], ![[108, 89, 123, 181, 190, 30, 164, 70], [44, 132, 25, 158, 137, 30, 53, 11], [62, 174, 214, 155], [154, 129, 224, 43], [70, 167, 32, 70], [189, 20, 157, 84, 10, 138, 52, 144], [139, 188, 14, 39, 115, 115, 17, 44]], ![[1, 11, 88, 215, 52, 116, 30, 185], [21, 177, 174, 36, 155, 117, 4, 12], [110, 136, 175, 44], [211, 95, 197, 161], [73, 224, 7, 1], [7, 125, 68, 218, 180, 107, 94, 25], [178, 181, 62, 70, 209, 175, 148, 97]]]
 h' := ![![[117, 220, 208, 181, 100], [207, 49, 115, 139, 148], [59, 62, 35, 71, 83], [68, 130, 179, 152, 84], [42, 42, 30, 88, 18], [95, 28, 49, 126, 29], [0, 0, 0, 1], [0, 1]], ![[117, 82, 121, 52, 212], [12, 15, 82, 215, 35], [138, 146, 111, 97, 159], [163, 116, 222, 156, 225], [107, 76, 204, 105, 32], [117, 119, 61, 161, 43], [157, 95, 148, 201, 79], [117, 220, 208, 181, 100]], ![[10, 21, 72, 48, 116], [23, 118, 91, 192, 138], [61, 213, 63, 42, 21], [107, 123, 170, 67, 155], [34, 175, 61, 137, 52], [13, 28, 51, 203, 58], [123, 108, 179, 77, 158], [117, 82, 121, 52, 212]], ![[30, 130, 53, 173, 26], [88, 226, 53, 190, 153], [85, 59, 192, 168, 58], [42, 0, 35, 149, 137], [171, 11, 43, 91, 161], [3, 196, 131, 171, 98], [44, 220, 188, 213, 199], [10, 21, 72, 48, 116]], ![[0, 1], [43, 46, 113, 172, 207], [193, 201, 53, 76, 133], [70, 85, 75, 157, 80], [183, 150, 116, 33, 191], [128, 83, 162, 20, 226], [146, 31, 166, 189, 18], [30, 130, 53, 173, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [150, 226, 27, 57], [], [], []]
 b := ![[], [118, 195, 8, 203, 206], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 5
  hpos := by decide
  P := [82, 168, 66, 181, 180, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-465468937558, 14029709576, 152660396520, -205908630960, -68358689200]
  a := ![-1, 13, 9, 2, -30]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2050523954, 61804888, 672512760, -907086480, -301139600]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 602738989907 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def PBC227 : ContainsPrimesAboveP 227 ![I227N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI227N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![227, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 227 (by decide) 𝕀

instance hp229 : Fact (Nat.Prime 229) := {out := by norm_num}

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-413, 8, -7, -315, 133]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![-413, 8, -7, -315, 133]] 
 ![![229, 0, 0, 0, 0], ![0, 229, 0, 0, 0], ![0, 0, 229, 0, 0], ![147, 69, 66, 1, 0], ![104, 86, 96, 0, 1]] where
  M :=![![![-413, 8, -7, -315, 133], ![-1064, 218, 912, 35, -630], ![3052, -111, -903, 1507, 350], ![-868, -597, -1724, -2024, 1822], ![-5734, 238, 2396, -2004, -1393]]]
  hmulB := by decide  
  f := ![![![1612905, -975970, 430215, -280651, 336401]], ![![-2691208, 1628452, -717836, 468279, -561302]], ![![3590812, -2172801, 957789, -624813, 748930]], ![![1252171, -757689, 333995, -217882, 261163]], ![![1233482, -746380, 329010, -214630, 257265]]]
  g := ![![![140, 45, 35, -315, 133], ![259, 227, 258, 35, -630], ![-1113, -586, -585, 1507, 350], ![468, -77, -188, -2024, 1822], ![1894, 1128, 1172, -2004, -1393]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 3 2 7 [93, 148, 114, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [209, 161, 207], [135, 67, 22], [0, 1]]
 g := ![![[47, 52, 26], [86, 196], [162, 200, 36], [178, 126], [193, 220], [217, 167, 172], [1]], ![[78, 164, 47, 216], [228, 11], [130, 211, 76, 195], [184, 81], [228, 75], [63, 68, 203, 155], [124, 224, 135, 115]], ![[69, 204, 1, 191], [196, 171], [124, 68, 137, 88], [69, 134], [90, 11], [212, 74, 128, 199], [116, 26, 16, 114]]]
 h' := ![![[209, 161, 207], [31, 131, 22], [48, 164, 215], [72, 23, 223], [67, 33, 144], [200, 161, 92], [136, 81, 115], [0, 1]], ![[135, 67, 22], [219, 0, 195], [144, 42, 34], [12, 191, 8], [112, 62, 220], [83, 156, 103], [162, 128, 198], [209, 161, 207]], ![[0, 1], [43, 98, 12], [167, 23, 209], [86, 15, 227], [159, 134, 94], [96, 141, 34], [203, 20, 145], [135, 67, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [170, 126], []]
 b := ![[], [92, 38, 89], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 3
  hpos := by decide
  P := [93, 148, 114, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-95523, 25712, 160744, 43024, -126928]
  a := ![0, -10, -6, -10, 8]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![29609, 34816, 41512, 43024, -126928]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 12008989 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3015, 1850, 252, 104, -418]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![3015, 1850, 252, 104, -418]] 
 ![![229, 0, 0, 0, 0], ![154, 1, 0, 0, 0], ![202, 0, 1, 0, 0], ![170, 0, 0, 1, 0], ![175, 0, 0, 0, 1]] where
  M :=![![![3015, 1850, 252, 104, -418], ![3344, 4909, 2656, 1236, 208], ![-2504, 1764, 2553, 1212, 1132], ![-6200, -2760, 356, 197, 1108], ![-6692, 794, 3538, 1696, 2091]]]
  hmulB := by decide  
  f := ![![![-42869, -154, 8456, -23760, -542]], ![![-28810, -47, 5888, -15796, -572]], ![![-36994, -208, 7025, -20732, -192]], ![![-32978, -212, 6164, -18563, -72]], ![![-33819, 60, 7330, -18192, -1095]]]
  g := ![![![-1211, 1850, 252, 104, -418], ![-6706, 4909, 2656, 1236, 208], ![-5214, 1764, 2553, 1212, 1132], ![522, -2760, 356, 197, 1108], ![-6541, 794, 3538, 1696, 2091]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N1 : Nat.card (O ⧸ I229N1) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N1)

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := prime_ideal_of_norm_prime hp229.out _ NI229N1

def I229N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![95, -3, -36, 37, 20]] i)))

def SI229N2: IdealEqSpanCertificate' Table ![![95, -3, -36, 37, 20]] 
 ![![229, 0, 0, 0, 0], ![173, 1, 0, 0, 0], ![63, 0, 1, 0, 0], ![189, 0, 0, 1, 0], ![12, 0, 0, 0, 1]] where
  M :=![![![95, -3, -36, 37, 20], ![-160, -18, -40, -149, 74], ![-216, 49, 225, 35, -186], ![824, 3, -152, 468, -2], ![44, -98, -358, -264, 355]]]
  hmulB := by decide  
  f := ![![![-2681165, 1622379, -715172, 466529, -559216]], ![![-2005973, 1213819, -535072, 349044, -418390]], ![![-763679, 462104, -203703, 132882, -159282]], ![![-2200861, 1331746, -587056, 382955, -459038]], ![![-151032, 91390, -40286, 26280, -31501]]]
  g := ![![![-19, -3, -36, 37, 20], ![143, -18, -40, -149, 74], ![-119, 49, 225, 35, -186], ![-343, 3, -152, 468, -2], ![372, -98, -358, -264, 355]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N2 : Nat.card (O ⧸ I229N2) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N2)

lemma isPrimeI229N2 : Ideal.IsPrime I229N2 := prime_ideal_of_norm_prime hp229.out _ NI229N2
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![-413, 8, -7, -315, 133]] ![![3015, 1850, 252, 104, -418]]
  ![![-137951, 237876, 257715, 121965, 95457]] where
 M := ![![![-137951, 237876, 257715, 121965, 95457]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI229N1 : IdealMulLeCertificate' Table 
  ![![-137951, 237876, 257715, 121965, 95457]] ![![95, -3, -36, 37, 20]]
  ![![229, 0, 0, 0, 0]] where
 M := ![![![-2132677, -228771, 724785, 351286, 552119]]]
 hmul := by decide  
 g := ![![![![-9313, -999, 3165, 1534, 2411]]]]
 hle2 := by decide  


def PBC229 : ContainsPrimesAboveP 229 ![I229N0, I229N1, I229N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI229N0
    exact isPrimeI229N1
    exact isPrimeI229N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 229 (by decide) (𝕀 ⊙ MulI229N0 ⊙ MulI229N1)
instance hp233 : Fact (Nat.Prime 233) := {out := by norm_num}

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![623, -19, -104, 389, -28]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![623, -19, -104, 389, -28]] 
 ![![233, 0, 0, 0, 0], ![0, 233, 0, 0, 0], ![0, 0, 233, 0, 0], ![57, 57, 67, 1, 0], ![54, 27, 144, 0, 1]] where
  M :=![![![623, -19, -104, 389, -28], ![224, -278, -872, -541, 778], ![-3224, 217, 1477, -1109, -930], ![3608, 483, 832, 3232, -1498], ![4796, -590, -3226, 680, 2331]]]
  hmulB := by decide  
  f := ![![![-919873, 556615, -245360, 160061, -191856]], ![![1534848, -928740, 409396, -267069, 320122]], ![![-2047912, 1239191, -546247, 356343, -427130]], ![![-434401, 262855, -115869, 75587, -90602]], ![![-1304546, 789380, -347966, 226995, -272087]]]
  g := ![![![-86, -92, -95, 389, -28], ![-47, 41, -329, -541, 778], ![473, 380, 900, -1109, -930], ![-428, -615, 0, 3232, -1498], ![-686, -439, -1650, 680, 2331]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 3 2 7 [227, 126, 97, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 190, 88], [117, 42, 145], [0, 1]]
 g := ![![[42, 159, 32], [20, 224], [57, 60], [158, 231, 28], [128, 207], [175, 200, 89], [1]], ![[125, 134, 232, 42], [113, 170], [157, 101], [206, 89, 65, 45], [204, 116], [63, 33, 63, 35], [149, 137, 143, 180]], ![[20, 229, 169, 67], [100, 66], [19, 224], [189, 193, 15, 65], [134, 196], [61, 64, 179, 149], [86, 168, 158, 53]]]
 h' := ![![[19, 190, 88], [69, 49, 107], [132, 32, 34], [16, 54, 35], [13, 28, 140], [118, 156, 185], [6, 107, 136], [0, 1]], ![[117, 42, 145], [140, 9, 185], [188, 187, 50], [90, 171, 164], [232, 147, 189], [147, 145, 62], [64, 20, 216], [19, 190, 88]], ![[0, 1], [172, 175, 174], [51, 14, 149], [183, 8, 34], [121, 58, 137], [4, 165, 219], [21, 106, 114], [117, 42, 145]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [93, 122], []]
 b := ![[], [103, 65, 131], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 3
  hpos := by decide
  P := [227, 126, 97, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1859295, -349574, -1352233, 130609, 791131]
  a := ![13, 10, 7, 1, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-207324, -125128, -532300, 130609, 791131]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 12649337 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-919873, 556615, -245360, 160061, -191856]] i)))

def SI233N1: IdealEqSpanCertificate' Table ![![-919873, 556615, -245360, 160061, -191856]] 
 ![![233, 0, 0, 0, 0], ![0, 233, 0, 0, 0], ![180, 167, 1, 0, 0], ![230, 12, 0, 1, 0], ![232, 153, 0, 0, 1]] where
  M :=![![![-919873, 556615, -245360, 160061, -191856], ![1534848, -928740, 409396, -267069, 320122], ![-2047912, 1239191, -546247, 356343, -427130], ![941096, -569457, 251020, -163754, 196282], ![-827644, 500806, -220762, 144012, -172621]]]
  hmulB := by decide  
  f := ![![![623, -19, -104, 389, -28]], ![![224, -278, -872, -541, 778]], ![![628, -213, -699, -92, 532]], ![![642, -31, -144, 370, 6]], ![![788, -204, -690, 35, 493]]]
  g := ![![![218633, 295987, -245360, 160061, -191856], ![-364802, -493870, 409396, -267069, 320122], ![486746, 658958, -546247, 356343, -427130], ![-223676, -302815, 251020, -163754, 196282], ![196716, 266313, -220762, 144012, -172621]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P1 : CertificateIrreducibleZModOfList' 233 2 2 7 [22, 84, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [149, 232], [0, 1]]
 g := ![![[25, 74], [62], [170], [85, 205], [7], [0, 72], [149, 1]], ![[100, 159], [62], [170], [107, 28], [7], [10, 161], [65, 232]]]
 h' := ![![[149, 232], [144, 105], [24, 67], [227, 183], [79, 111], [0, 70], [217, 44], [0, 1]], ![[0, 1], [178, 128], [221, 166], [0, 50], [75, 122], [178, 163], [16, 189], [149, 232]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [212]]
 b := ![[], [25, 106]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N1 : CertifiedPrimeIdeal' SI233N1 233 where
  n := 2
  hpos := by decide
  P := [22, 84, 1]
  hirr := P233P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-947, -545, -382, -944, 958]
  a := ![-1, -5, -3, -1, 9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![269, -309, -382, -944, 958]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N1 B_one_repr
lemma NI233N1 : Nat.card (O ⧸ I233N1) = 54289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N1
def MulI233N0 : IdealMulLeCertificate' Table 
  ![![623, -19, -104, 389, -28]] ![![-919873, 556615, -245360, 160061, -191856]]
  ![![233, 0, 0, 0, 0]] where
 M := ![![![233, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3845, 2327, -1026, 669, -802]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![-3845, 2327, -1026, 669, -802]] 
 ![![239, 0, 0, 0, 0], ![0, 239, 0, 0, 0], ![17, 232, 1, 0, 0], ![119, 76, 0, 1, 0], ![99, 62, 0, 0, 1]] where
  M :=![![![-3845, 2327, -1026, 669, -802], ![6416, -3882, 1712, -1117, 1338], ![-8560, 5181, -2283, 1491, -1786], ![3936, -2381, 1048, -684, 822], ![-3464, 2094, -922, 600, -721]]]
  hmulB := by decide  
  f := ![![![125, 75, 14, 11, -22]], ![![176, 192, 84, 61, 22]], ![![179, 192, 83, 60, 20]], ![![117, 98, 34, 25, -4]], ![![97, 81, 28, 21, -3]]]
  g := ![![![56, 1001, -1026, 669, -802], ![-93, -1670, 1712, -1117, 1338], ![124, 2227, -2283, 1491, -1786], ![-58, -1023, 1048, -684, 822], ![51, 900, -922, 600, -721]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 2 2 7 [82, 81, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [158, 238], [0, 1]]
 g := ![![[103, 24], [164, 2], [110, 197], [82, 135], [8], [4, 198], [158, 1]], ![[71, 215], [2, 237], [166, 42], [141, 104], [8], [218, 41], [77, 238]]]
 h' := ![![[158, 238], [175, 195], [62, 99], [207, 156], [95, 180], [150, 41], [189, 26], [0, 1]], ![[0, 1], [154, 44], [169, 140], [238, 83], [94, 59], [175, 198], [234, 213], [158, 238]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [113]]
 b := ![[], [197, 176]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 2
  hpos := by decide
  P := [82, 81, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-13722, -3580, -1706, -12342, 5280]
  a := ![3, -14, -7, -4, 34]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![4022, 4196, -1706, -12342, 5280]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N0 B_one_repr
lemma NI239N0 : Nat.card (O ⧸ I239N0) = 57121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N0

def I239N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-255, 197, 769, 460, -731]] i)))

def SI239N1: IdealEqSpanCertificate' Table ![![-255, 197, 769, 460, -731]] 
 ![![239, 0, 0, 0, 0], ![0, 239, 0, 0, 0], ![57, 228, 1, 0, 0], ![149, 22, 0, 1, 0], ![192, 207, 0, 0, 1]] where
  M :=![![![-255, 197, 769, 460, -731], ![5848, -209, -1988, 2540, 920], ![-6604, -610, -835, -5448, 2080], ![-11244, 1528, 7912, -1461, -5908], ![17254, 504, -1786, 10912, -1415]]]
  hmulB := by decide  
  f := ![![![-315711, 191139, -84227, 54952, -65877]], ![![527016, -318703, 140620, -91652, 109904]], ![![424523, -256669, 113276, -73816, 88521]], ![![-146961, 89007, -39205, 25587, -30671]], ![![201638, -121761, 53812, -35028, 42019]]]
  g := ![![![116, -142, 769, 460, -731], ![-1824, 865, -1988, 2540, 920], ![1897, -506, -835, -5448, 2080], ![3723, -2290, 7912, -1461, -5908], ![-5168, 1927, -1786, 10912, -1415]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P1 : CertificateIrreducibleZModOfList' 239 2 2 7 [93, 41, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [198, 238], [0, 1]]
 g := ![![[21, 18], [216, 128], [90, 27], [27, 67], [101], [93, 55], [198, 1]], ![[0, 221], [226, 111], [178, 212], [148, 172], [101], [228, 184], [157, 238]]]
 h' := ![![[198, 238], [227, 58], [234, 75], [118, 79], [41, 28], [194, 36], [228, 154], [0, 1]], ![[0, 1], [0, 181], [27, 164], [225, 160], [88, 211], [152, 203], [128, 85], [198, 238]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [218]]
 b := ![[], [203, 109]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N1 : CertifiedPrimeIdeal' SI239N1 239 where
  n := 2
  hpos := by decide
  P := [93, 41, 1]
  hirr := P239P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3167, -888, -811, -3153, 1567]
  a := ![1, -7, -5, -1, 17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![887, -297, -811, -3153, 1567]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N1 : Ideal.IsPrime I239N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N1 B_one_repr
lemma NI239N1 : Nat.card (O ⧸ I239N1) = 57121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N1

def I239N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 50, 29, 5, -1]] i)))

def SI239N2: IdealEqSpanCertificate' Table ![![107, 50, 29, 5, -1]] 
 ![![239, 0, 0, 0, 0], ![38, 1, 0, 0, 0], ![215, 0, 1, 0, 0], ![198, 0, 0, 1, 0], ![175, 0, 0, 0, 1]] where
  M :=![![![107, 50, 29, 5, -1], ![8, 176, 88, 55, 10], ![-44, -7, 87, 23, 50], ![-204, -93, -24, -2, 18], ![-210, -36, 90, 36, 67]]]
  hmulB := by decide  
  f := ![![![4531, 76, -671, 2695, -167]], ![![726, 6, -130, 413, -4]], ![![3983, 75, -560, 2394, -177]], ![![3858, 75, -534, 2326, -180]], ![![3449, 38, -583, 1991, -54]]]
  g := ![![![-37, 50, 29, 5, -1], ![-160, 176, 88, 55, 10], ![-133, -7, 87, 23, 50], ![24, -93, -24, -2, 18], ![-155, -36, 90, 36, 67]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N2 : Nat.card (O ⧸ I239N2) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N2)

lemma isPrimeI239N2 : Ideal.IsPrime I239N2 := prime_ideal_of_norm_prime hp239.out _ NI239N2
def MulI239N0 : IdealMulLeCertificate' Table 
  ![![-3845, 2327, -1026, 669, -802]] ![![-255, 197, 769, 460, -731]]
  ![![4531, 76, -671, 2695, -167]] where
 M := ![![![4531, 76, -671, 2695, -167]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI239N1 : IdealMulLeCertificate' Table 
  ![![4531, 76, -671, 2695, -167]] ![![107, 50, 29, 5, -1]]
  ![![239, 0, 0, 0, 0]] where
 M := ![![![239, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC239 : ContainsPrimesAboveP 239 ![I239N0, I239N1, I239N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI239N0
    exact isPrimeI239N1
    exact isPrimeI239N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 239 (by decide) (𝕀 ⊙ MulI239N0 ⊙ MulI239N1)
instance hp241 : Fact (Nat.Prime 241) := {out := by norm_num}

def I241N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0, 0, 0]] i)))

def SI241N0: IdealEqSpanCertificate' Table ![![241, 0, 0, 0, 0]] 
 ![![241, 0, 0, 0, 0], ![0, 241, 0, 0, 0], ![0, 0, 241, 0, 0], ![0, 0, 0, 241, 0], ![0, 0, 0, 0, 241]] where
  M :=![![![241, 0, 0, 0, 0], ![0, 241, 0, 0, 0], ![0, 0, 241, 0, 0], ![0, 0, 0, 241, 0], ![0, 0, 0, 0, 241]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P241P0 : CertificateIrreducibleZModOfList' 241 5 2 7 [111, 23, 14, 24, 236, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [183, 100, 186, 1, 124], [45, 34, 186, 85, 219], [159, 148, 123, 86, 107], [100, 199, 228, 69, 32], [0, 1]]
 g := ![![[70, 106, 64, 127, 80], [71, 119, 205, 240], [128, 11, 239, 16], [134, 192, 79, 5], [45, 68, 11, 121, 12], [1, 5, 1], []], ![[122, 16, 28, 76, 5, 31, 13, 202], [126, 182, 132, 240], [102, 82, 236, 239], [100, 159, 190, 187], [17, 163, 80, 142, 1, 225, 184, 74], [152, 171, 83, 122, 79, 44, 49, 176], [175, 235, 199, 230, 198, 174, 221, 73]], ![[170, 172, 96, 200, 179, 147, 58, 74], [191, 222, 45, 15], [14, 3, 3, 194], [180, 87, 132, 36], [177, 45, 42, 82, 68, 49, 202, 202], [46, 131, 184, 133, 206, 16, 7, 126], [208, 56, 50, 161, 80, 96, 49, 197]], ![[178, 120, 107, 16, 199, 88, 237, 59], [38, 7, 98, 237], [157, 2, 222, 159], [196, 118, 101, 238], [128, 193, 165, 223, 126, 47, 180, 233], [148, 120, 201, 63, 109, 9, 181, 36], [29, 65, 150, 194, 105, 23, 105, 40]], ![[92, 177, 215, 60, 133, 8, 65, 161], [226, 180, 116, 238], [88, 213, 232, 134], [96, 191, 24, 2], [200, 192, 99, 108, 74, 64, 83, 100], [199, 25, 190, 41, 97, 19, 207, 12], [90, 170, 42, 94, 211, 104, 89, 233]]]
 h' := ![![[183, 100, 186, 1, 124], [71, 201, 158, 227, 70], [177, 99, 100, 213, 177], [86, 36, 190, 50, 4], [66, 123, 63, 26, 103], [130, 145, 1, 124, 112], [0, 0, 0, 1], [0, 1]], ![[45, 34, 186, 85, 219], [24, 161, 3, 135, 99], [88, 202, 92, 46, 177], [223, 145, 63, 168, 203], [113, 10, 107, 92, 123], [88, 108, 109, 217, 191], [194, 148, 164, 38, 46], [183, 100, 186, 1, 124]], ![[159, 148, 123, 86, 107], [148, 44, 137, 93, 135], [158, 166, 155, 16, 225], [5, 58, 4, 153, 215], [127, 213, 43, 237, 6], [30, 160, 197, 36, 195], [75, 99, 165, 195, 209], [45, 34, 186, 85, 219]], ![[100, 199, 228, 69, 32], [150, 18, 165, 224, 207], [130, 202, 81, 201, 113], [143, 170, 107, 177, 221], [152, 198, 126, 204, 31], [209, 196, 53, 105, 132], [195, 19, 202, 10, 53], [159, 148, 123, 86, 107]], ![[0, 1], [5, 58, 19, 44, 212], [73, 54, 54, 6, 31], [125, 73, 118, 175, 80], [211, 179, 143, 164, 219], [189, 114, 122, 0, 93], [223, 216, 192, 238, 174], [100, 199, 228, 69, 32]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [226, 129, 142, 32], [], [], []]
 b := ![[], [71, 225, 100, 234, 163], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 5
  hpos := by decide
  P := [111, 23, 14, 24, 236, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![74143891, 4997617, 5583006, 58100521, -20885542]
  a := ![4, 2, 1, 1, -4]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![307651, 20737, 23166, 241081, -86662]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI241N0 : Ideal.IsPrime I241N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI241N0 B_one_repr
lemma NI241N0 : Nat.card (O ⧸ I241N0) = 812990017201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI241N0

def PBC241 : ContainsPrimesAboveP 241 ![I241N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI241N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![241, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 241 (by decide) 𝕀

instance hp251 : Fact (Nat.Prime 251) := {out := by norm_num}

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![311, 15, -120, -59, -88]] i)))

def SI251N0: IdealEqSpanCertificate' Table ![![311, 15, -120, -59, -88]] 
 ![![251, 0, 0, 0, 0], ![0, 251, 0, 0, 0], ![74, 97, 1, 0, 0], ![101, 215, 0, 1, 0], ![153, 214, 0, 0, 1]] where
  M :=![![![311, 15, -120, -59, -88], ![704, 324, -28, -5, -118], ![120, 343, 225, 95, 54], ![-568, 87, 316, 126, 154], ![-76, 502, 470, 252, 139]]]
  hmulB := by decide  
  f := ![![![-788443, 477087, -210304, 137191, -164444]], ![![1315552, -796042, 350904, -228911, 274382]], ![![268958, -162747, 71741, -46800, 56096]], ![![812819, -491838, 216808, -141434, 169528]], ![![638195, -386173, 170230, -111049, 133107]]]
  g := ![![![114, 172, -120, -59, -88], ![85, 117, -28, -5, -118], ![-137, -213, 225, 95, 54], ![-240, -361, 316, 126, 154], ![-325, -514, 470, 252, 139]]]
  hle1 := by decide   
  hle2 := by decide  


def P251P0 : CertificateIrreducibleZModOfList' 251 2 2 7 [241, 118, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [133, 250], [0, 1]]
 g := ![![[189, 25], [59, 28], [5], [160, 243], [62, 41], [209, 75], [133, 1]], ![[0, 226], [18, 223], [5], [100, 8], [244, 210], [144, 176], [15, 250]]]
 h' := ![![[133, 250], [88, 5], [101, 167], [94, 235], [118, 69], [82, 36], [75, 129], [0, 1]], ![[0, 1], [0, 246], [224, 84], [225, 16], [8, 182], [101, 215], [164, 122], [133, 250]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [131]]
 b := ![[], [225, 191]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI251N0 : CertifiedPrimeIdeal' SI251N0 251 where
  n := 2
  hpos := by decide
  P := [241, 118, 1]
  hirr := P251P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-193764, -42843, -45435, -192174, 34658]
  a := ![7, 47, 23, 0, -140]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![68826, 152450, -45435, -192174, 34658]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI251N0 : Ideal.IsPrime I251N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI251N0 B_one_repr
lemma NI251N0 : Nat.card (O ⧸ I251N0) = 63001 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI251N0

def I251N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5583, 578, 3276, -1274, -2272]] i)))

def SI251N1: IdealEqSpanCertificate' Table ![![-5583, 578, 3276, -1274, -2272]] 
 ![![251, 0, 0, 0, 0], ![0, 251, 0, 0, 0], ![141, 90, 1, 0, 0], ![111, 48, 0, 1, 0], ![80, 14, 0, 0, 1]] where
  M :=![![![-5583, 578, 3276, -1274, -2272], ![18176, 819, -840, 12370, -2548], ![1104, -3702, -13679, -10662, 13644], ![-63664, 2114, 21024, -28177, -9388], ![25000, 6088, 16896, 32120, -21775]]]
  hmulB := by decide  
  f := ![![![-46901, -22990, 972, 670, 7904]], ![![-63232, -70259, -31512, -14534, 1340]], ![![-48915, -38238, -10907, -4908, 4860]], ![![-32465, -23480, -5652, -2511, 3676]], ![![-18136, -11350, -1680, -708, 2473]]]
  g := ![![![-575, -802, 3276, -1274, -2272], ![-4114, -1919, -840, 12370, -2548], ![8055, 6168, -13679, -10662, 13644], ![3389, -1618, 21024, -28177, -9388], ![-16656, -10962, 16896, 32120, -21775]]]
  hle1 := by decide   
  hle2 := by decide  


def P251P1 : CertificateIrreducibleZModOfList' 251 2 2 7 [222, 116, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [135, 250], [0, 1]]
 g := ![![[247, 225], [60, 52], [125], [230, 196], [134, 51], [57, 243], [135, 1]], ![[0, 26], [52, 199], [125], [84, 55], [242, 200], [232, 8], [19, 250]]]
 h' := ![![[135, 250], [234, 15], [14, 110], [144, 171], [121, 14], [147, 94], [150, 182], [0, 1]], ![[0, 1], [0, 236], [55, 141], [137, 80], [3, 237], [36, 157], [122, 69], [135, 250]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [195]]
 b := ![[], [133, 223]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI251N1 : CertifiedPrimeIdeal' SI251N1 251 where
  n := 2
  hpos := by decide
  P := [222, 116, 1]
  hirr := P251P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16811, -2863, -4445, -18172, 440]
  a := ![1, 15, 8, -1, -43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![10326, 5033, -4445, -18172, 440]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI251N1 : Ideal.IsPrime I251N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI251N1 B_one_repr
lemma NI251N1 : Nat.card (O ⧸ I251N1) = 63001 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI251N1

def I251N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-105, -12, -22, -94, 42]] i)))

def SI251N2: IdealEqSpanCertificate' Table ![![-105, -12, -22, -94, 42]] 
 ![![251, 0, 0, 0, 0], ![130, 1, 0, 0, 0], ![19, 0, 1, 0, 0], ![206, 0, 0, 1, 0], ![165, 0, 0, 0, 1]] where
  M :=![![![-105, -12, -22, -94, 42], ![-336, 49, 248, -34, -188], ![920, -10, -229, 470, 60], ![-72, -154, -544, -507, 564], ![-1708, 84, 664, -672, -353]]]
  hmulB := by decide  
  f := ![![![51717, -31268, 13562, -9046, 10658]], ![![26446, -15987, 6932, -4626, 5448]], ![![4373, -2642, 1149, -764, 902]], ![![42234, -25534, 11076, -7387, 8704]], ![![34183, -20664, 8966, -5978, 7045]]]
  g := ![![![57, -12, -22, -94, 42], ![106, 49, 248, -34, -188], ![-399, -10, -229, 470, 60], ![166, -154, -544, -507, 564], ![683, 84, 664, -672, -353]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N2 : Nat.card (O ⧸ I251N2) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N2)

lemma isPrimeI251N2 : Ideal.IsPrime I251N2 := prime_ideal_of_norm_prime hp251.out _ NI251N2
def MulI251N0 : IdealMulLeCertificate' Table 
  ![![311, 15, -120, -59, -88]] ![![-5583, 578, 3276, -1274, -2272]]
  ![![-39977, -24187, -79548, -95341, 88000]] where
 M := ![![![-39977, -24187, -79548, -95341, 88000]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI251N1 : IdealMulLeCertificate' Table 
  ![![-39977, -24187, -79548, -95341, 88000]] ![![-105, -12, -22, -94, 42]]
  ![![251, 0, 0, 0, 0]] where
 M := ![![![-204299191, 22164555, 123395114, -43605477, -86741082]]]
 hmul := by decide  
 g := ![![![![-813941, 88305, 491614, -173727, -345582]]]]
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


lemma PB324I5_primes (p : ℕ) :
  p ∈ Set.range ![199, 211, 223, 227, 229, 233, 239, 241, 251] ↔ Nat.Prime p ∧ 197 < p ∧ p ≤ 251 := by
  rw [← List.mem_ofFn']
  convert primes_range 197 251 (by omega)

def PB324I5 : PrimesBelowBoundCertificateInterval O 197 251 324 where
  m := 9
  g := ![2, 2, 2, 1, 3, 2, 3, 1, 3]
  P := ![199, 211, 223, 227, 229, 233, 239, 241, 251]
  hP := PB324I5_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I199N0, I199N1]
    · exact ![I211N0, I211N1]
    · exact ![I223N0, I223N1]
    · exact ![I227N0]
    · exact ![I229N0, I229N1, I229N2]
    · exact ![I233N0, I233N1]
    · exact ![I239N0, I239N1, I239N2]
    · exact ![I241N0]
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
    · exact ![7880599, 39601]
    · exact ![1982119441, 211]
    · exact ![2472973441, 223]
    · exact ![602738989907]
    · exact ![12008989, 229, 229]
    · exact ![12649337, 54289]
    · exact ![57121, 57121, 239]
    · exact ![812990017201]
    · exact ![63001, 63001, 251]
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
    · dsimp ; intro j
      fin_cases j
      exact NI227N0
    · dsimp ; intro j
      fin_cases j
      exact NI229N0
      exact NI229N1
      exact NI229N2
    · dsimp ; intro j
      fin_cases j
      exact NI233N0
      exact NI233N1
    · dsimp ; intro j
      fin_cases j
      exact NI239N0
      exact NI239N1
      exact NI239N2
    · dsimp ; intro j
      fin_cases j
      exact NI241N0
    · dsimp ; intro j
      fin_cases j
      exact NI251N0
      exact NI251N1
      exact NI251N2
  β := ![I211N1, I223N1, I229N1, I229N2, I239N2, I251N2]
  Il := ![[], [I211N1], [I223N1], [], [I229N1, I229N2], [], [I239N2], [], [I251N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
