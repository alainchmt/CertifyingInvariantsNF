
import IdealArithmetic.Examples.NF5_1_27000000_1.RI5_1_27000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp257 : Fact (Nat.Prime 257) := {out := by norm_num}

def I257N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-137, -231, -135, -64, -11]] i)))

def SI257N0: IdealEqSpanCertificate' Table ![![-137, -231, -135, -64, -11]] 
 ![![257, 0, 0, 0, 0], ![0, 257, 0, 0, 0], ![0, 0, 257, 0, 0], ![0, 0, 0, 257, 0], ![176, 21, 59, 146, 1]] where
  M :=![![![-137, -231, -135, -64, -11], ![88, -375, -356, -184, -128], ![468, 50, -141, -44, -120], ![436, 420, 152, 93, 20], ![694, 296, -74, -96, -145]]]
  hmulB := by decide  
  f := ![![![25, -15, 7, -4, 5]], ![![-40, 25, -12, 8, -8]], ![![52, -34, 15, -12, 12]], ![![-28, 16, -4, 5, -8]], ![![10, -7, 5, -2, 1]]]
  g := ![![![7, 0, 2, 6, -11], ![88, 9, 28, 72, -128], ![84, 10, 27, 68, -120], ![-12, 0, -4, -11, 20], ![102, 13, 33, 82, -145]]]
  hle1 := by decide   
  hle2 := by decide  


def P257P0 : CertificateIrreducibleZModOfList' 257 4 2 8 [32, 117, 121, 50, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [227, 212, 248, 188], [240, 197, 104, 59], [254, 104, 162, 10], [0, 1]]
 g := ![![[17, 109, 51, 241], [125, 93, 31], [4, 44, 197], [179, 215, 241], [110, 249, 159], [111, 180, 187], [1], []], ![[33, 24, 46, 89, 62, 106], [133, 129, 195], [104, 226, 215], [1, 208, 225], [3, 132, 196], [143, 225, 8], [207, 148, 95], [132, 146, 135]], ![[184, 21, 153, 197, 223, 158], [103, 107, 225], [248, 232, 165], [116, 22, 223], [107, 194, 121], [46, 21, 25], [238, 190, 29], [242, 132, 140]], ![[6, 16, 207, 124, 184, 138], [211, 166, 123], [68, 178, 26], [36, 63, 137], [33, 215, 114], [238, 119, 42], [179, 32, 169], [139, 39, 100]]]
 h' := ![![[227, 212, 248, 188], [99, 144, 44, 193], [191, 70, 62, 206], [233, 13, 123, 222], [43, 240, 142, 64], [42, 49, 233, 38], [225, 140, 136, 207], [0, 0, 1], [0, 1]], ![[240, 197, 104, 59], [25, 191, 7, 198], [13, 132, 48, 127], [0, 145, 187, 230], [240, 114, 5, 15], [183, 234, 61, 14], [90, 70, 67, 137], [17, 60, 143, 98], [227, 212, 248, 188]], ![[254, 104, 162, 10], [24, 147, 140, 30], [39, 253, 144, 242], [120, 79, 133, 200], [157, 76, 11, 134], [165, 159, 167, 11], [98, 172, 207, 252], [255, 85, 202, 172], [240, 197, 104, 59]], ![[0, 1], [129, 32, 66, 93], [126, 59, 3, 196], [195, 20, 71, 119], [233, 84, 99, 44], [2, 72, 53, 194], [200, 132, 104, 175], [187, 112, 168, 244], [254, 104, 162, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [150, 31, 205], []]
 b := ![[], [], [116, 100, 128, 88], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N0 : CertifiedPrimeIdeal' SI257N0 257 where
  n := 4
  hpos := by decide
  P := [32, 117, 121, 50, 1]
  hirr := P257P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-54116194, 54629766, 231706755, 160824771, -229321881]
  a := ![0, 8, 5, -1, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![156834766, 18950931, 53547462, 130902021, -229321881]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI257N0 : Ideal.IsPrime I257N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI257N0 B_one_repr
lemma NI257N0 : Nat.card (O ⧸ I257N0) = 4362470401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI257N0

def I257N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25, -15, 7, -4, 5]] i)))

def SI257N1: IdealEqSpanCertificate' Table ![![25, -15, 7, -4, 5]] 
 ![![257, 0, 0, 0, 0], ![222, 1, 0, 0, 0], ![176, 0, 1, 0, 0], ![142, 0, 0, 1, 0], ![127, 0, 0, 0, 1]] where
  M :=![![![25, -15, 7, -4, 5], ![-40, 25, -12, 8, -8], ![52, -34, 15, -12, 12], ![-28, 16, -4, 5, -8], ![30, -14, 4, 0, 5]]]
  hmulB := by decide  
  f := ![![![-137, -231, -135, -64, -11]], ![![-118, -201, -118, -56, -10]], ![![-92, -158, -93, -44, -8]], ![![-74, -126, -74, -35, -6]], ![![-65, -113, -67, -32, -6]]]
  g := ![![![8, -15, 7, -4, 5], ![-14, 25, -12, 8, -8], ![20, -34, 15, -12, 12], ![-10, 16, -4, 5, -8], ![7, -14, 4, 0, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI257N1 : Nat.card (O ⧸ I257N1) = 257 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI257N1)

lemma isPrimeI257N1 : Ideal.IsPrime I257N1 := prime_ideal_of_norm_prime hp257.out _ NI257N1
def MulI257N0 : IdealMulLeCertificate' Table 
  ![![-137, -231, -135, -64, -11]] ![![25, -15, 7, -4, 5]]
  ![![257, 0, 0, 0, 0]] where
 M := ![![![257, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC257 : ContainsPrimesAboveP 257 ![I257N0, I257N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI257N0
    exact isPrimeI257N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 257 (by decide) (𝕀 ⊙ MulI257N0)
instance hp263 : Fact (Nat.Prime 263) := {out := by norm_num}

def I263N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3065, 224, 1665, -897, -1061]] i)))

def SI263N0: IdealEqSpanCertificate' Table ![![-3065, 224, 1665, -897, -1061]] 
 ![![263, 0, 0, 0, 0], ![0, 263, 0, 0, 0], ![0, 0, 263, 0, 0], ![8, 24, 127, 1, 0], ![40, 67, 132, 0, 1]] where
  M :=![![![-3065, 224, 1665, -897, -1061], ![8488, 618, 120, 6349, -1794], ![2932, -2045, -7585, -4435, 7246], ![-33228, 777, 9576, -15788, -3538], ![8958, 3312, 10350, 15028, -12105]]]
  hmulB := by decide  
  f := ![![![7119, -2554, -5187, -2475, -2627]], ![![21016, 4328, -5412, -2645, -4950]], ![![9292, 10447, 4729, 2183, -170]], ![![6584, 5392, 1673, 757, -596]], ![![11126, 6026, 252, 67, -1737]]]
  g := ![![![177, 353, 972, -897, -1061], ![112, -120, -2165, 6349, -1794], ![-956, -1449, -1524, -4435, 7246], ![892, 2345, 9436, -15788, -3538], ![1418, 1725, -1142, 15028, -12105]]]
  hle1 := by decide   
  hle2 := by decide  


def P263P0 : CertificateIrreducibleZModOfList' 263 3 2 8 [111, 89, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [247, 187, 210], [7, 75, 53], [0, 1]]
 g := ![![[166, 261, 223], [56, 12, 205], [47, 183, 74], [25, 133], [180, 31], [219, 64], [254, 1], []], ![[56, 79, 130, 140], [152, 6, 176, 138], [182, 92, 162, 13], [262, 207], [133, 61], [109, 205], [82, 102], [133, 179]], ![[252, 176, 7, 174], [172, 63, 14, 175], [202, 59, 44, 239], [43, 234], [230, 140], [251, 83], [139, 253], [27, 179]]]
 h' := ![![[247, 187, 210], [96, 4, 152], [43, 251, 87], [258, 50, 211], [156, 235, 213], [66, 205, 89], [210, 164, 255], [0, 0, 1], [0, 1]], ![[7, 75, 53], [223, 8, 142], [0, 177, 60], [64, 149, 25], [74, 129, 101], [149, 92, 18], [26, 19, 176], [221, 182, 75], [247, 187, 210]], ![[0, 1], [180, 251, 232], [171, 98, 116], [49, 64, 27], [80, 162, 212], [25, 229, 156], [220, 80, 95], [208, 81, 187], [7, 75, 53]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [258, 260], []]
 b := ![[], [31, 246, 124], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI263N0 : CertifiedPrimeIdeal' SI263N0 263 where
  n := 3
  hpos := by decide
  P := [111, 89, 9, 1]
  hirr := P263P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![16195182, -2185825, -9721183, 4405409, 6945592]
  a := ![3, -5, -3, -1, -52]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1128790, -2179735, -5650290, 4405409, 6945592]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI263N0 : Ideal.IsPrime I263N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI263N0 B_one_repr
lemma NI263N0 : Nat.card (O ⧸ I263N0) = 18191447 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI263N0

def I263N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-105, -99, -337, -358, 361]] i)))

def SI263N1: IdealEqSpanCertificate' Table ![![-105, -99, -337, -358, 361]] 
 ![![263, 0, 0, 0, 0], ![59, 1, 0, 0, 0], ![71, 0, 1, 0, 0], ![243, 0, 0, 1, 0], ![184, 0, 0, 0, 1]] where
  M :=![![![-105, -99, -337, -358, 361], ![-2888, 175, 1240, -1038, -716], ![4308, 214, -123, 2994, -680], ![4164, -882, -4080, -421, 3352], ![-9906, -30, 1968, -5476, -141]]]
  hmulB := by decide  
  f := ![![![36863, -8953, -23189, -11114, -12537]], ![![8651, -1906, -5281, -2532, -2897]], ![![10099, -2227, -6164, -2956, -3381]], ![![33855, -8151, -21237, -10179, -11497]], ![![25870, -5948, -15994, -7668, -8719]]]
  g := ![![![191, -99, -337, -358, 361], ![1075, 175, 1240, -1038, -716], ![-2289, 214, -123, 2994, -680], ![-641, -882, -4080, -421, 3352], ![4596, -30, 1968, -5476, -141]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI263N1 : Nat.card (O ⧸ I263N1) = 263 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI263N1)

lemma isPrimeI263N1 : Ideal.IsPrime I263N1 := prime_ideal_of_norm_prime hp263.out _ NI263N1

def I263N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-35, 21, -9, 6, -7]] i)))

def SI263N2: IdealEqSpanCertificate' Table ![![-35, 21, -9, 6, -7]] 
 ![![263, 0, 0, 0, 0], ![214, 1, 0, 0, 0], ![139, 0, 1, 0, 0], ![11, 0, 0, 1, 0], ![102, 0, 0, 0, 1]] where
  M :=![![![-35, 21, -9, 6, -7], ![56, -35, 16, -10, 12], ![-76, 46, -21, 14, -16], ![36, -22, 8, -7, 8], ![-34, 18, -8, 4, -7]]]
  hmulB := by decide  
  f := ![![![-67, -89, -41, -22, -17]], ![![-54, -73, -34, -18, -14]], ![![-35, -47, -22, -12, -9]], ![![-3, -3, -1, -1, -1]], ![![-24, -34, -16, -8, -7]]]
  g := ![![![-10, 21, -9, 6, -7], ![16, -35, 16, -10, 12], ![-21, 46, -21, 14, -16], ![11, -22, 8, -7, 8], ![-8, 18, -8, 4, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI263N2 : Nat.card (O ⧸ I263N2) = 263 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI263N2)

lemma isPrimeI263N2 : Ideal.IsPrime I263N2 := prime_ideal_of_norm_prime hp263.out _ NI263N2
def MulI263N0 : IdealMulLeCertificate' Table 
  ![![-3065, 224, 1665, -897, -1061]] ![![-105, -99, -337, -358, 361]]
  ![![13622891, 1521929, 2677582, 12037441, -5256192]] where
 M := ![![![13622891, 1521929, 2677582, 12037441, -5256192]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI263N1 : IdealMulLeCertificate' Table 
  ![![13622891, 1521929, 2677582, 12037441, -5256192]] ![![-35, 21, -9, 6, -7]]
  ![![263, 0, 0, 0, 0]] where
 M := ![![![16989011, -3453190, -16135313, -1282651, 13154471]]]
 hmul := by decide  
 g := ![![![![64597, -13130, -61351, -4877, 50017]]]]
 hle2 := by decide  


def PBC263 : ContainsPrimesAboveP 263 ![I263N0, I263N1, I263N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI263N0
    exact isPrimeI263N1
    exact isPrimeI263N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 263 (by decide) (𝕀 ⊙ MulI263N0 ⊙ MulI263N1)
instance hp269 : Fact (Nat.Prime 269) := {out := by norm_num}

def I269N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![27069613, -16379838, 7220367, -4710203, 5645869]] i)))

def SI269N0: IdealEqSpanCertificate' Table ![![27069613, -16379838, 7220367, -4710203, 5645869]] 
 ![![269, 0, 0, 0, 0], ![0, 269, 0, 0, 0], ![0, 0, 269, 0, 0], ![0, 0, 0, 269, 0], ![154, 15, 190, 255, 1]] where
  M :=![![![27069613, -16379838, 7220367, -4710203, 5645869], ![-45166952, 27330548, -12047532, 7859199, -9420406], ![60265100, -36466441, 16074709, -10486325, 12569402], ![-27694132, 16757735, -7386948, 4818870, -5776122], ![24355570, -14737568, 6496446, -4237952, 5079805]]]
  hmulB := by decide  
  f := ![![![-1, 36, 33, 13, 1]], ![![-8, 42, 48, 51, 26]], ![![-100, -31, -7, -29, 38]], ![![-148, -61, 12, -56, -42]], ![![-212, -57, 28, -63, -11]]]
  g := ![![![-3131577, -375717, -3960947, -5369542, 5645869], ![5225188, 626902, 6609032, 8959341, -9420406], ![-6971832, -836459, -8818259, -11954215, 12569402], ![3203824, 384385, 4052328, 5493420, -5776122], ![-2817600, -338047, -3563816, -4831183, 5079805]]]
  hle1 := by decide   
  hle2 := by decide  


def P269P0 : CertificateIrreducibleZModOfList' 269 4 2 8 [192, 128, 126, 166, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 119, 192, 24], [80, 93, 55, 268], [22, 56, 22, 246], [0, 1]]
 g := ![![[7, 103, 100, 30], [77, 227, 97], [62, 211, 109, 245], [122, 141, 195, 213], [227, 259, 24], [254, 186, 118], [1], []], ![[156, 67, 107, 69, 265, 20], [217, 255, 41], [17, 120, 100, 92, 46, 105], [44, 9, 221, 52, 222, 23], [173, 237, 9], [109, 84, 103], [63, 154, 202], [255, 218, 38]], ![[180, 105, 197, 92, 74, 84], [82, 122, 150], [125, 268, 236, 110, 139, 118], [46, 241, 248, 97, 129, 202], [118, 215, 67], [111, 168, 218], [267, 209, 49], [109, 262, 1]], ![[84, 184, 215, 168, 262, 253], [147, 25, 138], [104, 202, 44, 0, 177, 173], [215, 196, 164, 94, 68, 213], [117, 162, 1], [181, 56, 30], [207, 194, 258], [268, 213, 260]]]
 h' := ![![[1, 119, 192, 24], [62, 144, 88, 90], [201, 144, 169, 108], [248, 225, 19, 75], [45, 127, 109, 189], [201, 27, 19, 232], [77, 141, 143, 103], [0, 0, 1], [0, 1]], ![[80, 93, 55, 268], [150, 129, 27, 254], [53, 144, 158, 93], [122, 227, 49, 24], [184, 231, 244, 47], [154, 92, 115, 266], [10, 56, 58, 60], [268, 255, 208, 134], [1, 119, 192, 24]], ![[22, 56, 22, 246], [157, 162, 154, 67], [90, 13, 189, 42], [183, 152, 193, 107], [110, 218, 90, 228], [112, 135, 30, 41], [119, 267, 90, 196], [267, 120, 115, 262], [80, 93, 55, 268]], ![[0, 1], [141, 103, 0, 127], [180, 237, 22, 26], [192, 203, 8, 63], [68, 231, 95, 74], [118, 15, 105, 268], [13, 74, 247, 179], [138, 163, 214, 142], [22, 56, 22, 246]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [144, 86, 28], []]
 b := ![[], [], [68, 23, 87, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI269N0 : CertifiedPrimeIdeal' SI269N0 269 where
  n := 4
  hpos := by decide
  P := [192, 128, 126, 166, 1]
  hirr := P269P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![44856749, -2025, -2753579, 31651892, -7226820]
  a := ![1, 3, 2, -1, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![4304041, 402975, 5094209, 6968368, -7226820]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI269N0 : Ideal.IsPrime I269N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI269N0 B_one_repr
lemma NI269N0 : Nat.card (O ⧸ I269N0) = 5236114321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI269N0

def I269N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -36, -33, -13, -1]] i)))

def SI269N1: IdealEqSpanCertificate' Table ![![1, -36, -33, -13, -1]] 
 ![![269, 0, 0, 0, 0], ![28, 1, 0, 0, 0], ![132, 0, 1, 0, 0], ![21, 0, 0, 1, 0], ![11, 0, 0, 0, 1]] where
  M :=![![![1, -36, -33, -13, -1], ![8, -42, -48, -51, -26], ![100, 31, 7, 29, -38], ![148, 61, -12, 56, 42], ![14, 62, 0, -76, 13]]]
  hmulB := by decide  
  f := ![![![-27069613, 16379838, -7220367, 4710203, -5645869]], ![![-2649748, 1603364, -706776, 461065, -552654]], ![![-13507264, 8173253, -3602837, 2350309, -2817190]], ![![-2010289, 1216427, -536211, 349797, -419283]], ![![-1197477, 724594, -319407, 208365, -249756]]]
  g := ![![![21, -36, -33, -13, -1], ![33, -42, -48, -51, -26], ![-7, 31, 7, 29, -38], ![-6, 61, -12, 56, 42], ![-1, 62, 0, -76, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI269N1 : Nat.card (O ⧸ I269N1) = 269 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI269N1)

lemma isPrimeI269N1 : Ideal.IsPrime I269N1 := prime_ideal_of_norm_prime hp269.out _ NI269N1
def MulI269N0 : IdealMulLeCertificate' Table 
  ![![27069613, -16379838, 7220367, -4710203, 5645869]] ![![1, -36, -33, -13, -1]]
  ![![269, 0, 0, 0, 0]] where
 M := ![![![-269, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC269 : ContainsPrimesAboveP 269 ![I269N0, I269N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI269N0
    exact isPrimeI269N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 269 (by decide) (𝕀 ⊙ MulI269N0)
instance hp271 : Fact (Nat.Prime 271) := {out := by norm_num}

def I271N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19801, 24278, 11757, 5443, 113]] i)))

def SI271N0: IdealEqSpanCertificate' Table ![![19801, 24278, 11757, 5443, 113]] 
 ![![271, 0, 0, 0, 0], ![0, 271, 0, 0, 0], ![0, 0, 271, 0, 0], ![0, 0, 0, 271, 0], ![216, 11, 164, 5, 1]] where
  M :=![![![19801, 24278, 11757, 5443, 113], ![-904, 44950, 37896, 17845, 10886], ![-43092, 651, 19043, 9165, 12402], ![-49156, -43339, -15060, -6864, 3722], ![-83462, -22982, 16656, 8228, 18285]]]
  hmulB := by decide  
  f := ![![![-327, 184, -75, 41, -65]], ![![520, -300, 156, -61, 82]], ![![-588, 399, -235, 135, -102]], ![![148, -197, 84, -170, 94]], ![![-594, 373, -194, 109, -109]]]
  g := ![![![-17, 85, -25, 18, 113], ![-8680, -276, -6448, -135, 10886], ![-10044, -501, -7435, -195, 12402], ![-3148, -311, -2308, -94, 3722], ![-14882, -827, -11004, -307, 18285]]]
  hle1 := by decide   
  hle2 := by decide  


def P271P0 : CertificateIrreducibleZModOfList' 271 4 2 8 [81, 217, 171, 10, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [112, 208, 165, 115], [106, 209, 52, 243], [43, 124, 54, 184], [0, 1]]
 g := ![![[12, 141, 166, 166], [207, 262, 180, 185], [19, 199, 44, 62], [159, 105, 24, 10], [113, 4, 259], [140, 252, 100], [1], []], ![[53, 163, 249, 257, 190, 266], [259, 33, 17, 263, 149, 47], [169, 221, 118, 75, 21, 262], [84, 173, 269, 49, 214, 24], [97, 217, 224], [237, 73, 228], [184, 166, 233], [209, 8, 217]], ![[114, 161, 58, 253, 69, 15], [111, 31, 106, 206, 44, 33], [148, 248, 59, 174, 146, 266], [228, 140, 21, 236, 101, 189], [26, 243, 200], [147, 232, 158], [254, 213, 32], [228, 88, 242]], ![[93, 139, 79, 78, 103, 255], [68, 94, 119, 159, 260, 133], [130, 27, 170, 22, 204, 132], [128, 81, 3, 127, 105, 249], [93, 237, 217], [112, 207, 219], [135, 242, 228], [227, 8, 252]]]
 h' := ![![[112, 208, 165, 115], [35, 235, 192, 232], [87, 193, 171, 166], [129, 206, 249, 182], [106, 209, 33, 84], [99, 80, 262, 157], [190, 54, 100, 261], [0, 0, 1], [0, 1]], ![[106, 209, 52, 243], [67, 246, 264, 169], [106, 260, 152, 257], [253, 260, 166, 231], [114, 123, 213, 149], [58, 28, 86, 123], [234, 89, 109, 109], [222, 49, 240, 222], [112, 208, 165, 115]], ![[43, 124, 54, 184], [116, 85, 55, 177], [70, 98, 234, 12], [21, 210, 45, 160], [228, 78, 20, 221], [39, 79, 180, 147], [201, 160, 33, 126], [85, 170, 54, 158], [106, 209, 52, 243]], ![[0, 1], [249, 247, 31, 235], [146, 262, 256, 107], [247, 137, 82, 240], [25, 132, 5, 88], [90, 84, 14, 115], [225, 239, 29, 46], [264, 52, 247, 162], [43, 124, 54, 184]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [155, 8, 138], []]
 b := ![[], [], [127, 156, 244, 63], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI271N0 : CertifiedPrimeIdeal' SI271N0 271 where
  n := 4
  hpos := by decide
  P := [81, 217, 171, 10, 1]
  hirr := P271P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![63079754, 816944805, 3033888879, 2621674359, -3074017437]
  a := ![1, -11, -7, -1, 47]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2450372126, 127790172, 1871486157, 66390264, -3074017437]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI271N0 : Ideal.IsPrime I271N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI271N0 B_one_repr
lemma NI271N0 : Nat.card (O ⧸ I271N0) = 5393580481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI271N0

def I271N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![327, -184, 75, -41, 65]] i)))

def SI271N1: IdealEqSpanCertificate' Table ![![327, -184, 75, -41, 65]] 
 ![![271, 0, 0, 0, 0], ![261, 1, 0, 0, 0], ![226, 0, 1, 0, 0], ![51, 0, 0, 1, 0], ![90, 0, 0, 0, 1]] where
  M :=![![![327, -184, 75, -41, 65], ![-520, 300, -156, 61, -82], ![588, -399, 235, -135, 102], ![-148, 197, -84, 170, -94], ![370, -188, -30, -64, 143]]]
  hmulB := by decide  
  f := ![![![-19801, -24278, -11757, -5443, -113]], ![![-19067, -23548, -11463, -5308, -149]], ![![-16354, -20249, -9875, -4573, -140]], ![![-3545, -4409, -2157, -999, -35]], ![![-6268, -7978, -3966, -1838, -105]]]
  g := ![![![102, -184, 75, -41, 65], ![-145, 300, -156, 61, -82], ![182, -399, 235, -135, 102], ![-121, 197, -84, 170, -94], ![172, -188, -30, -64, 143]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI271N1 : Nat.card (O ⧸ I271N1) = 271 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI271N1)

lemma isPrimeI271N1 : Ideal.IsPrime I271N1 := prime_ideal_of_norm_prime hp271.out _ NI271N1
def MulI271N0 : IdealMulLeCertificate' Table 
  ![![19801, 24278, 11757, 5443, 113]] ![![327, -184, 75, -41, 65]]
  ![![271, 0, 0, 0, 0]] where
 M := ![![![-271, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC271 : ContainsPrimesAboveP 271 ![I271N0, I271N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI271N0
    exact isPrimeI271N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 271 (by decide) (𝕀 ⊙ MulI271N0)
instance hp277 : Fact (Nat.Prime 277) := {out := by norm_num}

def I277N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![277, 0, 0, 0, 0]] i)))

def SI277N0: IdealEqSpanCertificate' Table ![![277, 0, 0, 0, 0]] 
 ![![277, 0, 0, 0, 0], ![0, 277, 0, 0, 0], ![0, 0, 277, 0, 0], ![0, 0, 0, 277, 0], ![0, 0, 0, 0, 277]] where
  M :=![![![277, 0, 0, 0, 0], ![0, 277, 0, 0, 0], ![0, 0, 277, 0, 0], ![0, 0, 0, 277, 0], ![0, 0, 0, 0, 277]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P277P0 : CertificateIrreducibleZModOfList' 277 5 2 8 [151, 51, 43, 5, 180, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 6, 130, 99, 178], [223, 224, 52, 26, 52], [57, 224, 13, 239, 69], [57, 99, 82, 190, 255], [0, 1]]
 g := ![![[130, 8, 74, 231, 25], [20, 193, 131, 237], [34, 182, 151, 128, 108], [50, 102, 22, 256], [262, 236, 89, 162, 34], [53, 263, 97, 1], [], []], ![[253, 24, 70, 146, 57, 130, 7, 99], [42, 49, 30, 267], [211, 69, 175, 13, 162, 105, 63, 119], [80, 113, 127, 9], [54, 226, 174, 153, 27, 268, 81, 269], [39, 245, 125, 220], [198, 274, 126, 100], [29, 239, 98, 106]], ![[2, 176, 92, 275, 2, 90, 39, 258], [252, 164, 232, 192], [232, 169, 98, 216, 1, 124, 204, 79], [94, 11, 24, 92], [264, 162, 238, 170, 170, 222, 276, 39], [33, 73, 27, 66], [267, 216, 68, 41], [19, 52, 180, 211]], ![[99, 19, 201, 259, 19, 186, 105, 59], [252, 87, 15, 52], [145, 52, 267, 269, 61, 260, 115, 130], [232, 14, 177, 41], [267, 2, 138, 256, 236, 143, 234, 171], [129, 9, 127, 117], [90, 276, 262, 4], [250, 198, 77, 52]], ![[99, 79, 168, 218, 145, 105, 175, 3], [131, 256, 263, 147], [226, 107, 261, 176, 115, 243, 79, 258], [276, 28, 225, 255], [136, 19, 191, 242, 180, 158, 92, 67], [213, 121, 264, 222], [205, 261, 211, 160], [267, 91, 85, 207]]]
 h' := ![![[37, 6, 130, 99, 178], [48, 186, 146, 164, 272], [129, 123, 263, 107, 121], [114, 158, 273, 219, 51], [49, 100, 216, 204, 261], [30, 242, 131, 225, 158], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[223, 224, 52, 26, 52], [28, 76, 182, 217, 217], [217, 153, 83, 255, 78], [148, 239, 173, 9, 157], [58, 170, 157, 245, 3], [209, 159, 236, 52, 200], [2, 160, 51, 135, 142], [37, 271, 258, 174, 267], [37, 6, 130, 99, 178]], ![[57, 224, 13, 239, 69], [41, 260, 136, 112, 145], [12, 147, 130, 44, 68], [124, 175, 70, 106, 171], [70, 265, 80, 238, 107], [77, 263, 23, 39, 65], [118, 35, 122, 19, 204], [47, 227, 61, 107, 128], [223, 224, 52, 26, 52]], ![[57, 99, 82, 190, 255], [108, 178, 239, 127, 149], [52, 201, 166, 191, 208], [58, 66, 255, 30, 119], [241, 67, 197, 115, 128], [52, 87, 191, 227, 79], [124, 134, 260, 180, 35], [124, 62, 70, 170, 275], [57, 224, 13, 239, 69]], ![[0, 1], [197, 131, 128, 211, 48], [158, 207, 189, 234, 79], [121, 193, 60, 190, 56], [168, 229, 181, 29, 55], [205, 80, 250, 11, 52], [76, 225, 121, 220, 172], [50, 271, 164, 103, 161], [57, 99, 82, 190, 255]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 127, 104, 95], [], [], []]
 b := ![[], [243, 271, 141, 88, 222], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI277N0 : CertifiedPrimeIdeal' SI277N0 277 where
  n := 5
  hpos := by decide
  P := [151, 51, 43, 5, 180, 1]
  hirr := P277P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-466320804139, 14092096338, 153032052114, -206215890900, -68558992476]
  a := ![-1, 13, 9, 2, -30]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1683468607, 50873994, 552462282, -744461700, -247505388]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI277N0 : Ideal.IsPrime I277N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI277N0 B_one_repr
lemma NI277N0 : Nat.card (O ⧸ I277N0) = 1630793025157 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI277N0

def PBC277 : ContainsPrimesAboveP 277 ![I277N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI277N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![277, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 277 (by decide) 𝕀

instance hp281 : Fact (Nat.Prime 281) := {out := by norm_num}

def I281N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 14, -6, 10, -4]] i)))

def SI281N0: IdealEqSpanCertificate' Table ![![-3, 14, -6, 10, -4]] 
 ![![281, 0, 0, 0, 0], ![0, 281, 0, 0, 0], ![0, 0, 281, 0, 0], ![180, 103, 46, 1, 0], ![240, 254, 257, 0, 1]] where
  M :=![![![-3, 14, -6, 10, -4], ![32, -15, 0, -14, 20], ![-96, 30, 19, -6, -24], ![80, -10, 12, 53, -16], ![40, -2, -54, 8, 41]]]
  hmulB := by decide  
  f := ![![![13, 2, -6, -2, -4]], ![![32, 13, 0, -2, -4]], ![![0, 18, 11, 6, 0]], ![![20, 9, -2, -1, -4]], ![![40, 30, 5, 2, -7]]]
  g := ![![![-3, 0, 2, 10, -4], ![-8, -13, -16, -14, 20], ![24, 24, 23, -6, -24], ![-20, -5, 6, 53, -16], ![-40, -40, -39, 8, 41]]]
  hle1 := by decide   
  hle2 := by decide  


def P281P0 : CertificateIrreducibleZModOfList' 281 3 2 8 [271, 126, 79, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [48, 240, 82], [154, 40, 199], [0, 1]]
 g := ![![[61, 215, 241], [121, 132], [96, 50], [55, 172, 90], [62, 2, 209], [127, 274], [202, 1], []], ![[80, 50, 96, 204], [153, 7], [228, 271], [278, 86, 247, 96], [86, 107, 87, 26], [33, 57], [183, 195], [195, 261]], ![[97, 258, 54, 41], [59, 121], [137, 17], [168, 40, 280, 174], [86, 82, 167, 21], [180, 245], [159, 276], [78, 261]]]
 h' := ![![[48, 240, 82], [205, 140, 135], [261, 112, 91], [269, 121, 98], [58, 26, 86], [145, 131, 107], [53, 129, 214], [0, 0, 1], [0, 1]], ![[154, 40, 199], [107, 122, 20], [194, 115, 179], [64, 0, 73], [164, 208, 233], [209, 37, 129], [260, 188, 30], [39, 237, 40], [48, 240, 82]], ![[0, 1], [280, 19, 126], [50, 54, 11], [101, 160, 110], [127, 47, 243], [272, 113, 45], [57, 245, 37], [49, 44, 240], [154, 40, 199]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 23], []]
 b := ![[], [267, 65, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI281N0 : CertifiedPrimeIdeal' SI281N0 281 where
  n := 3
  hpos := by decide
  P := [271, 126, 79, 1]
  hirr := P281P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-22545, 23412, 125736, 71804, -110024]
  a := ![0, -10, -6, -10, 8]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![47895, 73216, 89320, 71804, -110024]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI281N0 : Ideal.IsPrime I281N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI281N0 B_one_repr
lemma NI281N0 : Nat.card (O ⧸ I281N0) = 22188041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI281N0

def I281N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13, -2, 6, 2, 4]] i)))

def SI281N1: IdealEqSpanCertificate' Table ![![-13, -2, 6, 2, 4]] 
 ![![281, 0, 0, 0, 0], ![0, 281, 0, 0, 0], ![50, 236, 1, 0, 0], ![2, 226, 0, 1, 0], ![272, 235, 0, 0, 1]] where
  M :=![![![-13, -2, 6, 2, 4], ![-32, -13, 0, 2, 4], ![0, -18, -11, -6, 0], ![16, -2, -12, -9, -8], ![8, -22, -18, -8, -9]]]
  hmulB := by decide  
  f := ![![![3, -14, 6, -10, 4]], ![![-32, 15, 0, 14, -20]], ![![-26, 10, 1, 10, -16]], ![![-26, 12, 0, 11, -16]], ![![-24, -1, 6, 2, -13]]]
  g := ![![![-5, -10, 6, 2, 4], ![-4, -5, 0, 2, 4], ![2, 14, -11, -6, 0], ![10, 24, -12, -9, -8], ![12, 29, -18, -8, -9]]]
  hle1 := by decide   
  hle2 := by decide  


def P281P1 : CertificateIrreducibleZModOfList' 281 2 2 8 [49, 105, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [176, 280], [0, 1]]
 g := ![![[243, 195], [28], [70], [85, 175], [91, 33], [144], [66], [1]], ![[0, 86], [28], [70], [256, 106], [279, 248], [144], [66], [1]]]
 h' := ![![[176, 280], [15, 241], [194, 77], [50, 167], [37, 52], [69, 95], [10, 269], [232, 176], [0, 1]], ![[0, 1], [0, 40], [258, 204], [218, 114], [197, 229], [210, 186], [146, 12], [17, 105], [176, 280]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [271, 147]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI281N1 : CertifiedPrimeIdeal' SI281N1 281 where
  n := 2
  hpos := by decide
  P := [49, 105, 1]
  hirr := P281P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5271, -12, -517, -6493, -1419]
  a := ![13, 10, 7, 1, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1493, 6843, -517, -6493, -1419]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI281N1 : Ideal.IsPrime I281N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI281N1 B_one_repr
lemma NI281N1 : Nat.card (O ⧸ I281N1) = 78961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI281N1
def MulI281N0 : IdealMulLeCertificate' Table 
  ![![-3, 14, -6, 10, -4]] ![![-13, -2, 6, 2, 4]]
  ![![281, 0, 0, 0, 0]] where
 M := ![![![-281, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC281 : ContainsPrimesAboveP 281 ![I281N0, I281N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI281N0
    exact isPrimeI281N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 281 (by decide) (𝕀 ⊙ MulI281N0)
instance hp283 : Fact (Nat.Prime 283) := {out := by norm_num}

def I283N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1063, -688, 107, -327, 397]] i)))

def SI283N0: IdealEqSpanCertificate' Table ![![1063, -688, 107, -327, 397]] 
 ![![283, 0, 0, 0, 0], ![0, 283, 0, 0, 0], ![0, 0, 283, 0, 0], ![271, 168, 239, 1, 0], ![32, 173, 190, 0, 1]] where
  M :=![![![1063, -688, 107, -327, 397], ![-3176, 1136, 72, -253, -654], ![4204, -1299, 699, 979, 74], ![1292, 255, -2240, 262, 1306], ![-3550, -644, 950, -2820, 335]]]
  hmulB := by decide  
  f := ![![![-4653, -2146, 207, 119, 815]], ![![-6520, -6830, -2900, -1335, 238]], ![![2308, -3375, -3807, -1803, -1454]], ![![-6345, -8950, -4744, -2204, -313]], ![![-2934, -6694, -4326, -2023, -749]]]
  g := ![![![272, -51, 10, -327, 397], ![305, 554, 653, -253, -654], ![-931, -631, -874, 979, 74], ![-394, -953, -1106, 262, 1306], ![2650, 1467, 2160, -2820, 335]]]
  hle1 := by decide   
  hle2 := by decide  


def P283P0 : CertificateIrreducibleZModOfList' 283 3 2 8 [194, 180, 274, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 271, 94], [1, 11, 189], [0, 1]]
 g := ![![[140, 54, 152], [156, 116, 265], [176, 101], [167, 4, 112], [242, 204, 256], [241, 179], [9, 1], []], ![[12, 226, 254, 228], [277, 71, 91, 228], [152, 211], [8, 120, 100, 28], [196, 213, 241, 136], [144, 129], [245, 121], [9, 63]], ![[14, 220, 245, 140], [253, 59, 99, 232], [168, 137], [172, 239, 167, 219], [72, 177, 94, 79], [190, 269], [118, 144], [197, 63]]]
 h' := ![![[8, 271, 94], [17, 170, 111], [200, 65, 185], [147, 62, 147], [30, 144, 252], [264, 101, 267], [235, 167, 184], [0, 0, 1], [0, 1]], ![[1, 11, 189], [40, 82, 221], [1, 21, 221], [165, 177, 87], [120, 53, 177], [250, 45, 262], [270, 96, 176], [16, 116, 11], [8, 271, 94]], ![[0, 1], [270, 31, 234], [26, 197, 160], [143, 44, 49], [263, 86, 137], [274, 137, 37], [175, 20, 206], [271, 167, 271], [1, 11, 189]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52, 89], []]
 b := ![[], [48, 75, 267], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI283N0 : CertifiedPrimeIdeal' SI283N0 283 where
  n := 3
  hpos := by decide
  P := [194, 180, 274, 1]
  hirr := P283P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-367171, -25514, 21447, -277098, 24991]
  a := ![-1, -5, -3, -1, 9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![261225, 149129, 217313, -277098, 24991]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI283N0 : Ideal.IsPrime I283N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI283N0 B_one_repr
lemma NI283N0 : Nat.card (O ⧸ I283N0) = 22665187 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI283N0

def I283N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4653, -2146, 207, 119, 815]] i)))

def SI283N1: IdealEqSpanCertificate' Table ![![-4653, -2146, 207, 119, 815]] 
 ![![283, 0, 0, 0, 0], ![0, 283, 0, 0, 0], ![188, 45, 1, 0, 0], ![30, 73, 0, 1, 0], ![63, 243, 0, 0, 1]] where
  M :=![![![-4653, -2146, 207, 119, 815], ![-6520, -6830, -2900, -1335, 238], ![2308, -3375, -3807, -1803, -1454], ![9076, 2781, -1576, -784, -1922], ![8014, -2890, -5852, -2792, -2961]]]
  hmulB := by decide  
  f := ![![![1063, -688, 107, -327, 397]], ![![-3176, 1136, 72, -253, -654]], ![![216, -281, 85, -254, 160]], ![![-702, 221, 22, -99, -122]], ![![-2503, 820, 89, -300, -472]]]
  g := ![![![-348, -771, 207, 119, 815], ![1992, 577, -2900, -1335, 238], ![3052, 2307, -3807, -1803, -1454], ![1590, 2113, -1576, -784, -1922], ![4871, 4183, -5852, -2792, -2961]]]
  hle1 := by decide   
  hle2 := by decide  


def P283P1 : CertificateIrreducibleZModOfList' 283 2 2 8 [166, 46, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [237, 282], [0, 1]]
 g := ![![[256, 150], [47, 203], [240], [82, 40], [54, 95], [36], [135], [1]], ![[148, 133], [48, 80], [240], [223, 243], [212, 188], [36], [135], [1]]]
 h' := ![![[237, 282], [122, 85], [281, 130], [255, 33], [92, 235], [124, 100], [52, 6], [117, 237], [0, 1]], ![[0, 1], [174, 198], [244, 153], [152, 250], [36, 48], [52, 183], [59, 277], [252, 46], [237, 282]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [237]]
 b := ![[], [37, 260]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI283N1 : CertifiedPrimeIdeal' SI283N1 283 where
  n := 2
  hpos := by decide
  P := [166, 46, 1]
  hirr := P283P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-13743, -3090, -1461, -12202, 4090]
  a := ![3, -14, -7, -4, 34]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1305, -143, -1461, -12202, 4090]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI283N1 : Ideal.IsPrime I283N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI283N1 B_one_repr
lemma NI283N1 : Nat.card (O ⧸ I283N1) = 80089 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI283N1
def MulI283N0 : IdealMulLeCertificate' Table 
  ![![1063, -688, 107, -327, 397]] ![![-4653, -2146, 207, 119, 815]]
  ![![283, 0, 0, 0, 0]] where
 M := ![![![283, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC283 : ContainsPrimesAboveP 283 ![I283N0, I283N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI283N0
    exact isPrimeI283N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 283 (by decide) (𝕀 ⊙ MulI283N0)
instance hp293 : Fact (Nat.Prime 293) := {out := by norm_num}

def I293N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![719, -408, 161, -97, 149]] i)))

def SI293N0: IdealEqSpanCertificate' Table ![![719, -408, 161, -97, 149]] 
 ![![293, 0, 0, 0, 0], ![0, 293, 0, 0, 0], ![99, 156, 1, 0, 0], ![85, 111, 0, 1, 0], ![140, 133, 0, 0, 1]] where
  M :=![![![719, -408, 161, -97, 149], ![-1192, 666, -324, 121, -194], ![1372, -879, 513, -251, 218], ![-276, 421, -248, 360, -154], ![658, -414, -28, -224, 307]]]
  hmulB := by decide  
  f := ![![![6229, 3194, -9, -33, -1015]], ![![8120, 9480, 4424, 2045, -66]], ![![6415, 6141, 2370, 1086, -371]], ![![4841, 4503, 1679, 768, -311]], ![![6622, 5840, 2030, 925, -501]]]
  g := ![![![-95, -118, 161, -97, 149], ![163, 217, -324, 121, -194], ![-200, -280, 513, -251, 218], ![52, 67, -248, 360, -154], ![-70, -41, -28, -224, 307]]]
  hle1 := by decide   
  hle2 := by decide  


def P293P0 : CertificateIrreducibleZModOfList' 293 2 2 8 [157, 201, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [92, 292], [0, 1]]
 g := ![![[61, 235], [40], [50, 39], [6], [31], [28, 169], [260], [1]], ![[292, 58], [40], [122, 254], [6], [31], [47, 124], [260], [1]]]
 h' := ![![[92, 292], [78, 198], [61, 178], [270, 268], [115, 251], [292, 275], [237, 13], [136, 92], [0, 1]], ![[0, 1], [128, 95], [29, 115], [21, 25], [60, 42], [101, 18], [261, 280], [103, 201], [92, 292]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [86]]
 b := ![[], [73, 43]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI293N0 : CertifiedPrimeIdeal' SI293N0 293 where
  n := 2
  hpos := by decide
  P := [157, 201, 1]
  hirr := P293P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2943, -2008, -1611, -3313, 4287]
  a := ![1, -7, -5, -1, 17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-553, 160, -1611, -3313, 4287]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI293N0 : Ideal.IsPrime I293N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI293N0 B_one_repr
lemma NI293N0 : Nat.card (O ⧸ I293N0) = 85849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI293N0

def I293N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2849, 427, 2150, -249, -1644]] i)))

def SI293N1: IdealEqSpanCertificate' Table ![![-2849, 427, 2150, -249, -1644]] 
 ![![293, 0, 0, 0, 0], ![19, 1, 0, 0, 0], ![103, 0, 1, 0, 0], ![184, 0, 0, 1, 0], ![224, 0, 0, 0, 1]] where
  M :=![![![-2849, 427, 2150, -249, -1644], ![13152, 226, -1936, 7837, -498], ![-4584, -2229, -7141, -9275, 8086], ![-38920, 2185, 16100, -14508, -9026], ![25212, 3280, 6640, 23688, -11433]]]
  hmulB := by decide  
  f := ![![![-188205, -43451, 44726, 21883, 43312]], ![![-13387, -3605, 2750, 1354, 2958]], ![![-66167, -15876, 15225, 7458, 15086]], ![![-117040, -27211, 27656, 13534, 26890]], ![![-143260, -33964, 33304, 16308, 32759]]]
  g := ![![![620, 427, 2150, -249, -1644], ![-3830, 226, -1936, 7837, -498], ![2282, -2229, -7141, -9275, 8086], ![10077, 2185, 16100, -14508, -9026], ![-8596, 3280, 6640, 23688, -11433]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI293N1 : Nat.card (O ⧸ I293N1) = 293 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI293N1)

lemma isPrimeI293N1 : Ideal.IsPrime I293N1 := prime_ideal_of_norm_prime hp293.out _ NI293N1

def I293N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4837839, -2927379, 1290413, -841800, 1009021]] i)))

def SI293N2: IdealEqSpanCertificate' Table ![![4837839, -2927379, 1290413, -841800, 1009021]] 
 ![![293, 0, 0, 0, 0], ![98, 1, 0, 0, 0], ![130, 0, 1, 0, 0], ![27, 0, 0, 1, 0], ![237, 0, 0, 0, 1]] where
  M :=![![![4837839, -2927379, 1290413, -841800, 1009021], ![-8072168, 4884473, -2153116, 1404584, -1683600], ![10770484, -6517226, 2872847, -1874100, 2246384], ![-4949452, 2994916, -1320184, 861221, -1032300], ![4352790, -2633876, 1161034, -757400, 907855]]]
  hmulB := by decide  
  f := ![![![2101, -655, -1969, 20, 1345]], ![![666, -221, -654, -16, 450]], ![![950, -284, -855, 36, 574]], ![![303, -65, -227, 41, 151]], ![![1627, -537, -1609, -52, 1118]]]
  g := ![![![-315502, -2927379, 1290413, -841800, 1009021], ![526430, 4884473, -2153116, 1404584, -1683600], ![-702402, -6517226, 2872847, -1874100, 2246384], ![322781, 2994916, -1320184, 861221, -1032300], ![-283869, -2633876, 1161034, -757400, 907855]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI293N2 : Nat.card (O ⧸ I293N2) = 293 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI293N2)

lemma isPrimeI293N2 : Ideal.IsPrime I293N2 := prime_ideal_of_norm_prime hp293.out _ NI293N2

def I293N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-103, -697, -695, -288, -219]] i)))

def SI293N3: IdealEqSpanCertificate' Table ![![-103, -697, -695, -288, -219]] 
 ![![293, 0, 0, 0, 0], ![158, 1, 0, 0, 0], ![38, 0, 1, 0, 0], ![142, 0, 0, 1, 0], ![183, 0, 0, 0, 1]] where
  M :=![![![-103, -697, -695, -288, -219], ![1752, -919, -1256, -664, -576], ![1428, 912, -203, -16, -376], ![628, 1544, 1180, 513, 272], ![2406, 1928, 434, 228, -303]]]
  hmulB := by decide  
  f := ![![![-138621, 731, 31711, -73132, -6199]], ![![-74582, 531, 17562, -38928, -3842]], ![![-16066, -98, 3011, -9032, -46]], ![![-70298, 142, 15250, -37783, -2302]], ![![-88865, 911, 21937, -45536, -5602]]]
  g := ![![![742, -697, -695, -288, -219], ![1346, -919, -1256, -664, -576], ![-218, 912, -203, -16, -376], ![-1402, 1544, 1180, 513, 272], ![-1009, 1928, 434, 228, -303]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI293N3 : Nat.card (O ⧸ I293N3) = 293 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI293N3)

lemma isPrimeI293N3 : Ideal.IsPrime I293N3 := prime_ideal_of_norm_prime hp293.out _ NI293N3
def MulI293N0 : IdealMulLeCertificate' Table 
  ![![719, -408, 161, -97, 149]] ![![-2849, 427, 2150, -249, -1644]]
  ![![-620643, 132711, 613697, 66986, -505001]] where
 M := ![![![-620643, 132711, 613697, 66986, -505001]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI293N1 : IdealMulLeCertificate' Table 
  ![![-620643, 132711, 613697, 66986, -505001]] ![![4837839, -2927379, 1290413, -841800, 1009021]]
  ![![6270026961, -3794006470, 1672435866, -1091015770, 1307730890]] where
 M := ![![![6270026961, -3794006470, 1672435866, -1091015770, 1307730890]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI293N2 : IdealMulLeCertificate' Table 
  ![![6270026961, -3794006470, 1672435866, -1091015770, 1307730890]] ![![-103, -697, -695, -288, -219]]
  ![![293, 0, 0, 0, 0]] where
 M := ![![![-2443431077995, 1478521470945, -651744494713, 425165110366, -509622812465]]]
 hmul := by decide  
 g := ![![![![-8339355215, 5046148365, -2224383941, 1451075462, -1739327005]]]]
 hle2 := by decide  


def PBC293 : ContainsPrimesAboveP 293 ![I293N0, I293N1, I293N2, I293N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI293N0
    exact isPrimeI293N1
    exact isPrimeI293N2
    exact isPrimeI293N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 293 (by decide) (𝕀 ⊙ MulI293N0 ⊙ MulI293N1 ⊙ MulI293N2)
instance hp307 : Fact (Nat.Prime 307) := {out := by norm_num}

def I307N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![20961681, -12683925, 5591179, -3647402, 4371947]] i)))

def SI307N0: IdealEqSpanCertificate' Table ![![20961681, -12683925, 5591179, -3647402, 4371947]] 
 ![![307, 0, 0, 0, 0], ![0, 307, 0, 0, 0], ![0, 0, 307, 0, 0], ![126, 193, 143, 1, 0], ![158, 204, 230, 0, 1]] where
  M :=![![![20961681, -12683925, 5591179, -3647402, 4371947], ![-34975576, 21163739, -9329152, 6085866, -7294804], ![46667004, -28238230, 12447645, -8120214, 9733268], ![-21445284, 12976554, -5720172, 3731551, -4472812], ![18860034, -11412216, 5030598, -3281708, 3933609]]]
  hmulB := by decide  
  f := ![![![-115, -67, -17, 10, 57]], ![![-456, -219, -40, -158, 20]], ![![148, -90, -21, 98, -168]], ![![-262, -207, -43, -49, -42]], ![![-252, -248, -52, -28, -83]]]
  g := ![![![-684799, -653461, -1558235, -3647402, 4371947], ![1142620, 1090331, 2599990, 6085866, -7294804], ![-1524568, -1454800, -3469099, -8120214, 9733268], ![700598, 668537, 1594185, 3731551, -4472812], ![-616140, -587944, -1402004, -3281708, 3933609]]]
  hle1 := by decide   
  hle2 := by decide  


def P307P0 : CertificateIrreducibleZModOfList' 307 3 2 8 [110, 46, 117, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [126, 237, 306], [64, 69, 1], [0, 1]]
 g := ![![[77, 159, 240], [283, 18, 155], [185, 160], [114, 9], [130, 160, 63], [198, 285, 112], [190, 1], []], ![[305, 226, 219, 243], [257, 45, 270, 8], [211, 58], [215, 233], [117, 205, 176, 21], [137, 84, 43, 59], [42, 156], [23, 1]], ![[304, 42, 152, 273], [133, 104, 186, 7], [147, 16], [303, 10], [232, 83, 140, 284], [120, 223, 295, 278], [195, 295], [21, 1]]]
 h' := ![![[126, 237, 306], [184, 31, 94], [39, 281, 259], [110, 46, 62], [129, 41, 3], [17, 28, 129], [283, 53, 135], [0, 0, 1], [0, 1]], ![[64, 69, 1], [221, 40, 8], [241, 182, 91], [160, 47, 241], [204, 264, 166], [146, 178, 277], [134, 91, 52], [145, 226, 69], [126, 237, 306]], ![[0, 1], [281, 236, 205], [142, 151, 264], [196, 214, 4], [129, 2, 138], [111, 101, 208], [106, 163, 120], [251, 81, 237], [64, 69, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [127, 279], []]
 b := ![[], [67, 67, 279], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI307N0 : CertifiedPrimeIdeal' SI307N0 307 where
  n := 3
  hpos := by decide
  P := [110, 46, 117, 1]
  hirr := P307P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-19450, -2310, -2964, -20120, 2208]
  a := ![4, 2, 1, 1, -4]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![7058, 11174, 7708, -20120, 2208]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI307N0 : Ideal.IsPrime I307N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI307N0 B_one_repr
lemma NI307N0 : Nat.card (O ⧸ I307N0) = 28934443 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI307N0

def I307N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![115, 67, 17, -10, -57]] i)))

def SI307N1: IdealEqSpanCertificate' Table ![![115, 67, 17, -10, -57]] 
 ![![307, 0, 0, 0, 0], ![0, 307, 0, 0, 0], ![156, 165, 1, 0, 0], ![48, 259, 0, 1, 0], ![300, 78, 0, 0, 1]] where
  M :=![![![115, 67, 17, -10, -57], ![456, 219, 40, 158, -20], ![-148, 90, 21, -98, 168], ![-900, -30, 336, -177, -88], ![210, 174, 288, 484, -73]]]
  hmulB := by decide  
  f := ![![![-20961681, 12683925, -5591179, 3647402, -4371947]], ![![34975576, -21163739, 9329152, -6085866, 7294804]], ![![7994400, -4837415, 2132373, -1391052, 1667380]], ![![26299540, -15913865, 7014964, -4576207, 5485256]], ![![-11658858, 7054782, -3109806, 2028680, -2431671]]]
  g := ![![![49, 14, 17, -10, -57], ![-24, -149, 40, 158, -20], ![-160, 29, 21, -98, 168], ![-60, -9, 336, -177, -88], ![-150, -544, 288, 484, -73]]]
  hle1 := by decide   
  hle2 := by decide  


def P307P1 : CertificateIrreducibleZModOfList' 307 2 2 8 [301, 205, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [102, 306], [0, 1]]
 g := ![![[17, 112], [50, 302], [101], [99], [163, 274], [156, 122], [273], [1]], ![[82, 195], [154, 5], [101], [99], [174, 33], [13, 185], [273], [1]]]
 h' := ![![[102, 306], [300, 135], [99, 223], [159, 228], [57, 75], [15, 46], [139, 212], [6, 102], [0, 1]], ![[0, 1], [255, 172], [127, 84], [83, 79], [32, 232], [102, 261], [273, 95], [279, 205], [102, 306]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [246]]
 b := ![[], [174, 123]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI307N1 : CertifiedPrimeIdeal' SI307N1 307 where
  n := 2
  hpos := by decide
  P := [301, 205, 1]
  hirr := P307P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-193095, -38754, -43434, -192174, 22478]
  a := ![7, 47, 23, 0, -140]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![29523, 179634, -43434, -192174, 22478]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI307N1 : Ideal.IsPrime I307N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI307N1 B_one_repr
lemma NI307N1 : Nat.card (O ⧸ I307N1) = 94249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI307N1
def MulI307N0 : IdealMulLeCertificate' Table 
  ![![20961681, -12683925, 5591179, -3647402, 4371947]] ![![115, 67, 17, -10, -57]]
  ![![307, 0, 0, 0, 0]] where
 M := ![![![-307, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC307 : ContainsPrimesAboveP 307 ![I307N0, I307N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI307N0
    exact isPrimeI307N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 307 (by decide) (𝕀 ⊙ MulI307N0)


lemma PB324I6_primes (p : ℕ) :
  p ∈ Set.range ![257, 263, 269, 271, 277, 281, 283, 293, 307] ↔ Nat.Prime p ∧ 251 < p ∧ p ≤ 307 := by
  rw [← List.mem_ofFn']
  convert primes_range 251 307 (by omega)

def PB324I6 : PrimesBelowBoundCertificateInterval O 251 307 324 where
  m := 9
  g := ![2, 3, 2, 2, 1, 2, 2, 4, 2]
  P := ![257, 263, 269, 271, 277, 281, 283, 293, 307]
  hP := PB324I6_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I257N0, I257N1]
    · exact ![I263N0, I263N1, I263N2]
    · exact ![I269N0, I269N1]
    · exact ![I271N0, I271N1]
    · exact ![I277N0]
    · exact ![I281N0, I281N1]
    · exact ![I283N0, I283N1]
    · exact ![I293N0, I293N1, I293N2, I293N3]
    · exact ![I307N0, I307N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC257
    · exact PBC263
    · exact PBC269
    · exact PBC271
    · exact PBC277
    · exact PBC281
    · exact PBC283
    · exact PBC293
    · exact PBC307
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![4362470401, 257]
    · exact ![18191447, 263, 263]
    · exact ![5236114321, 269]
    · exact ![5393580481, 271]
    · exact ![1630793025157]
    · exact ![22188041, 78961]
    · exact ![22665187, 80089]
    · exact ![85849, 293, 293, 293]
    · exact ![28934443, 94249]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI257N0
      exact NI257N1
    · dsimp ; intro j
      fin_cases j
      exact NI263N0
      exact NI263N1
      exact NI263N2
    · dsimp ; intro j
      fin_cases j
      exact NI269N0
      exact NI269N1
    · dsimp ; intro j
      fin_cases j
      exact NI271N0
      exact NI271N1
    · dsimp ; intro j
      fin_cases j
      exact NI277N0
    · dsimp ; intro j
      fin_cases j
      exact NI281N0
      exact NI281N1
    · dsimp ; intro j
      fin_cases j
      exact NI283N0
      exact NI283N1
    · dsimp ; intro j
      fin_cases j
      exact NI293N0
      exact NI293N1
      exact NI293N2
      exact NI293N3
    · dsimp ; intro j
      fin_cases j
      exact NI307N0
      exact NI307N1
  β := ![I257N1, I263N1, I263N2, I269N1, I271N1, I293N1, I293N2, I293N3]
  Il := ![[I257N1], [I263N1, I263N2], [I269N1], [I271N1], [], [], [], [I293N1, I293N2, I293N3], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
