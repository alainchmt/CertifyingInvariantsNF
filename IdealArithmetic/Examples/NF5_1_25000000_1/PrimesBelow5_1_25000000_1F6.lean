
import IdealArithmetic.Examples.NF5_1_25000000_1.RI5_1_25000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp257 : Fact (Nat.Prime 257) := {out := by norm_num}

def I257N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![257, 0, 0, 0, 0]] i)))

def SI257N0: IdealEqSpanCertificate' Table ![![257, 0, 0, 0, 0]] 
 ![![257, 0, 0, 0, 0], ![0, 257, 0, 0, 0], ![0, 0, 257, 0, 0], ![0, 0, 0, 257, 0], ![0, 0, 0, 0, 257]] where
  M :=![![![257, 0, 0, 0, 0], ![0, 257, 0, 0, 0], ![0, 0, 257, 0, 0], ![0, 0, 0, 257, 0], ![0, 0, 0, 0, 257]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P257P0 : CertificateIrreducibleZModOfList' 257 5 2 8 [89, 30, 90, 68, 82, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [231, 95, 166, 163, 193], [238, 205, 195, 229, 249], [236, 110, 193, 54, 13], [241, 103, 217, 68, 59], [0, 1]]
 g := ![![[162, 123, 132, 206, 244], [3, 64, 29, 1], [80, 6, 230, 197], [225, 17, 144, 159], [73, 149, 40, 50], [165, 231, 175, 1], [], []], ![[101, 189, 219, 159, 240, 68, 252, 199], [124, 208, 77, 113], [22, 227, 91, 241], [236, 12, 140, 117], [204, 18, 75, 32], [107, 241, 209, 21], [18, 141, 249, 61], [253, 82, 237, 241]], ![[42, 115, 7, 5, 71, 194, 164, 255], [105, 89, 19, 165], [143, 103, 88, 135], [198, 193, 104, 88], [79, 16, 25, 242], [123, 6, 181, 30], [248, 6, 74, 68], [219, 127, 83, 64]], ![[247, 98, 165, 210, 112, 178, 91, 211], [196, 168, 200, 95], [247, 158, 46, 113], [1, 7, 146, 193], [79, 97, 195, 223], [17, 67, 168, 61], [249, 18, 234, 240], [58, 207, 139, 169]], ![[137, 109, 134, 41, 101, 114, 197, 44], [13, 40, 142, 159], [75, 155, 69, 72], [26, 226, 199, 222], [85, 168, 98, 248], [173, 67, 159, 67], [6, 218, 158, 225], [224, 71, 142, 140]]]
 h' := ![![[231, 95, 166, 163, 193], [15, 218, 12, 209, 191], [252, 222, 4, 184, 1], [144, 193, 70, 190, 35], [196, 95, 91, 72, 38], [221, 191, 167, 173, 214], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[238, 205, 195, 229, 249], [13, 34, 84, 142, 252], [68, 39, 198, 25, 192], [235, 74, 34, 129, 64], [57, 9, 242, 61, 84], [123, 185, 227, 34, 240], [213, 220, 51, 52, 110], [4, 218, 73, 247, 33], [231, 95, 166, 163, 193]], ![[236, 110, 193, 54, 13], [30, 4, 174, 33, 128], [61, 194, 179, 190, 200], [127, 247, 10, 133, 69], [253, 35, 252, 17, 49], [208, 16, 170, 39, 146], [238, 186, 71, 91, 95], [145, 37, 110, 246, 117], [238, 205, 195, 229, 249]], ![[241, 103, 217, 68, 59], [31, 93, 181, 216, 6], [241, 93, 124, 72, 159], [76, 174, 6, 217, 192], [200, 252, 242, 219, 128], [99, 149, 126, 189, 123], [228, 196, 235, 164, 33], [162, 146, 239, 206, 92], [236, 110, 193, 54, 13]], ![[0, 1], [252, 165, 63, 171, 194], [102, 223, 9, 43, 219], [98, 83, 137, 102, 154], [149, 123, 201, 145, 215], [2, 230, 81, 79, 48], [39, 169, 157, 207, 18], [109, 113, 91, 72, 15], [241, 103, 217, 68, 59]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [219, 194, 54, 87], [], [], []]
 b := ![[], [117, 35, 182, 254, 166], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N0 : CertifiedPrimeIdeal' SI257N0 257 where
  n := 5
  hpos := by decide
  P := [89, 30, 90, 68, 82, 1]
  hirr := P257P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-24045164021243, -2831037155946, -21819899470490, -39016265280544, 36881180507066]
  a := ![26, 17, 31, 30, -91]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-93560949499, -11015708778, -84902332570, -151814261792, 143506538938]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI257N0 : Ideal.IsPrime I257N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI257N0 B_one_repr
lemma NI257N0 : Nat.card (O ⧸ I257N0) = 1121154893057 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI257N0

def PBC257 : ContainsPrimesAboveP 257 ![I257N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI257N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![257, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 257 (by decide) 𝕀

instance hp263 : Fact (Nat.Prime 263) := {out := by norm_num}

def I263N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4773, 1550, -662, 374, -2658]] i)))

def SI263N0: IdealEqSpanCertificate' Table ![![4773, 1550, -662, 374, -2658]] 
 ![![263, 0, 0, 0, 0], ![0, 263, 0, 0, 0], ![38, 158, 1, 0, 0], ![58, 199, 0, 1, 0], ![260, 107, 0, 0, 1]] where
  M :=![![![4773, 1550, -662, 374, -2658], ![9884, 3363, -1270, 798, -5356], ![19828, 7018, -2369, 1642, -10482], ![-2724, -806, 430, -201, 1592], ![12720, 4568, -1476, 1064, -6661]]]
  hmulB := by decide  
  f := ![![![2035, -2366, -90, -678, 1070]], ![![-2924, 3301, 166, 890, -1536]], ![![-1446, 1624, 87, 434, -762]], ![![-1774, 1987, 104, 525, -928]], ![![824, -999, -22, -310, 435]]]
  g := ![![![2659, 1202, -662, 374, -2658], ![5340, 2351, -1270, 798, -5356], ![10418, 4472, -2369, 1642, -10482], ![-1602, -757, 430, -201, 1592], ![6612, 2809, -1476, 1064, -6661]]]
  hle1 := by decide   
  hle2 := by decide  


def P263P0 : CertificateIrreducibleZModOfList' 263 2 2 8 [81, 142, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [121, 262], [0, 1]]
 g := ![![[5, 13], [204, 181], [12, 205], [86], [179], [43], [176], [1]], ![[0, 250], [13, 82], [95, 58], [86], [179], [43], [176], [1]]]
 h' := ![![[121, 262], [45, 117], [80, 60], [144, 176], [260, 127], [89, 210], [195, 116], [182, 121], [0, 1]], ![[0, 1], [0, 146], [239, 203], [137, 87], [110, 136], [251, 53], [29, 147], [95, 142], [121, 262]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64]]
 b := ![[], [168, 32]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI263N0 : CertifiedPrimeIdeal' SI263N0 263 where
  n := 2
  hpos := by decide
  P := [81, 142, 1]
  hirr := P263P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2279352, -811726, -2882713, -3878318, 5298802]
  a := ![239, 117, 236, 172, -835]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3975218, 2507492, -2882713, -3878318, 5298802]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI263N0 : Ideal.IsPrime I263N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI263N0 B_one_repr
lemma NI263N0 : Nat.card (O ⧸ I263N0) = 69169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI263N0

def I263N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, -125, 1, -32, 72]] i)))

def SI263N1: IdealEqSpanCertificate' Table ![![-7, -125, 1, -32, 72]] 
 ![![263, 0, 0, 0, 0], ![0, 263, 0, 0, 0], ![124, 109, 1, 0, 0], ![241, 31, 0, 1, 0], ![182, 237, 0, 0, 1]] where
  M :=![![![-7, -125, 1, -32, 72], ![-224, 58, 5, 20, -8], ![-8, -259, -12, -64, 116], ![-24, 142, -2, 37, -81], ![-52, -80, -8, -18, 29]]]
  hmulB := by decide  
  f := ![![![7, 9, 45, 44, -72]], ![![200, -36, -77, 104, 92]], ![![84, -11, -13, 60, 8]], ![![29, 5, 36, 55, -61]], ![![186, -26, -37, 126, 31]]]
  g := ![![![-21, -62, 1, -32, 72], ![-16, 3, 5, 20, -8], ![-16, -93, -12, -64, 116], ![23, 70, -2, 37, -81], ![0, -21, -8, -18, 29]]]
  hle1 := by decide   
  hle2 := by decide  


def P263P1 : CertificateIrreducibleZModOfList' 263 2 2 8 [14, 192, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [71, 262], [0, 1]]
 g := ![![[164, 6], [82, 149], [196, 68], [244], [75], [218], [44], [1]], ![[64, 257], [141, 114], [27, 195], [244], [75], [218], [44], [1]]]
 h' := ![![[71, 262], [167, 163], [149, 181], [34, 133], [174, 36], [31, 148], [106, 84], [249, 71], [0, 1]], ![[0, 1], [168, 100], [113, 82], [9, 130], [100, 227], [19, 115], [21, 179], [30, 192], [71, 262]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [88]]
 b := ![[], [16, 44]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI263N1 : CertifiedPrimeIdeal' SI263N1 263 where
  n := 2
  hpos := by decide
  P := [14, 192, 1]
  hirr := P263P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-13929, -1706, -12116, -22716, 17292]
  a := ![19, 11, 21, 18, -66]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![14509, -7890, -12116, -22716, 17292]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI263N1 : Ideal.IsPrime I263N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI263N1 B_one_repr
lemma NI263N1 : Nat.card (O ⧸ I263N1) = 69169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI263N1

def I263N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1325, 1485, 47, 408, -639]] i)))

def SI263N2: IdealEqSpanCertificate' Table ![![-1325, 1485, 47, 408, -639]] 
 ![![263, 0, 0, 0, 0], ![259, 1, 0, 0, 0], ![247, 0, 1, 0, 0], ![256, 0, 0, 1, 0], ![18, 0, 0, 0, 1]] where
  M :=![![![-1325, 1485, 47, 408, -639], ![1740, -2094, -53, -574, 939], ![-2608, 2835, 96, 780, -1201], ![1680, -1912, -58, -525, 830], ![-496, 462, 22, 128, -177]]]
  hmulB := by decide  
  f := ![![![633, -151, -459, 126, 619]], ![![613, -149, -458, 110, 620]], ![![581, -130, -387, 144, 514]], ![![680, -158, -468, 159, 628]], ![![54, -16, -52, 0, 73]]]
  g := ![![![-1865, 1485, 47, 408, -639], ![2613, -2094, -53, -574, 939], ![-3569, 2835, 96, 780, -1201], ![2398, -1912, -58, -525, 830], ![-590, 462, 22, 128, -177]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI263N2 : Nat.card (O ⧸ I263N2) = 263 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI263N2)

lemma isPrimeI263N2 : Ideal.IsPrime I263N2 := prime_ideal_of_norm_prime hp263.out _ NI263N2
def MulI263N0 : IdealMulLeCertificate' Table 
  ![![4773, 1550, -662, 374, -2658]] ![![-7, -125, 1, -32, 72]]
  ![![-246075, -69519, 40983, -17686, 147088]] where
 M := ![![![-246075, -69519, 40983, -17686, 147088]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI263N1 : IdealMulLeCertificate' Table 
  ![![-246075, -69519, 40983, -17686, 147088]] ![![-1325, 1485, 47, 408, -639]]
  ![![263, 0, 0, 0, 0]] where
 M := ![![![-4465477, -1891496, 315074, -415540, 2029045]]]
 hmul := by decide  
 g := ![![![![-16979, -7192, 1198, -1580, 7715]]]]
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

def I269N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-925, 1084, 26, 298, -488]] i)))

def SI269N0: IdealEqSpanCertificate' Table ![![-925, 1084, 26, 298, -488]] 
 ![![269, 0, 0, 0, 0], ![0, 269, 0, 0, 0], ![176, 252, 1, 0, 0], ![122, 115, 0, 1, 0], ![255, 23, 0, 0, 1]] where
  M :=![![![-925, 1084, 26, 298, -488], ![1356, -1495, -56, -410, 622], ![-1668, 2120, 33, 582, -1004], ![1208, -1386, -38, -381, 612], ![-208, 380, -8, 104, -217]]]
  hmulB := by decide  
  f := ![![![71, 0, 54, 114, -88]], ![![124, -103, -348, -178, 534]], ![![156, -96, -291, -98, 444]], ![![90, -43, -118, -15, 178]], ![![81, -9, 22, 96, -39]]]
  g := ![![![307, -106, 26, 298, -488], ![-362, 169, -56, -410, 622], ![660, -186, 33, 582, -1004], ![-378, 141, -38, -381, 612], ![163, -17, -8, 104, -217]]]
  hle1 := by decide   
  hle2 := by decide  


def P269P0 : CertificateIrreducibleZModOfList' 269 2 2 8 [62, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [253, 268], [0, 1]]
 g := ![![[61, 256], [99], [236, 55], [134, 154], [73], [255], [256], [1]], ![[0, 13], [99], [163, 214], [91, 115], [73], [255], [256], [1]]]
 h' := ![![[253, 268], [256, 16], [163, 231], [31, 18], [120, 31], [72, 197], [77, 40], [207, 253], [0, 1]], ![[0, 1], [0, 253], [233, 38], [12, 251], [162, 238], [148, 72], [244, 229], [194, 16], [253, 268]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [134]]
 b := ![[], [267, 67]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI269N0 : CertifiedPrimeIdeal' SI269N0 269 where
  n := 2
  hpos := by decide
  P := [62, 16, 1]
  hirr := P269P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-577935, -122329, -510458, -839787, 958746]
  a := ![-107, -61, -118, -103, 375]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-196147, 754786, -510458, -839787, 958746]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI269N0 : Ideal.IsPrime I269N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI269N0 B_one_repr
lemma NI269N0 : Nat.card (O ⧸ I269N0) = 72361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI269N0

def I269N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, 0, 0, -2, 6]] i)))

def SI269N1: IdealEqSpanCertificate' Table ![![-5, 0, 0, -2, 6]] 
 ![![269, 0, 0, 0, 0], ![0, 269, 0, 0, 0], ![129, 66, 1, 0, 0], ![228, 121, 0, 1, 0], ![120, 130, 0, 0, 1]] where
  M :=![![![-5, 0, 0, -2, 6], ![-20, -1, 8, -2, 4], ![-12, -8, 23, 34, -2], ![-4, -10, -38, -35, 58], ![-40, -8, -4, -20, 33]]]
  hmulB := by decide  
  f := ![![![-145, 228, 4, 62, -110]], ![![316, -265, -12, -74, 104]], ![![7, 46, -1, 12, -28]], ![![20, 73, -2, 19, -46]], ![![88, -26, -4, -8, 1]]]
  g := ![![![-1, -2, 0, -2, 6], ![-4, -3, 8, -2, 4], ![-39, -20, 23, 34, -2], ![22, -3, -38, -35, 58], ![4, -6, -4, -20, 33]]]
  hle1 := by decide   
  hle2 := by decide  


def P269P1 : CertificateIrreducibleZModOfList' 269 2 2 8 [265, 90, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [179, 268], [0, 1]]
 g := ![![[112, 67], [25], [86, 61], [158, 228], [152], [11], [30], [1]], ![[0, 202], [25], [245, 208], [82, 41], [152], [11], [30], [1]]]
 h' := ![![[179, 268], [76, 228], [75, 264], [94, 64], [242, 175], [248, 48], [136, 77], [4, 179], [0, 1]], ![[0, 1], [0, 41], [256, 5], [252, 205], [94, 94], [232, 221], [200, 192], [34, 90], [179, 268]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [115, 152]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI269N1 : CertifiedPrimeIdeal' SI269N1 269 where
  n := 2
  hpos := by decide
  P := [265, 90, 1]
  hirr := P269P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-91140, 5070, -14210, -88690, 32320]
  a := ![35, 28, 52, 60, -123]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![67230, 27780, -14210, -88690, 32320]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI269N1 : Ideal.IsPrime I269N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI269N1 B_one_repr
lemma NI269N1 : Nat.card (O ⧸ I269N1) = 72361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI269N1

def I269N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 0, 2, 0, -2]] i)))

def SI269N2: IdealEqSpanCertificate' Table ![![-3, 0, 2, 0, -2]] 
 ![![269, 0, 0, 0, 0], ![220, 1, 0, 0, 0], ![20, 0, 1, 0, 0], ![180, 0, 0, 1, 0], ![156, 0, 0, 0, 1]] where
  M :=![![![-3, 0, 2, 0, -2], ![8, -1, 4, 12, -6], ![0, -12, -41, -32, 66], ![-52, 12, 28, -21, -38], ![-8, 4, 20, 12, -29]]]
  hmulB := by decide  
  f := ![![![961, -368, -102, -104, -86]], ![![788, -297, -84, -84, -74]], ![![84, -28, -9, -8, -10]], ![![640, -244, -68, -69, -58]], ![![564, -212, -60, -60, -53]]]
  g := ![![![1, 0, 2, 0, -2], ![-4, -1, 4, 12, -6], ![-4, -12, -41, -32, 66], ![24, 12, 28, -21, -38], ![4, 4, 20, 12, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI269N2 : Nat.card (O ⧸ I269N2) = 269 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI269N2)

lemma isPrimeI269N2 : Ideal.IsPrime I269N2 := prime_ideal_of_norm_prime hp269.out _ NI269N2
def MulI269N0 : IdealMulLeCertificate' Table 
  ![![-925, 1084, 26, 298, -488]] ![![-5, 0, 0, -2, 6]]
  ![![961, -368, -102, -104, -86]] where
 M := ![![![961, -368, -102, -104, -86]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI269N1 : IdealMulLeCertificate' Table 
  ![![961, -368, -102, -104, -86]] ![![-3, 0, 2, 0, -2]]
  ![![269, 0, 0, 0, 0]] where
 M := ![![![269, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC269 : ContainsPrimesAboveP 269 ![I269N0, I269N1, I269N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI269N0
    exact isPrimeI269N1
    exact isPrimeI269N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 269 (by decide) (𝕀 ⊙ MulI269N0 ⊙ MulI269N1)
instance hp271 : Fact (Nat.Prime 271) := {out := by norm_num}

def I271N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 3, 1, 6, -8]] i)))

def SI271N0: IdealEqSpanCertificate' Table ![![13, 3, 1, 6, -8]] 
 ![![271, 0, 0, 0, 0], ![0, 271, 0, 0, 0], ![168, 238, 1, 0, 0], ![218, 193, 0, 1, 0], ![149, 208, 0, 0, 1]] where
  M :=![![![13, 3, 1, 6, -8], ![20, 2, -19, -10, 18], ![-52, 21, 4, -62, -16], ![68, 8, 72, 123, -117], ![60, 4, 0, 38, -17]]]
  hmulB := by decide  
  f := ![![![83, -259, 9, -70, 160]], ![![-500, 232, 39, 66, -10]], ![![-388, 41, 40, 14, 92]], ![![-290, -42, 35, -9, 121]], ![![-339, 35, 35, 12, 81]]]
  g := ![![![-1, 1, 1, 6, -8], ![10, 10, -19, -10, 18], ![56, 53, 4, -62, -16], ![-79, -61, 72, 123, -117], ![-21, -14, 0, 38, -17]]]
  hle1 := by decide   
  hle2 := by decide  


def P271P0 : CertificateIrreducibleZModOfList' 271 2 2 8 [264, 210, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [61, 270], [0, 1]]
 g := ![![[241, 140], [117, 228], [190, 18], [186, 81], [163], [85], [198], [1]], ![[109, 131], [204, 43], [204, 253], [249, 190], [163], [85], [198], [1]]]
 h' := ![![[61, 270], [6, 144], [246, 162], [218, 254], [219, 262], [220, 71], [80, 195], [7, 61], [0, 1]], ![[0, 1], [118, 127], [101, 109], [265, 17], [212, 9], [215, 200], [51, 76], [205, 210], [61, 270]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [247]]
 b := ![[], [95, 259]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI271N0 : CertifiedPrimeIdeal' SI271N0 271 where
  n := 2
  hpos := by decide
  P := [264, 210, 1]
  hirr := P271P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-87736, 10792, 29864, -51520, -34188]
  a := ![-28, -30, -56, -78, 98]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![41404, 36744, 29864, -51520, -34188]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI271N0 : Ideal.IsPrime I271N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI271N0 B_one_repr
lemma NI271N0 : Nat.card (O ⧸ I271N0) = 73441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI271N0

def I271N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6503, 7488, 228, 2054, -3253]] i)))

def SI271N1: IdealEqSpanCertificate' Table ![![-6503, 7488, 228, 2054, -3253]] 
 ![![271, 0, 0, 0, 0], ![0, 271, 0, 0, 0], ![80, 88, 1, 0, 0], ![97, 5, 0, 1, 0], ![135, 82, 0, 0, 1]] where
  M :=![![![-6503, 7488, 228, 2054, -3253], ![8904, -10383, -272, -2852, 4619], ![-12772, 14336, 481, 3934, -6107], ![8300, -9612, -282, -2637, 4203], ![-2332, 2398, 114, 658, -933]]]
  hmulB := by decide  
  f := ![![![171, -150, -582, -352, 885]], ![![-2836, 293, 94, -2338, 191]], ![![-856, 58, -105, -820, 265]], ![![41, -61, -248, -177, 381]], ![![-777, 10, -280, -902, 528]]]
  g := ![![![794, 900, 228, 2054, -3253], ![-1167, -1295, -272, -2852, 4619], ![1445, 1672, 481, 3934, -6107], ![-1036, -1167, -282, -2637, 4203], ![187, 242, 114, 658, -933]]]
  hle1 := by decide   
  hle2 := by decide  


def P271P1 : CertificateIrreducibleZModOfList' 271 2 2 8 [179, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [258, 270], [0, 1]]
 g := ![![[209, 162], [90, 37], [67, 98], [188, 57], [20], [53], [169], [1]], ![[0, 109], [151, 234], [148, 173], [260, 214], [20], [53], [169], [1]]]
 h' := ![![[258, 270], [150, 220], [202, 151], [223, 130], [103, 190], [65, 66], [164, 18], [92, 258], [0, 1]], ![[0, 1], [0, 51], [136, 120], [159, 141], [72, 81], [20, 205], [201, 253], [261, 13], [258, 270]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55]]
 b := ![[], [111, 163]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI271N1 : CertifiedPrimeIdeal' SI271N1 271 where
  n := 2
  hpos := by decide
  P := [179, 13, 1]
  hirr := P271P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-34145, 10930, 37232, 3960, -50997]
  a := ![17, 23, 43, 61, -53]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![12870, 3308, 37232, 3960, -50997]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI271N1 : Ideal.IsPrime I271N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI271N1 B_one_repr
lemma NI271N1 : Nat.card (O ⧸ I271N1) = 73441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI271N1

def I271N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, -1, -5, -8, 9]] i)))

def SI271N2: IdealEqSpanCertificate' Table ![![-5, -1, -5, -8, 9]] 
 ![![271, 0, 0, 0, 0], ![216, 1, 0, 0, 0], ![227, 0, 1, 0, 0], ![176, 0, 0, 1, 0], ![35, 0, 0, 0, 1]] where
  M :=![![![-5, -1, -5, -8, 9], ![-20, 6, 21, 2, -29], ![112, -3, 40, 132, -73], ![-44, -28, -138, -155, 220], ![-56, -2, -26, -68, 49]]]
  hmulB := by decide  
  f := ![![![-2143, 3675, 25, 994, -1857]], ![![-1688, 2914, 19, 788, -1475]], ![![-1807, 3106, 21, 840, -1570]], ![![-1380, 2370, 16, 641, -1198]], ![![-275, 481, 3, 130, -244]]]
  g := ![![![9, -1, -5, -8, 9], ![-20, 6, 21, 2, -29], ![-107, -3, 40, 132, -73], ![210, -28, -138, -155, 220], ![61, -2, -26, -68, 49]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI271N2 : Nat.card (O ⧸ I271N2) = 271 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI271N2)

lemma isPrimeI271N2 : Ideal.IsPrime I271N2 := prime_ideal_of_norm_prime hp271.out _ NI271N2
def MulI271N0 : IdealMulLeCertificate' Table 
  ![![13, 3, 1, 6, -8]] ![![-6503, 7488, 228, 2054, -3253]]
  ![![-2143, 3675, 25, 994, -1857]] where
 M := ![![![-2143, 3675, 25, 994, -1857]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI271N1 : IdealMulLeCertificate' Table 
  ![![-2143, 3675, 25, 994, -1857]] ![![-5, -1, -5, -8, 9]]
  ![![271, 0, 0, 0, 0]] where
 M := ![![![271, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC271 : ContainsPrimesAboveP 271 ![I271N0, I271N1, I271N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI271N0
    exact isPrimeI271N1
    exact isPrimeI271N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 271 (by decide) (𝕀 ⊙ MulI271N0 ⊙ MulI271N1)
instance hp277 : Fact (Nat.Prime 277) := {out := by norm_num}

def I277N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-288741, 332903, 9631, 91386, -145810]] i)))

def SI277N0: IdealEqSpanCertificate' Table ![![-288741, 332903, 9631, 91386, -145810]] 
 ![![277, 0, 0, 0, 0], ![0, 277, 0, 0, 0], ![125, 97, 1, 0, 0], ![161, 193, 0, 1, 0], ![222, 272, 0, 0, 1]] where
  M :=![![![-288741, 332903, 9631, 91386, -145810], ![400468, -461882, -13379, -126786, 202272], ![-555516, 640661, 18504, 175870, -280686], ![370392, -427048, -12360, -117229, 187033], ![-94332, 108848, 3124, 29882, -47737]]]
  hmulB := by decide  
  f := ![![![-617, -749, -3447, -3454, 5446]], ![![-14876, 2844, 6173, -7410, -7840]], ![![-5321, 680, 768, -3874, -560]], ![![-10661, 1475, 2018, -7355, -1869]], ![![-15170, 2178, 3210, -10178, -3187]]]
  g := ![![![58354, 77334, 9631, 91386, -145810], ![-80935, -107265, -13379, -126786, 202272], ![112378, 148915, 18504, 175870, -280686], ![-74845, -99191, -12360, -117229, 187033], ![19140, 25354, 3124, 29882, -47737]]]
  hle1 := by decide   
  hle2 := by decide  


def P277P0 : CertificateIrreducibleZModOfList' 277 2 2 8 [42, 48, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [229, 276], [0, 1]]
 g := ![![[199, 213], [147], [74, 4], [102], [272, 194], [23], [88], [1]], ![[224, 64], [147], [159, 273], [102], [101, 83], [23], [88], [1]]]
 h' := ![![[229, 276], [40, 203], [216, 79], [205, 2], [210, 42], [191, 86], [7, 85], [235, 229], [0, 1]], ![[0, 1], [268, 74], [25, 198], [109, 275], [133, 235], [218, 191], [82, 192], [46, 48], [229, 276]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [97]]
 b := ![[], [56, 187]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI277N0 : CertifiedPrimeIdeal' SI277N0 277 where
  n := 2
  hpos := by decide
  P := [42, 48, 1]
  hirr := P277P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![461, 63, 2446, 2477, -3758]
  a := ![-1, -5, -8, -15, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![470, 1108, 2446, 2477, -3758]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI277N0 : Ideal.IsPrime I277N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI277N0 B_one_repr
lemma NI277N0 : Nat.card (O ⧸ I277N0) = 76729 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI277N0

def I277N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-81, -27, 9, -10, 41]] i)))

def SI277N1: IdealEqSpanCertificate' Table ![![-81, -27, 9, -10, 41]] 
 ![![277, 0, 0, 0, 0], ![0, 277, 0, 0, 0], ![143, 23, 1, 0, 0], ![145, 100, 0, 1, 0], ![2, 93, 0, 0, 1]] where
  M :=![![![-81, -27, 9, -10, 41], ![-144, -52, 31, 4, 53], ![-220, -121, -6, -2, 187], ![-40, 18, -36, -97, 30], ![-208, -62, 30, -32, 71]]]
  hmulB := by decide  
  f := ![![![11679, -13449, -391, -3692, 5885]], ![![-16156, 18672, 537, 5126, -8189]], ![![4769, -5486, -160, -1506, 2399]], ![![227, -237, -9, -65, 97]], ![![-5326, 6156, 177, 1690, -2700]]]
  g := ![![![0, -11, 9, -10, 41], ![-19, -22, 31, 4, 53], ![2, -62, -6, -2, 187], ![69, 28, -36, -97, 30], ![0, -15, 30, -32, 71]]]
  hle1 := by decide   
  hle2 := by decide  


def P277P1 : CertificateIrreducibleZModOfList' 277 2 2 8 [79, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [261, 276], [0, 1]]
 g := ![![[165, 270], [188], [93, 21], [91], [112, 268], [249], [256], [1]], ![[0, 7], [188], [34, 256], [91], [256, 9], [249], [256], [1]]]
 h' := ![![[261, 276], [79, 230], [132, 241], [269, 129], [16, 214], [234, 97], [144, 94], [198, 261], [0, 1]], ![[0, 1], [0, 47], [154, 36], [144, 148], [193, 63], [67, 180], [25, 183], [177, 16], [261, 276]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37]]
 b := ![[], [148, 157]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI277N1 : CertifiedPrimeIdeal' SI277N1 277 where
  n := 2
  hpos := by decide
  P := [79, 16, 1]
  hirr := P277P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-132964, -8116, -58191, -152778, 117984]
  a := ![-45, -32, -57, -62, 159]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![108683, 20345, -58191, -152778, 117984]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI277N1 : Ideal.IsPrime I277N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI277N1 B_one_repr
lemma NI277N1 : Nat.card (O ⧸ I277N1) = 76729 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI277N1

def I277N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-25, -6, -36, -52, 59]] i)))

def SI277N2: IdealEqSpanCertificate' Table ![![-25, -6, -36, -52, 59]] 
 ![![277, 0, 0, 0, 0], ![157, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![148, 0, 0, 1, 0], ![78, 0, 0, 0, 1]] where
  M :=![![![-25, -6, -36, -52, 59], ![-132, 43, 130, -2, -187], ![752, 2, 311, 904, -575], ![-220, -198, -936, -983, 1485], ![-340, -14, -198, -458, 349]]]
  hmulB := by decide  
  f := ![![![-4209, -4868, 658, -1238, 4455]], ![![-2441, -2763, 378, -702, 2542]], ![![-128, -120, 17, -30, 113]], ![![-2244, -2584, 350, -657, 2367]], ![![-1234, -1394, 190, -354, 1281]]]
  g := ![![![15, -6, -36, -52, 59], ![27, 43, 130, -2, -187], ![-324, 2, 311, 904, -575], ![232, -198, -936, -983, 1485], ![156, -14, -198, -458, 349]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI277N2 : Nat.card (O ⧸ I277N2) = 277 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI277N2)

lemma isPrimeI277N2 : Ideal.IsPrime I277N2 := prime_ideal_of_norm_prime hp277.out _ NI277N2
def MulI277N0 : IdealMulLeCertificate' Table 
  ![![-288741, 332903, 9631, 91386, -145810]] ![![-81, -27, 9, -10, 41]]
  ![![4209, 4868, -658, 1238, -4455]] where
 M := ![![![4209, 4868, -658, 1238, -4455]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI277N1 : IdealMulLeCertificate' Table 
  ![![4209, 4868, -658, 1238, -4455]] ![![-25, -6, -36, -52, 59]]
  ![![277, 0, 0, 0, 0]] where
 M := ![![![-277, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC277 : ContainsPrimesAboveP 277 ![I277N0, I277N1, I277N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI277N0
    exact isPrimeI277N1
    exact isPrimeI277N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 277 (by decide) (𝕀 ⊙ MulI277N0 ⊙ MulI277N1)
instance hp281 : Fact (Nat.Prime 281) := {out := by norm_num}

def I281N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![281, 0, 0, 0, 0]] i)))

def SI281N0: IdealEqSpanCertificate' Table ![![281, 0, 0, 0, 0]] 
 ![![281, 0, 0, 0, 0], ![0, 281, 0, 0, 0], ![0, 0, 281, 0, 0], ![0, 0, 0, 281, 0], ![0, 0, 0, 0, 281]] where
  M :=![![![281, 0, 0, 0, 0], ![0, 281, 0, 0, 0], ![0, 0, 281, 0, 0], ![0, 0, 0, 281, 0], ![0, 0, 0, 0, 281]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P281P0 : CertificateIrreducibleZModOfList' 281 5 2 8 [69, 164, 248, 103, 98, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [115, 71, 239, 235, 247], [216, 150, 235, 5, 138], [260, 160, 94, 150, 29], [154, 180, 275, 172, 148], [0, 1]]
 g := ![![[92, 31, 113, 262, 163], [111, 264, 39, 111], [123, 87, 13, 144], [61, 72, 202, 275, 232], [0, 28, 222, 42, 80], [147, 228, 183, 1], [], []], ![[169, 239, 24, 271, 142, 247, 8, 111], [39, 13, 245, 280], [60, 226, 102, 273], [115, 202, 217, 119, 186, 80, 127, 155], [181, 46, 225, 147, 89, 21, 56, 121], [235, 258, 241, 20], [237, 54, 40, 195], [91, 212, 273, 32]], ![[56, 57, 180, 220, 262, 41, 40, 212], [82, 105, 21, 162], [208, 102, 186, 196], [180, 280, 97, 86, 196, 4, 52, 145], [8, 144, 210, 177, 80, 235, 79, 31], [248, 165, 178, 271], [146, 132, 28, 231], [280, 196, 65, 217]], ![[171, 85, 166, 186, 240, 251, 155, 14], [117, 88, 229, 119], [99, 88, 0, 238], [128, 56, 2, 196, 34, 89, 70, 172], [176, 25, 209, 206, 21, 168, 93, 66], [204, 37, 61, 276], [170, 251, 131, 7], [7, 193, 185, 279]], ![[23, 13, 51, 45, 210, 143, 228, 48], [122, 153, 6, 203], [191, 88, 93, 90], [141, 192, 71, 237, 251, 85, 247, 19], [149, 238, 61, 57, 115, 247, 11, 278], [137, 178, 117, 43], [128, 59, 64, 145], [44, 229, 18, 267]]]
 h' := ![![[115, 71, 239, 235, 247], [88, 102, 227, 53, 238], [260, 134, 50, 99, 119], [6, 202, 152, 249, 12], [0, 202, 65, 17, 90], [254, 62, 73, 237, 19], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[216, 150, 235, 5, 138], [244, 232, 52, 110, 75], [187, 93, 180, 102, 228], [154, 40, 269, 154, 58], [180, 119, 183, 104, 268], [99, 92, 121, 256, 125], [4, 240, 232, 106, 131], [202, 266, 136, 134, 40], [115, 71, 239, 235, 247]], ![[260, 160, 94, 150, 29], [125, 161, 60, 114, 155], [43, 151, 261, 159, 217], [273, 176, 62, 231, 14], [237, 14, 99, 117, 137], [114, 226, 170, 268, 10], [101, 263, 198, 248, 208], [79, 17, 248, 208, 145], [216, 150, 235, 5, 138]], ![[154, 180, 275, 172, 148], [155, 116, 116, 55, 42], [109, 70, 32, 220, 20], [14, 177, 124, 100, 111], [26, 63, 182, 126, 218], [275, 130, 96, 148, 254], [150, 9, 143, 180, 240], [239, 171, 227, 69, 179], [260, 160, 94, 150, 29]], ![[0, 1], [169, 232, 107, 230, 52], [193, 114, 39, 263, 259], [181, 248, 236, 109, 86], [220, 164, 33, 198, 130], [173, 52, 102, 215, 154], [230, 50, 270, 28, 263], [167, 108, 231, 151, 198], [154, 180, 275, 172, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [153, 272, 55, 23], [], [], []]
 b := ![[], [155, 184, 5, 102, 42], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI281N0 : CertifiedPrimeIdeal' SI281N0 281 where
  n := 5
  hpos := by decide
  P := [69, 164, 248, 103, 98, 1]
  hirr := P281P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![25938366337715, -1731325316860, 3065112048298, 24682442549040, -7880140139664]
  a := ![-23, -17, -32, -35, 81]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![92307353515, -6161300060, 10907872058, 87837873840, -28043203344]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI281N0 : Ideal.IsPrime I281N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI281N0 B_one_repr
lemma NI281N0 : Nat.card (O ⧸ I281N0) = 1751989905401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI281N0

def PBC281 : ContainsPrimesAboveP 281 ![I281N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI281N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![281, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 281 (by decide) 𝕀

instance hp283 : Fact (Nat.Prime 283) := {out := by norm_num}

def I283N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![283, 0, 0, 0, 0]] i)))

def SI283N0: IdealEqSpanCertificate' Table ![![283, 0, 0, 0, 0]] 
 ![![283, 0, 0, 0, 0], ![0, 283, 0, 0, 0], ![0, 0, 283, 0, 0], ![0, 0, 0, 283, 0], ![0, 0, 0, 0, 283]] where
  M :=![![![283, 0, 0, 0, 0], ![0, 283, 0, 0, 0], ![0, 0, 283, 0, 0], ![0, 0, 0, 283, 0], ![0, 0, 0, 0, 283]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P283P0 : CertificateIrreducibleZModOfList' 283 5 2 8 [259, 98, 74, 230, 236, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [197, 187, 176, 98, 258], [39, 72, 29, 155, 99], [147, 270, 158, 19, 83], [230, 36, 203, 11, 126], [0, 1]]
 g := ![![[20, 189, 80, 116, 144], [176, 57, 253, 84, 96], [222, 273, 98, 90], [31, 96, 274, 251, 81], [60, 154, 85, 24, 204], [59, 281, 47, 1], [], []], ![[96, 128, 137, 221, 67, 65, 25, 17], [98, 65, 96, 97, 51, 27, 201, 149], [193, 59, 236, 185], [79, 97, 262, 66, 274, 87, 148, 180], [81, 204, 11, 102, 214, 19, 207, 276], [247, 203, 176, 105], [153, 43, 219, 152], [88, 182, 137, 59]], ![[108, 160, 81, 125, 39, 279, 17, 24], [25, 268, 264, 71, 168, 248, 68, 141], [95, 212, 131, 216], [278, 62, 87, 66, 254, 191, 84, 227], [160, 84, 53, 190, 112, 207, 62, 61], [169, 239, 86, 165], [200, 26, 158, 15], [58, 239, 49, 179]], ![[14, 224, 176, 17, 209, 213, 264, 269], [36, 130, 56, 162, 57, 230, 75, 141], [137, 41, 206, 248], [272, 60, 180, 89, 9, 94, 258, 52], [62, 245, 152, 180, 251, 26, 220, 256], [124, 177, 90, 195], [96, 22, 239, 71], [103, 22, 72, 97]], ![[277, 108, 206, 266, 8, 195, 61, 122], [19, 132, 152, 132, 91, 267, 127, 114], [122, 121, 134, 85], [131, 55, 131, 52, 115, 151, 244, 276], [98, 145, 80, 268, 158, 246, 126, 8], [47, 27, 145, 152], [271, 167, 185, 40], [15, 102, 126, 28]]]
 h' := ![![[197, 187, 176, 98, 258], [262, 10, 84, 53, 12], [222, 45, 43, 59, 68], [178, 174, 56, 215, 72], [25, 81, 280, 54, 9], [1, 113, 71, 108, 223], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[39, 72, 29, 155, 99], [131, 63, 235, 226, 105], [205, 75, 282, 129, 126], [147, 234, 216, 272, 243], [32, 260, 144, 191, 39], [260, 136, 145, 263, 44], [254, 162, 94, 126, 117], [169, 87, 51, 137, 172], [197, 187, 176, 98, 258]], ![[147, 270, 158, 19, 83], [116, 23, 36, 9, 229], [13, 235, 238, 88, 259], [194, 126, 280, 177, 102], [214, 273, 112, 238, 105], [132, 213, 104, 11, 55], [86, 181, 137, 55, 221], [83, 8, 152, 16, 204], [39, 72, 29, 155, 99]], ![[230, 36, 203, 11, 126], [239, 155, 180, 8, 261], [204, 47, 136, 59, 184], [245, 249, 205, 265, 208], [271, 271, 265, 32, 104], [6, 250, 185, 214, 238], [150, 180, 154, 59, 55], [26, 196, 83, 15, 142], [147, 270, 158, 19, 83]], ![[0, 1], [48, 32, 31, 270, 242], [199, 164, 150, 231, 212], [147, 66, 92, 203, 224], [262, 247, 48, 51, 26], [37, 137, 61, 253, 6], [18, 43, 181, 43, 172], [56, 275, 279, 115, 48], [230, 36, 203, 11, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [76, 227, 102, 237], [], [], []]
 b := ![[], [219, 181, 23, 197, 134], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI283N0 : CertifiedPrimeIdeal' SI283N0 283 where
  n := 5
  hpos := by decide
  P := [259, 98, 74, 230, 236, 1]
  hirr := P283P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-64432600339, -5022160167, -47119190115, -94776977623, 81247461349]
  a := ![2, 5, 9, 15, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-227677033, -17746149, -166498905, -334900981, 287093503]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI283N0 : Ideal.IsPrime I283N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI283N0 B_one_repr
lemma NI283N0 : Nat.card (O ⧸ I283N0) = 1815232161643 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI283N0

def PBC283 : ContainsPrimesAboveP 283 ![I283N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI283N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![283, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 283 (by decide) 𝕀

instance hp293 : Fact (Nat.Prime 293) := {out := by norm_num}

def I293N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-667, 1488, -34, 404, -865]] i)))

def SI293N0: IdealEqSpanCertificate' Table ![![-667, 1488, -34, 404, -865]] 
 ![![293, 0, 0, 0, 0], ![0, 293, 0, 0, 0], ![51, 16, 1, 0, 0], ![210, 234, 0, 1, 0], ![232, 6, 0, 0, 1]] where
  M :=![![![-667, 1488, -34, 404, -865], ![2652, -1509, -196, -426, 233], ![-80, 3308, -197, 880, -2283], ![1220, -1786, -4, -489, 911], ![1012, 922, -158, 234, -933]]]
  hmulB := by decide  
  f := ![![![917, -94, -28, 758, -65]], ![![-1256, -627, -3182, -3772, 5111]], ![![47, -40, -151, -88, 230]], ![![-278, -570, -2542, -2395, 3997]], ![![724, -92, -98, 534, 67]]]
  g := ![![![399, -298, -34, 404, -865], ![164, 341, -196, -426, 233], ![1211, -634, -197, 880, -2283], ![-366, 366, -4, -489, 911], ![602, -156, -158, 234, -933]]]
  hle1 := by decide   
  hle2 := by decide  


def P293P0 : CertificateIrreducibleZModOfList' 293 2 2 8 [206, 187, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [106, 292], [0, 1]]
 g := ![![[45, 229], [184], [222, 40], [256], [224], [259, 178], [102], [1]], ![[0, 64], [184], [67, 253], [256], [224], [82, 115], [102], [1]]]
 h' := ![![[106, 292], [176, 225], [269, 188], [99, 178], [55, 277], [265, 215], [35, 249], [87, 106], [0, 1]], ![[0, 1], [0, 68], [273, 105], [215, 115], [117, 16], [201, 78], [59, 44], [189, 187], [106, 292]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [181]]
 b := ![[], [38, 237]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI293N0 : CertifiedPrimeIdeal' SI293N0 293 where
  n := 2
  hpos := by decide
  P := [206, 187, 1]
  hirr := P293P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-952224, -59176, -463874, -1143798, 883099]
  a := ![127, 90, 156, 164, -441]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![198034, 920522, -463874, -1143798, 883099]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI293N0 : Ideal.IsPrime I293N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI293N0 B_one_repr
lemma NI293N0 : Nat.card (O ⧸ I293N0) = 85849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI293N0

def I293N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17, 13, 11, 4, -20]] i)))

def SI293N1: IdealEqSpanCertificate' Table ![![-17, 13, 11, 4, -20]] 
 ![![293, 0, 0, 0, 0], ![0, 293, 0, 0, 0], ![242, 242, 1, 0, 0], ![181, 22, 0, 1, 0], ![9, 5, 0, 0, 1]] where
  M :=![![![-17, 13, 11, 4, -20], ![72, -14, 19, 64, -32], ![0, -37, -232, -180, 352], ![-280, 54, 166, -109, -219], ![-28, 32, 112, 74, -173]]]
  hmulB := by decide  
  f := ![![![-1693, -419, 317, -112, 1060]], ![![-4016, -1152, 663, -292, 2396]], ![![-4746, -1307, 814, -336, 2872]], ![![-1345, -345, 245, -91, 833]], ![![-141, -39, 24, -10, 85]]]
  g := ![![![-11, -9, 11, 4, -20], ![-54, -20, 19, 64, -32], ![292, 199, -232, -180, 352], ![-64, -125, 166, -109, -219], ![-133, -95, 112, 74, -173]]]
  hle1 := by decide   
  hle2 := by decide  


def P293P1 : CertificateIrreducibleZModOfList' 293 2 2 8 [42, 28, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [265, 292], [0, 1]]
 g := ![![[196, 222], [96], [118, 59], [228], [196], [215, 82], [198], [1]], ![[133, 71], [96], [224, 234], [228], [196], [263, 211], [198], [1]]]
 h' := ![![[265, 292], [109, 145], [25, 168], [26, 158], [144, 98], [53, 14], [187, 31], [251, 265], [0, 1]], ![[0, 1], [151, 148], [9, 125], [290, 135], [37, 195], [247, 279], [198, 262], [156, 28], [265, 292]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [78]]
 b := ![[], [253, 39]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI293N1 : CertifiedPrimeIdeal' SI293N1 293 where
  n := 2
  hpos := by decide
  P := [42, 28, 1]
  hirr := P293P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-59233, -2970, -26156, -69084, 51000]
  a := ![31, 23, 39, 42, -108]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![62511, 25910, -26156, -69084, 51000]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI293N1 : Ideal.IsPrime I293N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI293N1 B_one_repr
lemma NI293N1 : Nat.card (O ⧸ I293N1) = 85849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI293N1

def I293N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, 3, 1, 4, -5]] i)))

def SI293N2: IdealEqSpanCertificate' Table ![![9, 3, 1, 4, -5]] 
 ![![293, 0, 0, 0, 0], ![35, 1, 0, 0, 0], ![240, 0, 1, 0, 0], ![42, 0, 0, 1, 0], ![218, 0, 0, 0, 1]] where
  M :=![![![9, 3, 1, 4, -5], ![12, 2, -11, -6, 13], ![-40, 13, 4, -40, -3], ![40, 4, 46, 77, -74], ![32, 2, 2, 24, -7]]]
  hmulB := by decide  
  f := ![![![-29575, 34109, 993, 9362, -14925]], ![![-3393, 3913, 114, 1074, -1712]], ![![-24420, 28163, 820, 7730, -12323]], ![![-4110, 4740, 138, 1301, -2074]], ![![-22038, 25416, 740, 6976, -11121]]]
  g := ![![![2, 3, 1, 4, -5], ![0, 2, -11, -6, 13], ![3, 13, 4, -40, -3], ![6, 4, 46, 77, -74], ![0, 2, 2, 24, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI293N2 : Nat.card (O ⧸ I293N2) = 293 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI293N2)

lemma isPrimeI293N2 : Ideal.IsPrime I293N2 := prime_ideal_of_norm_prime hp293.out _ NI293N2
def MulI293N0 : IdealMulLeCertificate' Table 
  ![![-667, 1488, -34, 404, -865]] ![![-17, 13, 11, 4, -20]]
  ![![29575, -34109, -993, -9362, 14925]] where
 M := ![![![29575, -34109, -993, -9362, 14925]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI293N1 : IdealMulLeCertificate' Table 
  ![![29575, -34109, -993, -9362, 14925]] ![![9, 3, 1, 4, -5]]
  ![![293, 0, 0, 0, 0]] where
 M := ![![![-293, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC293 : ContainsPrimesAboveP 293 ![I293N0, I293N1, I293N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI293N0
    exact isPrimeI293N1
    exact isPrimeI293N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 293 (by decide) (𝕀 ⊙ MulI293N0 ⊙ MulI293N1)
instance hp307 : Fact (Nat.Prime 307) := {out := by norm_num}

def I307N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![307, 0, 0, 0, 0]] i)))

def SI307N0: IdealEqSpanCertificate' Table ![![307, 0, 0, 0, 0]] 
 ![![307, 0, 0, 0, 0], ![0, 307, 0, 0, 0], ![0, 0, 307, 0, 0], ![0, 0, 0, 307, 0], ![0, 0, 0, 0, 307]] where
  M :=![![![307, 0, 0, 0, 0], ![0, 307, 0, 0, 0], ![0, 0, 307, 0, 0], ![0, 0, 0, 307, 0], ![0, 0, 0, 0, 307]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P307P0 : CertificateIrreducibleZModOfList' 307 5 2 8 [7, 120, 178, 124, 80, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 217, 137, 140, 223], [93, 6, 13, 145, 236], [156, 52, 187, 2, 2], [258, 31, 277, 20, 153], [0, 1]]
 g := ![![[40, 218, 155, 78, 248], [296, 37, 202, 230, 89], [113, 176, 20, 149], [160, 217, 127, 225], [199, 91, 243, 17, 6], [187, 90, 136, 227, 1], [], []], ![[88, 108, 213, 35, 250, 43, 292, 183], [292, 199, 25, 155, 41, 173, 73, 105], [66, 273, 3, 93], [127, 267, 203, 127], [115, 272, 30, 261, 39, 86, 106, 79], [84, 139, 49, 142, 136, 15, 84, 97], [174, 188, 195, 199], [189, 199, 212, 302]], ![[45, 256, 250, 235, 50, 202, 78, 84], [62, 280, 87, 104, 304, 87, 71, 198], [193, 220, 282, 112], [129, 146, 223, 28], [161, 271, 209, 31, 211, 116], [301, 15, 279, 83, 189, 263, 153, 31], [187, 132, 114, 187], [72, 28, 97, 129]], ![[155, 219, 243, 62, 179, 257, 245, 221], [116, 203, 13, 299, 24, 99, 52, 137], [9, 60, 148, 28], [136, 134, 260, 246], [181, 23, 63, 141, 179, 279, 102, 111], [267, 72, 157, 153, 63, 196, 61, 59], [88, 272, 75, 219], [267, 42, 302, 4]], ![[203, 249, 53, 124, 26, 94, 261, 107], [112, 293, 278, 227, 267, 137, 195, 121], [252, 12, 245, 101], [117, 164, 57, 44], [70, 164, 236, 34, 58, 284, 197, 229], [290, 143, 122, 232, 106, 57, 71, 183], [149, 288, 32, 112], [200, 222, 267, 77]]]
 h' := ![![[27, 217, 137, 140, 223], [77, 236, 279, 162, 52], [230, 246, 234, 129, 157], [10, 230, 295, 20, 145], [142, 157, 78, 20, 292], [226, 262, 91, 292, 96], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[93, 6, 13, 145, 236], [300, 280, 212, 99, 76], [218, 31, 117, 51, 265], [56, 258, 51, 117, 20], [115, 221, 57, 105, 197], [38, 88, 272, 37, 284], [103, 285, 218, 10, 69], [20, 232, 86, 254, 210], [27, 217, 137, 140, 223]], ![[156, 52, 187, 2, 2], [226, 222, 149, 86, 271], [18, 74, 167, 186, 255], [270, 22, 256, 107, 135], [49, 225, 103, 241, 86], [190, 29, 198, 144], [86, 34, 218, 132, 140], [163, 262, 28, 57, 143], [93, 6, 13, 145, 236]], ![[258, 31, 277, 20, 153], [254, 160, 191, 262, 195], [66, 89, 271, 72, 284], [71, 22, 44, 71, 86], [193, 5, 269, 250, 89], [82, 171, 205, 26, 165], [64, 42, 172, 16, 45], [56, 161, 228, 15, 126], [156, 52, 187, 2, 2]], ![[0, 1], [120, 23, 90, 5, 20], [178, 174, 132, 176, 267], [10, 82, 275, 299, 228], [198, 6, 107, 305, 257], [243, 64, 155, 115, 69], [138, 253, 6, 149, 52], [80, 266, 271, 288, 135], [258, 31, 277, 20, 153]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [213, 58, 284, 146], [], [], []]
 b := ![[], [104, 162, 227, 177, 126], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI307N0 : CertifiedPrimeIdeal' SI307N0 307 where
  n := 5
  hpos := by decide
  P := [7, 120, 178, 124, 80, 1]
  hirr := P307P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5158276869916, -1195344607094, -7162380895817, -10469226116952, 11786109852328]
  a := ![-17, -5, -8, 4, 61]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-16802204788, -3893630642, -23330230931, -34101713736, 38391237304]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI307N0 : Ideal.IsPrime I307N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI307N0 B_one_repr
lemma NI307N0 : Nat.card (O ⧸ I307N0) = 2727042318307 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI307N0

def PBC307 : ContainsPrimesAboveP 307 ![I307N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI307N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![307, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 307 (by decide) 𝕀



lemma PB312I6_primes (p : ℕ) :
  p ∈ Set.range ![257, 263, 269, 271, 277, 281, 283, 293, 307] ↔ Nat.Prime p ∧ 251 < p ∧ p ≤ 307 := by
  rw [← List.mem_ofFn']
  convert primes_range 251 307 (by omega)

def PB312I6 : PrimesBelowBoundCertificateInterval O 251 307 312 where
  m := 9
  g := ![1, 3, 3, 3, 3, 1, 1, 3, 1]
  P := ![257, 263, 269, 271, 277, 281, 283, 293, 307]
  hP := PB312I6_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I257N0]
    · exact ![I263N0, I263N1, I263N2]
    · exact ![I269N0, I269N1, I269N2]
    · exact ![I271N0, I271N1, I271N2]
    · exact ![I277N0, I277N1, I277N2]
    · exact ![I281N0]
    · exact ![I283N0]
    · exact ![I293N0, I293N1, I293N2]
    · exact ![I307N0]
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
    · exact ![1121154893057]
    · exact ![69169, 69169, 263]
    · exact ![72361, 72361, 269]
    · exact ![73441, 73441, 271]
    · exact ![76729, 76729, 277]
    · exact ![1751989905401]
    · exact ![1815232161643]
    · exact ![85849, 85849, 293]
    · exact ![2727042318307]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI257N0
    · dsimp ; intro j
      fin_cases j
      exact NI263N0
      exact NI263N1
      exact NI263N2
    · dsimp ; intro j
      fin_cases j
      exact NI269N0
      exact NI269N1
      exact NI269N2
    · dsimp ; intro j
      fin_cases j
      exact NI271N0
      exact NI271N1
      exact NI271N2
    · dsimp ; intro j
      fin_cases j
      exact NI277N0
      exact NI277N1
      exact NI277N2
    · dsimp ; intro j
      fin_cases j
      exact NI281N0
    · dsimp ; intro j
      fin_cases j
      exact NI283N0
    · dsimp ; intro j
      fin_cases j
      exact NI293N0
      exact NI293N1
      exact NI293N2
    · dsimp ; intro j
      fin_cases j
      exact NI307N0
  β := ![I263N2, I269N2, I271N2, I277N2, I293N2]
  Il := ![[], [I263N2], [I269N2], [I271N2], [I277N2], [], [], [I293N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
