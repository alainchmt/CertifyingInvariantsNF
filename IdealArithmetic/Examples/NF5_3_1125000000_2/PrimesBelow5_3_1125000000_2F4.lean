
import IdealArithmetic.Examples.NF5_3_1125000000_2.RI5_3_1125000000_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3874, 1344, 3146, -385, -499]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![-3874, 1344, 3146, -385, -499]] 
 ![![157, 0, 0, 0, 0], ![0, 157, 0, 0, 0], ![0, 0, 157, 0, 0], ![0, 0, 0, 157, 0], ![15, 109, 11, 53, 1]] where
  M :=![![![-3874, 1344, 3146, -385, -499], ![-4990, 1995, 3458, -466, -542], ![-2710, 665, 2461, -260, -390], ![545, -17, -804, 94, 141], ![1220, -921, -152, 124, 29]]]
  hmulB := by decide  
  f := ![![![-18, 22, -12, -15, 13]], ![![130, -151, 74, 102, -86]], ![![-430, 505, -253, -340, 290]], ![![1385, -1621, 808, 1096, -927]], ![![505, -590, 293, 399, -337]]]
  g := ![![![23, 355, 55, 166, -499], ![20, 389, 60, 180, -542], ![20, 275, 43, 130, -390], ![-10, -98, -15, -47, 141], ![5, -26, -3, -9, 29]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 4 2 7 [14, 29, 114, 15, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [98, 44, 112, 155], [98, 33, 94, 23], [103, 79, 108, 136], [0, 1]]
 g := ![![[150, 87, 104, 132], [59, 95, 141], [147, 30, 114, 141], [47, 125, 33, 14], [142, 101, 45, 68], [1], []], ![[96, 152, 78, 72, 135, 92], [109, 128, 64], [47, 8, 51, 64, 88, 69], [18, 134, 117, 34, 104, 5], [119, 96, 41, 150, 92, 134], [120, 76, 75], [64, 120, 4]], ![[145, 140, 12, 92, 143, 65], [143, 104, 111], [124, 13, 19, 68, 109, 23], [25, 8, 68, 136, 66, 88], [33, 98, 47, 5, 19, 151], [1], [131, 0, 58]], ![[107, 27, 85, 9, 98, 149], [10, 35, 144], [2, 153, 74, 96, 124, 54], [59, 152, 9, 143, 87, 38], [108, 67, 16, 5, 8, 32], [120, 76, 75], [51, 153, 127]]]
 h' := ![![[98, 44, 112, 155], [91, 138, 89, 17], [140, 142, 115, 112], [127, 10, 30, 45], [53, 2, 62, 64], [143, 128, 43, 142], [0, 0, 1], [0, 1]], ![[98, 33, 94, 23], [32, 88, 145, 116], [50, 30, 89, 149], [107, 81, 150, 94], [116, 110, 43, 95], [38, 90, 75, 103], [73, 64, 25, 46], [98, 44, 112, 155]], ![[103, 79, 108, 136], [150, 132, 11, 101], [41, 91, 12, 41], [68, 58, 1, 1], [96, 42, 152, 132], [106, 128, 46, 142], [77, 0, 156], [98, 33, 94, 23]], ![[0, 1], [48, 113, 69, 80], [38, 51, 98, 12], [137, 8, 133, 17], [37, 3, 57, 23], [63, 125, 150, 84], [4, 93, 132, 111], [103, 79, 108, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [33, 122, 126], []]
 b := ![[], [], [77, 55, 56, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 4
  hpos := by decide
  P := [14, 29, 114, 15, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![32796615694, 8274518586, -31946753934, 59268016386, 41972403491]
  a := ![0, -7, 2, -8, -11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3801206603, -29087372369, -3144224155, -13791524641, 41972403491]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 607573201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![18, -22, 12, 15, -13]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![18, -22, 12, 15, -13]] 
 ![![157, 0, 0, 0, 0], ![104, 1, 0, 0, 0], ![87, 0, 1, 0, 0], ![134, 0, 0, 1, 0], ![130, 0, 0, 0, 1]] where
  M :=![![![18, -22, 12, 15, -13], ![-130, 151, -74, -102, 86], ![430, -505, 253, 340, -290], ![-1385, 1621, -808, -1096, 927], ![3290, -3857, 1926, 2598, -2211]]]
  hmulB := by decide  
  f := ![![![3874, -1344, -3146, 385, 499]], ![![2598, -903, -2106, 258, 334]], ![![2164, -749, -1759, 215, 279]], ![![3303, -1147, -2680, 328, 425]], ![![3200, -1107, -2604, 318, 413]]]
  g := ![![![6, -22, 12, 15, -13], ![-44, 151, -74, -102, 86], ![147, -505, 253, 340, -290], ![-467, 1621, -808, -1096, 927], ![1122, -3857, 1926, 2598, -2211]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![-3874, 1344, 3146, -385, -499]] ![![18, -22, 12, 15, -13]]
  ![![157, 0, 0, 0, 0]] where
 M := ![![![-157, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC157 : ContainsPrimesAboveP 157 ![I157N0, I157N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
    exact isPrimeI157N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 157 (by decide) (𝕀 ⊙ MulI157N0)
instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-278902, 59649, 174414, -19767, -27209]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![-278902, 59649, 174414, -19767, -27209]] 
 ![![163, 0, 0, 0, 0], ![0, 163, 0, 0, 0], ![0, 0, 163, 0, 0], ![8, 22, 36, 1, 0], ![15, 12, 78, 0, 1]] where
  M :=![![![-278902, 59649, 174414, -19767, -27209], ![-272090, 46441, 158832, -17214, -24650], ![-123250, 12432, 63655, -6282, -9778], ![87155, -25077, -60702, 7312, 9539], ![54690, -10890, -33432, 3732, 5209]]]
  hmulB := by decide  
  f := ![![![-15514, 26457, -21906, -423, 3817]], ![![38170, -64985, 53760, 1146, -9326]], ![![-46630, 79752, -66131, -1050, 11618]], ![![-5669, 9739, -8094, -86, 1439]], ![![-21450, 36705, -30444, -465, 5356]]]
  g := ![![![1763, 5037, 18456, -19767, -27209], ![1444, 4423, 16572, -17214, -24650], ![452, 1644, 6457, -6282, -9778], ![-702, -1843, -6552, 7312, 9539], ![-327, -954, -3522, 3732, 5209]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [1, 101, 83, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [95, 136, 122], [148, 26, 41], [0, 1]]
 g := ![![[68, 160, 113], [127, 33, 38], [162, 35], [95, 96], [127, 49], [105, 80, 1], []], ![[64, 82, 115, 99], [123, 118, 71, 27], [142, 152], [158, 71], [7, 53], [146, 114, 132, 157], [100, 51]], ![[89, 114, 72, 38], [157, 44, 59, 43], [151, 140], [76, 87], [138, 53], [15, 22, 102, 60], [18, 51]]]
 h' := ![![[95, 136, 122], [36, 5, 90], [92, 7, 53], [108, 85, 19], [140, 156, 111], [58, 73, 156], [0, 0, 1], [0, 1]], ![[148, 26, 41], [8, 132, 16], [104, 28, 113], [88, 114, 106], [88, 13, 76], [101, 24, 85], [123, 41, 26], [95, 136, 122]], ![[0, 1], [9, 26, 57], [37, 128, 160], [158, 127, 38], [76, 157, 139], [122, 66, 85], [44, 122, 136], [148, 26, 41]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [84, 151], []]
 b := ![[], [18, 98, 115], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [1, 101, 83, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6778776502, 443546770, 4245451367, -10712042441, -5724713694]
  a := ![3, -62, -1, -63, -58]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1010970972, 1869969600, 5131329125, -10712042441, -5724713694]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 4330747 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-87, 103, -52, -68, 60]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![-87, 103, -52, -68, 60]] 
 ![![163, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![113, 0, 1, 0, 0], ![82, 0, 0, 1, 0], ![50, 0, 0, 0, 1]] where
  M :=![![![-87, 103, -52, -68, 60], ![600, -695, 342, 480, -392], ![-1960, 2323, -1175, -1530, 1352], ![6460, -7482, 3682, 5167, -4216], ![-15050, 17747, -8924, -11812, 10255]]]
  hmulB := by decide  
  f := ![![![40091, -23859, -39730, 5528, 6364]], ![![2850, -1667, -2798, 388, 448]], ![![28081, -16678, -27795, 3866, 4452]], ![![20174, -11990, -19978, 2779, 3200]], ![![12240, -7287, -12130, 1688, 1943]]]
  g := ![![![45, 103, -52, -68, 60], ![-312, -695, 342, 480, -392], ![1015, 2323, -1175, -1530, 1352], ![-3360, -7482, 3682, 5167, -4216], ![7802, 17747, -8924, -11812, 10255]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1

def I163N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, -3, 2, 1, -1]] i)))

def SI163N2: IdealEqSpanCertificate' Table ![![2, -3, 2, 1, -1]] 
 ![![163, 0, 0, 0, 0], ![81, 1, 0, 0, 0], ![61, 0, 1, 0, 0], ![97, 0, 0, 1, 0], ![137, 0, 0, 0, 1]] where
  M :=![![![2, -3, 2, 1, -1], ![-10, 13, -8, -6, 6], ![30, -36, 19, 22, -18], ![-85, 103, -54, -64, 59], ![210, -246, 124, 164, -135]]]
  hmulB := by decide  
  f := ![![![-946, -187, 226, 1, -31]], ![![-472, -96, 110, 1, -15]], ![![-352, -73, 81, 1, -11]], ![![-559, -112, 132, 1, -18]], ![![-794, -157, 190, 1, -26]]]
  g := ![![![1, -3, 2, 1, -1], ![-5, 13, -8, -6, 6], ![13, -36, 19, 22, -18], ![-43, 103, -54, -64, 59], ![93, -246, 124, 164, -135]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N2 : Nat.card (O ⧸ I163N2) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N2)

lemma isPrimeI163N2 : Ideal.IsPrime I163N2 := prime_ideal_of_norm_prime hp163.out _ NI163N2
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![-278902, 59649, 174414, -19767, -27209]] ![![-87, 103, -52, -68, 60]]
  ![![3064, -668, -2566, 55, 577]] where
 M := ![![![3064, -668, -2566, 55, 577]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI163N1 : IdealMulLeCertificate' Table 
  ![![3064, -668, -2566, 55, 577]] ![![2, -3, 2, 1, -1]]
  ![![163, 0, 0, 0, 0]] where
 M := ![![![52323, -61777, 31296, 41728, -35534]]]
 hmul := by decide  
 g := ![![![![321, -379, 192, 256, -218]]]]
 hle2 := by decide  


def PBC163 : ContainsPrimesAboveP 163 ![I163N0, I163N1, I163N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
    exact isPrimeI163N1
    exact isPrimeI163N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 163 (by decide) (𝕀 ⊙ MulI163N0 ⊙ MulI163N1)
instance hp167 : Fact (Nat.Prime 167) := {out := by norm_num}

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0, 0, 0]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0, 0, 0]] 
 ![![167, 0, 0, 0, 0], ![0, 167, 0, 0, 0], ![0, 0, 167, 0, 0], ![0, 0, 0, 167, 0], ![0, 0, 0, 0, 167]] where
  M :=![![![167, 0, 0, 0, 0], ![0, 167, 0, 0, 0], ![0, 0, 167, 0, 0], ![0, 0, 0, 167, 0], ![0, 0, 0, 0, 167]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 5 2 7 [70, 110, 107, 3, 33, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 138, 156, 21, 39], [1, 150, 103, 121, 42], [46, 66, 13, 100, 106], [61, 146, 62, 92, 147], [0, 1]]
 g := ![![[138, 71, 100, 66, 127], [55, 92, 2, 67, 115], [97, 22, 161, 95, 89], [66, 152, 63, 121], [64, 163, 166, 87], [1], []], ![[85, 127, 13, 126, 6, 57, 80, 110], [66, 67, 82, 113, 45, 33, 126, 23], [125, 136, 118, 107, 47, 65, 31, 15], [129, 55, 7, 27], [88, 160, 164, 25], [80, 6, 85, 9, 156, 76, 39, 46], [59, 147, 42, 18]], ![[58, 28, 157, 37, 35, 90, 17, 31], [100, 126, 150, 65, 164, 6, 10, 76], [13, 125, 121, 80, 92, 49, 59, 56], [38, 25, 95, 27], [151, 149, 145, 75], [37, 93, 17, 73, 83, 150, 23, 4], [90, 51, 48, 94]], ![[129, 44, 148, 26, 39, 97, 150, 39], [97, 33, 31, 50, 125, 92, 134, 104], [120, 109, 101, 30, 69, 91, 55, 55], [162, 93, 161, 154], [62, 124, 44, 132], [165, 161, 67, 96, 2, 128, 134, 20], [131, 134, 110, 47]], ![[104, 129, 60, 5, 135, 141, 147, 162], [5, 157, 73, 141, 166, 139, 113, 25], [108, 111, 75, 122, 70, 149, 14, 8], [43, 123, 26, 49], [128, 20, 66, 150], [143, 12, 39, 46, 79, 9, 94, 124], [29, 36, 154, 66]]]
 h' := ![![[26, 138, 156, 21, 39], [158, 111, 122, 80, 36], [57, 109, 42, 33, 99], [104, 83, 133, 114, 151], [86, 123, 34, 13, 156], [97, 57, 60, 164, 134], [0, 0, 1], [0, 1]], ![[1, 150, 103, 121, 42], [42, 147, 56, 136, 131], [47, 145, 68, 120, 32], [24, 47, 155, 110, 28], [6, 46, 1, 50, 19], [133, 41, 48, 149, 5], [53, 82, 63, 151, 85], [26, 138, 156, 21, 39]], ![[46, 66, 13, 100, 106], [76, 119, 83, 112, 25], [79, 24, 23, 65, 53], [133, 3, 67, 96, 70], [156, 163, 46, 149, 19], [120, 121, 99, 15, 143], [47, 23, 98, 28, 4], [1, 150, 103, 121, 42]], ![[61, 146, 62, 92, 147], [148, 125, 100, 29, 58], [157, 61, 122, 58, 8], [103, 158, 26, 3, 122], [134, 49, 108, 112, 133], [93, 124, 74, 120, 74], [127, 151, 157, 0, 120], [46, 66, 13, 100, 106]], ![[0, 1], [153, 166, 140, 144, 84], [49, 162, 79, 58, 142], [150, 43, 120, 11, 130], [133, 120, 145, 10, 7], [24, 158, 53, 53, 145], [21, 78, 15, 155, 125], [61, 146, 62, 92, 147]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65, 8, 89, 65], [], [], []]
 b := ![[], [37, 93, 83, 162, 54], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 5
  hpos := by decide
  P := [70, 110, 107, 3, 33, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-15677611610946, 2278824199630, 8446757774958, -23879418816278, -11523097563404]
  a := ![1, -6, 1, -7, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-93877913838, 13645653890, 50579387874, -142990531834, -69000584212]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 129891985607 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def PBC167 : ContainsPrimesAboveP 167 ![I167N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![167, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 167 (by decide) 𝕀

instance hp173 : Fact (Nat.Prime 173) := {out := by norm_num}

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-810569, 389939, 715578, -95602, -113996]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![-810569, 389939, 715578, -95602, -113996]] 
 ![![173, 0, 0, 0, 0], ![0, 173, 0, 0, 0], ![0, 0, 173, 0, 0], ![0, 0, 0, 173, 0], ![120, 157, 36, 69, 1]] where
  M :=![![![-810569, 389939, 715578, -95602, -113996], ![-1139960, 511777, 971082, -128000, -154416], ![-772080, 328017, 639777, -83414, -101584], ![62060, -49910, -74110, 10859, 11964], ![182820, -85445, -158982, 21130, 25311]]]
  hmulB := by decide  
  f := ![![![-837, 1439, -1200, -6, 196]], ![![1960, -3421, 2890, -60, -416]], ![![-2080, 3821, -3361, 334, 296]], ![![500, -1712, 2042, -1221, 580]], ![![960, -1974, 1880, -459, 43]]]
  g := ![![![74387, 105707, 27858, 44914, -113996], ![100520, 143093, 37746, 60848, -154416], ![66000, 94085, 24837, 40034, -101584], ![-7940, -11146, -2918, -4709, 11964], ![-16500, -23464, -6186, -9973, 25311]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 4 2 7 [103, 41, 158, 161, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [124, 85, 119, 157], [13, 45, 6, 162], [48, 42, 48, 27], [0, 1]]
 g := ![![[155, 171, 142, 56], [3, 32, 40], [87, 51, 57, 31], [76, 43, 131, 159], [27, 17, 23], [12, 1], []], ![[42, 146, 162, 22, 158, 88], [49, 87, 13], [104, 61, 168, 160, 160, 78], [99, 102, 29, 15, 126, 34], [35, 50, 21], [63, 146, 139, 85, 149, 100], [48, 129, 83]], ![[118, 24, 51, 88, 120, 171], [16, 118, 163], [98, 20, 40, 142, 164, 127], [0, 0, 62, 30, 143, 170], [62, 104, 57], [80, 26, 46, 10, 42, 68], [93, 109, 121]], ![[136, 97, 21, 63, 0, 26], [54, 9, 38], [58, 148, 75, 50, 23, 18], [159, 155, 140, 19, 88, 70], [105, 70, 152], [59, 106, 21, 92, 86, 146], [39, 95, 37]]]
 h' := ![![[124, 85, 119, 157], [51, 104, 115, 103], [35, 122, 123, 46], [130, 66, 33, 66], [93, 77, 144, 141], [148, 97, 139, 159], [0, 0, 1], [0, 1]], ![[13, 45, 6, 162], [119, 94, 48, 9], [144, 24, 143, 79], [19, 155, 130, 38], [59, 138, 113, 25], [107, 126, 119, 114], [52, 116, 91, 146], [124, 85, 119, 157]], ![[48, 42, 48, 27], [96, 17, 149, 105], [138, 12, 75, 110], [57, 69, 120, 86], [107, 103, 60, 4], [145, 160, 60, 24], [105, 143, 138, 120], [13, 45, 6, 162]], ![[0, 1], [104, 131, 34, 129], [86, 15, 5, 111], [157, 56, 63, 156], [11, 28, 29, 3], [10, 136, 28, 49], [17, 87, 116, 80], [48, 42, 48, 27]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [38, 38, 76], []]
 b := ![[], [], [45, 172, 63, 117], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 4
  hpos := by decide
  P := [103, 41, 158, 161, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3005427933839, 728022393843, -2894440467639, 5409629796635, 3804857273296]
  a := ![1, 25, -3, 24, 33]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2621834941397, -3448754737073, -808493076915, -1486274693993, 3804857273296]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 895745041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-837, 1439, -1200, -6, 196]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![-837, 1439, -1200, -6, 196]] 
 ![![173, 0, 0, 0, 0], ![72, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![29, 0, 0, 1, 0], ![121, 0, 0, 0, 1]] where
  M :=![![![-837, 1439, -1200, -6, 196], ![1960, -3421, 2890, -60, -416], ![-2080, 3821, -3361, 334, 296], ![500, -1712, 2042, -1221, 580], ![-820, 3487, -4392, 2958, -1445]]]
  hmulB := by decide  
  f := ![![![-810569, 389939, 715578, -95602, -113996]], ![![-343936, 165245, 303426, -40528, -48336]], ![![-18519, 8658, 16107, -2140, -2564]], ![![-135517, 65077, 119524, -15963, -19040]], ![![-565873, 272238, 499572, -66744, -79585]]]
  g := ![![![-719, 1439, -1200, -6, 196], ![1686, -3421, 2890, -60, -416], ![-1807, 3821, -3361, 334, 296], ![479, -1712, 2042, -1221, 580], ![-865, 3487, -4392, 2958, -1445]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![-810569, 389939, 715578, -95602, -113996]] ![![-837, 1439, -1200, -6, 196]]
  ![![173, 0, 0, 0, 0]] where
 M := ![![![173, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC173 : ContainsPrimesAboveP 173 ![I173N0, I173N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
    exact isPrimeI173N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 173 (by decide) (𝕀 ⊙ MulI173N0)
instance hp179 : Fact (Nat.Prime 179) := {out := by norm_num}

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-261, 312, -160, -196, 172]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![-261, 312, -160, -196, 172]] 
 ![![179, 0, 0, 0, 0], ![0, 179, 0, 0, 0], ![0, 0, 179, 0, 0], ![0, 0, 0, 179, 0], ![114, 160, 74, 28, 1]] where
  M :=![![![-261, 312, -160, -196, 172], ![1720, -2017, 1016, 1352, -1128], ![-5640, 6668, -3369, -4400, 3832], ![18300, -21308, 10560, 14547, -12068], ![-43000, 50604, -25400, -33800, 29095]]]
  hmulB := by decide  
  f := ![![![601, -136, -384, 44, 60]], ![![600, -115, -360, 40, 56]], ![![280, -36, -155, 16, 24]], ![![-180, 52, 128, -15, -20]], ![![1006, -196, -610, 68, 95]]]
  g := ![![![-111, -152, -72, -28, 172], ![728, 997, 472, 184, -1128], ![-2472, -3388, -1603, -624, 3832], ![7788, 10668, 5048, 1969, -12068], ![-18770, -25724, -12170, -4740, 29095]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 4 2 7 [135, 1, 131, 63, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [178, 130, 134, 162], [96, 83, 151, 114], [21, 144, 73, 82], [0, 1]]
 g := ![![[61, 41, 63, 116], [75, 68, 70, 45], [104, 94, 47], [82, 114, 1], [108, 126, 60, 155], [116, 1], []], ![[137, 0, 4, 149, 161, 11], [2, 127, 12, 83, 173, 131], [171, 15, 108], [24, 129, 1], [114, 75, 87, 116, 101, 132], [165, 169, 128, 45, 124, 140], [121, 149, 110]], ![[51, 125, 126, 114, 83, 92], [83, 166, 151, 67, 154, 113], [137, 80, 151], [9, 175, 66], [112, 58, 26, 59, 172, 162], [70, 103, 54, 176, 149, 130], [116, 58, 108]], ![[23, 122, 39, 45, 32, 68], [25, 4, 98, 71, 81, 51], [85, 16, 142], [61, 167, 125], [50, 29, 64, 112, 47, 88], [156, 67, 19, 53, 150, 22], [120, 60, 101]]]
 h' := ![![[178, 130, 134, 162], [78, 69, 73, 37], [4, 100, 41, 90], [145, 121, 175, 88], [98, 117, 178, 1], [92, 107, 18, 79], [0, 0, 1], [0, 1]], ![[96, 83, 151, 114], [174, 55, 85, 125], [123, 84, 176, 31], [98, 92, 4, 114], [37, 70, 96, 1], [44, 7, 72, 83], [134, 89, 102, 104], [178, 130, 134, 162]], ![[21, 144, 73, 82], [175, 131, 99, 81], [157, 164, 50, 166], [6, 45, 68, 35], [133, 87, 112, 148], [37, 166, 70, 23], [0, 114, 140, 78], [96, 83, 151, 114]], ![[0, 1], [60, 103, 101, 115], [106, 10, 91, 71], [150, 100, 111, 121], [35, 84, 151, 29], [17, 78, 19, 173], [172, 155, 115, 176], [21, 144, 73, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [15, 70, 81], []]
 b := ![[], [], [143, 72, 177, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 4
  hpos := by decide
  P := [135, 1, 131, 63, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-176977505057, 313319525586, -219476800992, -64178088186, 263918547936]
  a := ![-1, -7, 5, -5, -18]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-169070904859, -234154458906, -110332119264, -41641885086, 263918547936]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 1026625681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![601, -136, -384, 44, 60]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![601, -136, -384, 44, 60]] 
 ![![179, 0, 0, 0, 0], ![69, 1, 0, 0, 0], ![36, 0, 1, 0, 0], ![66, 0, 0, 1, 0], ![65, 0, 0, 0, 1]] where
  M :=![![![601, -136, -384, 44, 60], ![600, -115, -360, 40, 56], ![280, -36, -155, 16, 24], ![-180, 52, 128, -15, -20], ![-120, 28, 72, -8, -11]]]
  hmulB := by decide  
  f := ![![![-261, 312, -160, -196, 172]], ![![-91, 109, -56, -68, 60]], ![![-84, 100, -51, -64, 56]], ![![6, -4, 0, 9, -4]], ![![-335, 396, -200, -260, 225]]]
  g := ![![![95, -136, -384, 44, 60], ![85, -115, -360, 40, 56], ![32, -36, -155, 16, 24], ![-34, 52, 128, -15, -20], ![-19, 28, 72, -8, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![-261, 312, -160, -196, 172]] ![![601, -136, -384, 44, 60]]
  ![![179, 0, 0, 0, 0]] where
 M := ![![![179, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC179 : ContainsPrimesAboveP 179 ![I179N0, I179N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI179N0
    exact isPrimeI179N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 179 (by decide) (𝕀 ⊙ MulI179N0)
instance hp181 : Fact (Nat.Prime 181) := {out := by norm_num}

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![81, -132, 104, 12, -28]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![81, -132, 104, 12, -28]] 
 ![![181, 0, 0, 0, 0], ![0, 181, 0, 0, 0], ![0, 0, 181, 0, 0], ![4, 1, 61, 1, 0], ![57, 31, 100, 0, 1]] where
  M :=![![![81, -132, 104, 12, -28], ![-280, 405, -288, -104, 104], ![520, -752, 509, 232, -312], ![-1420, 1636, -840, -1079, 724], ![2920, -3768, 2176, 1920, -2011]]]
  hmulB := by decide  
  f := ![![![-3179, 468, 1784, -188, -276]], ![![-2760, 161, 1312, -120, -200]], ![![-1000, -144, 281, -8, -40]], ![![-416, -39, 137, -7, -20]], ![![-2023, 95, 940, -84, -143]]]
  g := ![![![9, 4, 12, 12, -28], ![-32, -15, -24, -104, 104], ![96, 48, 97, 232, -312], ![-212, -109, -41, -1079, 724], ![607, 313, 476, 1920, -2011]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [141, 21, 170, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [167, 141, 146], [25, 39, 35], [0, 1]]
 g := ![![[63, 56, 43], [33, 36], [85, 180, 166], [17, 42], [158, 109, 16], [100, 11, 1], []], ![[90, 98, 152, 61], [69, 154], [88, 57, 23, 175], [43, 111], [55, 54, 13, 51], [172, 50, 162, 160], [166, 139]], ![[7, 42, 137, 141], [158, 137], [93, 160, 79, 171], [52, 180], [113, 80, 71, 107], [155, 162, 2, 71], [96, 139]]]
 h' := ![![[167, 141, 146], [126, 107, 119], [142, 166, 175], [0, 163, 96], [166, 99, 59], [18, 150, 4], [0, 0, 1], [0, 1]], ![[25, 39, 35], [146, 50, 172], [61, 79, 110], [21, 6, 30], [103, 47, 103], [103, 79, 155], [139, 117, 39], [167, 141, 146]], ![[0, 1], [5, 24, 71], [127, 117, 77], [125, 12, 55], [6, 35, 19], [89, 133, 22], [121, 64, 141], [25, 39, 35]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38, 89], []]
 b := ![[], [137, 35, 137], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [141, 21, 170, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-199714259, 233793956, -116448362, -158083894, 134163932]
  a := ![0, -4, -2, -14, 12]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-39860347, -20813282, -21490188, -158083894, 134163932]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 5929741 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![206, -117, -194, 27, 31]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![206, -117, -194, 27, 31]] 
 ![![181, 0, 0, 0, 0], ![17, 1, 0, 0, 0], ![127, 0, 1, 0, 0], ![179, 0, 0, 1, 0], ![155, 0, 0, 0, 1]] where
  M :=![![![206, -117, -194, 27, 31], ![310, -151, -288, 38, 46], ![230, -112, -189, 26, 30], ![-5, 17, 6, -2, -1], ![-40, 12, 56, -6, -9]]]
  hmulB := by decide  
  f := ![![![86, -11, -46, 141, 71]], ![![12, -2, -6, 19, 9]], ![![72, -9, -39, 117, 59]], ![![129, -22, -64, 203, 96]], ![![120, -11, -70, 195, 102]]]
  g := ![![![95, -117, -194, 27, 31], ![141, -151, -288, 38, 46], ![93, -112, -189, 26, 30], ![-3, 17, 6, -2, -1], ![-27, 12, 56, -6, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1

def I181N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-66, 19, 46, -5, -7]] i)))

def SI181N2: IdealEqSpanCertificate' Table ![![-66, 19, 46, -5, -7]] 
 ![![181, 0, 0, 0, 0], ![42, 1, 0, 0, 0], ![23, 0, 1, 0, 0], ![39, 0, 0, 1, 0], ![14, 0, 0, 0, 1]] where
  M :=![![![-66, 19, 46, -5, -7], ![-70, 19, 48, -2, -6], ![-30, 8, 21, 10, 2], ![45, -11, -26, 44, 21], ![50, -10, -28, 56, 27]]]
  hmulB := by decide  
  f := ![![![-746, 1325, -1150, -19, 201]], ![![-162, 289, -252, -4, 44]], ![![-108, 191, -165, -3, 29]], ![![-149, 266, -232, -3, 40]], ![![-84, 146, -124, -4, 23]]]
  g := ![![![-9, 19, 46, -5, -7], ![-10, 19, 48, -2, -6], ![-7, 8, 21, 10, 2], ![-5, -11, -26, 44, 21], ![-8, -10, -28, 56, 27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N2 : Nat.card (O ⧸ I181N2) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N2)

lemma isPrimeI181N2 : Ideal.IsPrime I181N2 := prime_ideal_of_norm_prime hp181.out _ NI181N2
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![81, -132, 104, 12, -28]] ![![206, -117, -194, 27, 31]]
  ![![746, -1325, 1150, 19, -201]] where
 M := ![![![746, -1325, 1150, 19, -201]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI181N1 : IdealMulLeCertificate' Table 
  ![![746, -1325, 1150, 19, -201]] ![![-66, 19, 46, -5, -7]]
  ![![181, 0, 0, 0, 0]] where
 M := ![![![-181, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC181 : ContainsPrimesAboveP 181 ![I181N0, I181N1, I181N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
    exact isPrimeI181N1
    exact isPrimeI181N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 181 (by decide) (𝕀 ⊙ MulI181N0 ⊙ MulI181N1)
instance hp191 : Fact (Nat.Prime 191) := {out := by norm_num}

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19276, 3629, 9472, -28757, -13073]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![-19276, 3629, 9472, -28757, -13073]] 
 ![![191, 0, 0, 0, 0], ![0, 191, 0, 0, 0], ![117, 13, 1, 0, 0], ![7, 81, 0, 1, 0], ![187, 158, 0, 0, 1]] where
  M :=![![![-19276, 3629, 9472, -28757, -13073], ![-130730, 24193, 64772, -195446, -88882], ![-444410, 82662, 219639, -663966, -302010], ![-1444685, 268587, 714242, -2158664, -981481], ![-1888200, 350590, 933938, -2821582, -1283747]]]
  hmulB := by decide  
  f := ![![![-927876, -8259, 381092, -29349, -57195]], ![![-571950, -205117, 42180, 17146, -3006]], ![![-607392, -20262, 235151, -16595, -35045]], ![![-274087, -87841, 30286, 6375, -3126]], ![![-1380742, -177685, 407730, -14537, -58444]]]
  g := ![![![7950, 22384, 9472, -28757, -13073], ![53822, 152129, 64772, -195446, -88882], ![183149, 516891, 219639, -663966, -302010], ![594956, 1680153, 714242, -2158664, -981481], ![778287, 2196804, 933938, -2821582, -1283747]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [3, 133, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [58, 190], [0, 1]]
 g := ![![[108, 64], [91, 128], [45, 153], [27, 79], [92, 184], [135, 117], [1]], ![[0, 127], [66, 63], [133, 38], [25, 112], [68, 7], [45, 74], [1]]]
 h' := ![![[58, 190], [109, 8], [56, 117], [110, 150], [106, 156], [168, 39], [188, 58], [0, 1]], ![[0, 1], [0, 183], [157, 74], [24, 41], [177, 35], [138, 152], [114, 133], [58, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [80]]
 b := ![[], [177, 40]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [3, 133, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3634, 26058, -25196, 9385, 29881]
  a := ![13, -7, 4, -6, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-14184, -26847, -25196, 9385, 29881]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![34, -40, 20, 27, -23]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![34, -40, 20, 27, -23]] 
 ![![191, 0, 0, 0, 0], ![37, 1, 0, 0, 0], ![175, 0, 1, 0, 0], ![182, 0, 0, 1, 0], ![109, 0, 0, 0, 1]] where
  M :=![![![34, -40, 20, 27, -23], ![-230, 269, -134, -182, 154], ![770, -903, 451, 608, -518], ![-2475, 2897, -1444, -1958, 1657], ![5880, -6893, 3442, 4644, -3951]]]
  hmulB := by decide  
  f := ![![![-706, -694, -514, 111, 91]], ![![-132, -143, -108, 23, 19]], ![![-640, -641, -481, 103, 85]], ![![-667, -663, -492, 106, 87]], ![![-404, -393, -294, 63, 52]]]
  g := ![![![-23, -40, 20, 27, -23], ![155, 269, -134, -182, 154], ![-518, -903, 451, 608, -518], ![1669, 2897, -1444, -1958, 1657], ![-3958, -6893, 3442, 4644, -3951]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1

def I191N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-270356, -34845, 79784, -2837, -11435]] i)))

def SI191N2: IdealEqSpanCertificate' Table ![![-270356, -34845, 79784, -2837, -11435]] 
 ![![191, 0, 0, 0, 0], ![58, 1, 0, 0, 0], ![37, 0, 1, 0, 0], ![44, 0, 0, 1, 0], ![189, 0, 0, 0, 1]] where
  M :=![![![-270356, -34845, 79784, -2837, -11435], ![-114350, -116201, -64016, 16674, 11522], ![57610, -112836, -132875, 21790, 21826], ![166305, -34133, -102618, 11534, 15993], ![42810, 12450, -5954, -772, 693]]]
  hmulB := by decide  
  f := ![![![10364, -12365, 6764, 7307, -5065]], ![![2882, -3403, 1848, 2048, -1332]], ![![3038, -3523, 1833, 2275, -1529]], ![![-219, 529, -326, -136, 997]], ![![17616, -20483, 10598, 13295, -9372]]]
  g := ![![![5679, -34845, 79784, -2837, -11435], ![31846, -116201, -64016, 16674, 11522], ![33689, -112836, -132875, 21790, 21826], ![12632, -34133, -102618, 11534, 15993], ![-2911, 12450, -5954, -772, 693]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N2 : Nat.card (O ⧸ I191N2) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N2)

lemma isPrimeI191N2 : Ideal.IsPrime I191N2 := prime_ideal_of_norm_prime hp191.out _ NI191N2

def I191N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6, -28, 18, 1, -3]] i)))

def SI191N3: IdealEqSpanCertificate' Table ![![-6, -28, 18, 1, -3]] 
 ![![191, 0, 0, 0, 0], ![70, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![147, 0, 0, 1, 0], ![105, 0, 0, 0, 1]] where
  M :=![![![-6, -28, 18, 1, -3], ![-30, 35, -58, 2, 10], ![50, -77, 33, 4, -6], ![-15, 49, -52, 0, 9], ![70, -113, 96, 2, -17]]]
  hmulB := by decide  
  f := ![![![174, -38, -84, 269, 119]], ![![70, -15, -34, 108, 48]], ![![52, -11, -25, 79, 35]], ![![203, -41, -100, 311, 140]], ![![190, -41, -90, 287, 126]]]
  g := ![![![8, -28, 18, 1, -3], ![-10, 35, -58, 2, 10], ![23, -77, 33, 4, -6], ![-14, 49, -52, 0, 9], ![33, -113, 96, 2, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N3 : Nat.card (O ⧸ I191N3) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N3)

lemma isPrimeI191N3 : Ideal.IsPrime I191N3 := prime_ideal_of_norm_prime hp191.out _ NI191N3
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![-19276, 3629, 9472, -28757, -13073]] ![![34, -40, 20, 27, -23]]
  ![![107721, -2815, -72092, 173240, 96792]] where
 M := ![![![107721, -2815, -72092, 173240, 96792]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI191N1 : IdealMulLeCertificate' Table 
  ![![107721, -2815, -72092, 173240, 96792]] ![![-270356, -34845, 79784, -2837, -11435]]
  ![![174, -38, -84, 269, 119]] where
 M := ![![![174, -38, -84, 269, 119]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI191N2 : IdealMulLeCertificate' Table 
  ![![174, -38, -84, 269, 119]] ![![-6, -28, 18, 1, -3]]
  ![![191, 0, 0, 0, 0]] where
 M := ![![![191, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC191 : ContainsPrimesAboveP 191 ![I191N0, I191N1, I191N2, I191N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI191N0
    exact isPrimeI191N1
    exact isPrimeI191N2
    exact isPrimeI191N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 191 (by decide) (𝕀 ⊙ MulI191N0 ⊙ MulI191N1 ⊙ MulI191N2)
instance hp193 : Fact (Nat.Prime 193) := {out := by norm_num}

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-49404, 84208, -69702, -1389, 12135]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![-49404, 84208, -69702, -1389, 12135]] 
 ![![193, 0, 0, 0, 0], ![0, 193, 0, 0, 0], ![0, 0, 193, 0, 0], ![0, 0, 0, 193, 0], ![32, 94, 154, 82, 1]] where
  M :=![![![-49404, 84208, -69702, -1389, 12135], ![121350, -206829, 171194, 3438, -29826], ![-149130, 254101, -210267, -4324, 36702], ![122835, -209065, 172828, 3902, -30437], ![-272750, 464129, -383628, -8778, 67603]]]
  hmulB := by decide  
  f := ![![![2468, -790, -1796, 221, 283]], ![![2830, -867, -2022, 246, 318]], ![![1590, -463, -1113, 132, 174]], ![![-545, 195, 416, -60, -69]], ![![2822, -839, -1992, 236, 311]]]
  g := ![![![-2268, -5474, -10044, -5163, 12135], ![5574, 13455, 24686, 12690, -29826], ![-6858, -16559, -30375, -15616, 36702], ![5683, 13741, 25182, 12952, -30437], ![-12622, -30521, -55930, -28768, 67603]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 4 2 7 [37, 54, 188, 165, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [56, 133, 71, 72], [154, 101, 57, 139], [11, 151, 65, 175], [0, 1]]
 g := ![![[35, 161, 102, 138], [116, 88, 62], [41, 12, 138], [68, 74, 181], [45, 161, 96], [17, 28, 1], []], ![[135, 120, 151, 164, 181, 147], [111, 72, 186], [4, 15, 124], [143, 119, 162], [94, 172, 134], [2, 88, 55], [55, 114, 22, 67, 33, 179]], ![[32, 142, 83, 26, 62, 67], [135, 67, 107], [16, 24, 139], [136, 148, 32], [191, 24, 62], [95, 71, 24], [58, 150, 120, 177, 17, 24]], ![[95, 186, 189, 69, 54, 100], [150, 53, 64], [54, 82, 86], [145, 161, 168], [7, 58, 137], [18, 158, 134], [129, 192, 123, 128, 51, 151]]]
 h' := ![![[56, 133, 71, 72], [35, 127, 189, 36], [9, 32, 152, 86], [102, 34, 150, 157], [63, 189, 48, 145], [143, 169, 80, 176], [0, 0, 0, 1], [0, 1]], ![[154, 101, 57, 139], [125, 111, 121, 103], [76, 158, 112, 46], [113, 34, 67, 160], [0, 112, 139, 82], [191, 7, 104, 83], [74, 191, 186, 21], [56, 133, 71, 72]], ![[11, 151, 65, 175], [191, 32, 178, 175], [19, 70, 98, 53], [178, 158, 173, 116], [81, 123, 115, 178], [134, 151, 8, 86], [102, 175, 24, 88], [154, 101, 57, 139]], ![[0, 1], [130, 116, 91, 72], [58, 126, 24, 8], [60, 160, 189, 146], [139, 155, 84, 174], [165, 59, 1, 41], [32, 20, 176, 83], [11, 151, 65, 175]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [9, 51, 60], []]
 b := ![[], [], [58, 71, 27, 44], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 4
  hpos := by decide
  P := [37, 54, 188, 165, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1426809288, 1674075520, -836793530, -1125900961, 960825879]
  a := ![-1, -1, -1, -2, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-166700712, -459293042, -771005072, -414060223, 960825879]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 1387488001 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2468, -790, -1796, 221, 283]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![2468, -790, -1796, 221, 283]] 
 ![![193, 0, 0, 0, 0], ![60, 1, 0, 0, 0], ![130, 0, 1, 0, 0], ![123, 0, 0, 1, 0], ![155, 0, 0, 0, 1]] where
  M :=![![![2468, -790, -1796, 221, 283], ![2830, -867, -2022, 246, 318], ![1590, -463, -1113, 132, 174], ![-545, 195, 416, -60, -69], ![-520, 163, 374, -56, -63]]]
  hmulB := by decide  
  f := ![![![-49404, 84208, -69702, -1389, 12135]], ![![-14730, 25107, -20782, -414, 3618]], ![![-34050, 58037, -48039, -958, 8364]], ![![-30849, 52583, -43526, -865, 7576]], ![![-41090, 70033, -57966, -1161, 10096]]]
  g := ![![![1100, -790, -1796, 221, 283], ![1234, -867, -2022, 246, 318], ![678, -463, -1113, 132, 174], ![-250, 195, 416, -60, -69], ![-219, 163, 374, -56, -63]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![-49404, 84208, -69702, -1389, 12135]] ![![2468, -790, -1796, 221, 283]]
  ![![193, 0, 0, 0, 0]] where
 M := ![![![193, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC193 : ContainsPrimesAboveP 193 ![I193N0, I193N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI193N0
    exact isPrimeI193N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 193 (by decide) (𝕀 ⊙ MulI193N0)
instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4319, 286, -3496, 7496, 3624]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![4319, 286, -3496, 7496, 3624]] 
 ![![197, 0, 0, 0, 0], ![0, 197, 0, 0, 0], ![0, 0, 197, 0, 0], ![0, 0, 0, 197, 0], ![68, 135, 36, 86, 1]] where
  M :=![![![4319, 286, -3496, 7496, 3624], ![36240, -9553, -14420, 51488, 22736], ![113680, -17178, -61041, 173484, 80240], ![383080, -76260, -183452, 568139, 255360], ![485580, -78586, -253784, 735352, 341531]]]
  hmulB := by decide  
  f := ![![![-115237, 46266, 92896, -11976, -14728]], ![![-147280, 56803, 116484, -14896, -18448]], ![![-92240, 34274, 71699, -9100, -11344]], ![![16920, -8068, -14868, 1983, 2368]], ![![-150048, 57587, 118400, -15126, -18749]]]
  g := ![![![-1229, -2482, -680, -1544, 3624], ![-7664, -15629, -4228, -9664, 22736], ![-27120, -55074, -14973, -34148, 80240], ![-86200, -175380, -47596, -108593, 255360], ![-115424, -234443, -63700, -145362, 341531]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 4 2 7 [79, 181, 28, 71, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [93, 87, 116, 101], [190, 154, 15, 39], [40, 152, 66, 57], [0, 1]]
 g := ![![[126, 87, 96, 187], [132, 69, 109], [157, 27, 191, 191], [15, 59, 121], [130, 37, 23], [88, 126, 1], []], ![[126, 23, 114, 37, 193, 88], [45, 154, 85], [129, 137, 150, 183, 135, 105], [171, 12, 182], [190, 2, 157], [163, 109, 104], [10, 4, 192, 81, 56, 188]], ![[83, 157, 196, 62, 99, 90], [9, 69, 24], [105, 189, 8, 111, 70, 43], [40, 24, 4], [124, 184, 135], [185, 185, 6], [48, 19, 108, 94, 100, 22]], ![[130, 120, 194, 111, 75, 189], [49, 78, 175], [6, 164, 172, 88, 35, 82], [147, 116, 28], [31, 128, 100], [80, 118, 144], [190, 13, 70, 93, 159, 13]]]
 h' := ![![[93, 87, 116, 101], [77, 179, 184, 160], [8, 146, 32, 122], [113, 169, 164, 114], [71, 24, 162, 186], [140, 122, 64, 90], [0, 0, 0, 1], [0, 1]], ![[190, 154, 15, 39], [137, 94, 192, 161], [46, 134, 6, 171], [45, 51, 113, 47], [143, 131, 15, 24], [141, 160, 74, 74], [4, 7, 176, 164], [93, 87, 116, 101]], ![[40, 152, 66, 57], [18, 87, 115, 184], [170, 119, 0, 40], [134, 57, 93, 42], [158, 16, 77, 2], [164, 120, 131, 23], [2, 38, 99, 20], [190, 154, 15, 39]], ![[0, 1], [122, 34, 100, 86], [168, 192, 159, 61], [171, 117, 24, 191], [84, 26, 140, 182], [13, 189, 125, 10], [134, 152, 119, 12], [40, 152, 66, 57]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [109, 114, 168], []]
 b := ![[], [], [48, 4, 151, 26], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 4
  hpos := by decide
  P := [79, 181, 28, 71, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-231535158748, 290270295459, -156167369406, -169404776647, 181386410370]
  a := ![3, 3, 0, -1, 14]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-63785842964, -122826878703, -33939482958, -80043837911, 181386410370]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 1506138481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![115237, -46266, -92896, 11976, 14728]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![115237, -46266, -92896, 11976, 14728]] 
 ![![197, 0, 0, 0, 0], ![52, 1, 0, 0, 0], ![27, 0, 1, 0, 0], ![60, 0, 0, 1, 0], ![64, 0, 0, 0, 1]] where
  M :=![![![115237, -46266, -92896, 11976, 14728], ![147280, -56803, -116484, 14896, 18448], ![92240, -34274, -71699, 9100, 11344], ![-16920, 8068, 14868, -1983, -2368], ![-24980, 9870, 19984, -2568, -3167]]]
  hmulB := by decide  
  f := ![![![-4319, -286, 3496, -7496, -3624]], ![![-1324, -27, 996, -2240, -1072]], ![![-1169, 48, 789, -1908, -904]], ![![-3260, 300, 1996, -5167, -2400]], ![![-3868, 306, 2424, -6168, -2911]]]
  g := ![![![17097, -46266, -92896, 11976, 14728], ![21176, -56803, -116484, 14896, 18448], ![12885, -34274, -71699, 9100, 11344], ![-2880, 8068, 14868, -1983, -2368], ![-3660, 9870, 19984, -2568, -3167]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![4319, 286, -3496, 7496, 3624]] ![![115237, -46266, -92896, 11976, 14728]]
  ![![197, 0, 0, 0, 0]] where
 M := ![![![-197, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC197 : ContainsPrimesAboveP 197 ![I197N0, I197N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
    exact isPrimeI197N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 197 (by decide) (𝕀 ⊙ MulI197N0)


lemma PB1640I4_primes (p : ℕ) :
  p ∈ Set.range ![157, 163, 167, 173, 179, 181, 191, 193, 197] ↔ Nat.Prime p ∧ 151 < p ∧ p ≤ 197 := by
  rw [← List.mem_ofFn']
  convert primes_range 151 197 (by omega)

def PB1640I4 : PrimesBelowBoundCertificateInterval O 151 197 1640 where
  m := 9
  g := ![2, 3, 1, 2, 2, 3, 4, 2, 2]
  P := ![157, 163, 167, 173, 179, 181, 191, 193, 197]
  hP := PB1640I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1, I163N2]
    · exact ![I167N0]
    · exact ![I173N0, I173N1]
    · exact ![I179N0, I179N1]
    · exact ![I181N0, I181N1, I181N2]
    · exact ![I191N0, I191N1, I191N2, I191N3]
    · exact ![I193N0, I193N1]
    · exact ![I197N0, I197N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC157
    · exact PBC163
    · exact PBC167
    · exact PBC173
    · exact PBC179
    · exact PBC181
    · exact PBC191
    · exact PBC193
    · exact PBC197
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![607573201, 157]
    · exact ![4330747, 163, 163]
    · exact ![129891985607]
    · exact ![895745041, 173]
    · exact ![1026625681, 179]
    · exact ![5929741, 181, 181]
    · exact ![36481, 191, 191, 191]
    · exact ![1387488001, 193]
    · exact ![1506138481, 197]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
      exact NI157N1
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
      exact NI163N1
      exact NI163N2
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
      exact NI173N1
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
      exact NI179N1
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
      exact NI181N2
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
      exact NI191N2
      exact NI191N3
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
      exact NI197N1
  β := ![I157N1, I163N1, I163N2, I173N1, I179N1, I181N1, I181N2, I191N1, I191N2, I191N3, I193N1, I197N1]
  Il := ![[I157N1], [I163N1, I163N2], [], [I173N1], [I179N1], [I181N1, I181N2], [I191N1, I191N2, I191N3], [I193N1], [I197N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
