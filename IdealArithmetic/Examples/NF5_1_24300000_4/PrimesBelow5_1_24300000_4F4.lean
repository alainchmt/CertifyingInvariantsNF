
import IdealArithmetic.Examples.NF5_1_24300000_4.RI5_1_24300000_4
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-315, 300, -292, 138, 24]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![-315, 300, -292, 138, 24]] 
 ![![157, 0, 0, 0, 0], ![0, 157, 0, 0, 0], ![54, 5, 1, 0, 0], ![22, 15, 0, 1, 0], ![66, 131, 0, 0, 1]] where
  M :=![![![-315, 300, -292, 138, 24], ![96, -445, 348, -536, 276], ![1104, 184, 107, 1248, -1072], ![-2192, 916, -1154, -697, 1110], ![2172, -1244, 1394, 224, -835]]]
  hmulB := by decide  
  f := ![![![-7031, -8876, -6480, -7862, -5268]], ![![-21072, -26641, -19412, -23496, -15724]], ![![-3490, -4409, -3217, -3900, -2612]], ![![-3530, -4463, -3254, -3941, -2638]], ![![-21266, -26883, -19594, -23724, -15879]]]
  g := ![![![69, -22, -292, 138, 24], ![-160, -193, 348, -536, 276], ![246, 773, 107, 1248, -1072], ![14, -817, -1154, -697, 1110], ![-146, 623, 1394, 224, -835]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [100, 93, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [64, 156], [0, 1]]
 g := ![![[81, 11], [76], [90, 145], [41, 67], [17, 156], [14], [1]], ![[0, 146], [76], [107, 12], [90, 90], [110, 1], [14], [1]]]
 h' := ![![[64, 156], [25, 110], [106, 62], [139, 107], [27, 58], [122, 28], [57, 64], [0, 1]], ![[0, 1], [0, 47], [149, 95], [79, 50], [128, 99], [30, 129], [71, 93], [64, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [96]]
 b := ![[], [34, 48]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [100, 93, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2250, 1828, 1569, 2078, 289]
  a := ![0, -8, -3, -4, -11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-938, -478, 1569, 2078, 289]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1701, -2353, -1876, -2406, -1617]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![-1701, -2353, -1876, -2406, -1617]] 
 ![![157, 0, 0, 0, 0], ![0, 157, 0, 0, 0], ![45, 125, 1, 0, 0], ![92, 139, 0, 1, 0], ![91, 151, 0, 0, 1]] where
  M :=![![![-1701, -2353, -1876, -2406, -1617], ![-6468, -7600, -5587, -6986, -4812], ![-19248, -23853, -17224, -20798, -13972], ![-24710, -31821, -23105, -27703, -18392], ![-33550, -43155, -31509, -38004, -25297]]]
  hmulB := by decide  
  f := ![![![-21087, -837, -3998, -20180, 18387]], ![![73548, -26878, 35937, 28778, -40360]], ![![51485, -21016, 26781, 17072, -26497]], ![![53258, -24903, 30038, 13243, -24886]], ![![58425, -25888, 31896, 16526, -28442]]]
  g := ![![![2874, 5164, -1876, -2406, -1617], ![8443, 15213, -5587, -6986, -4812], ![25100, 45413, -17224, -20798, -13972], ![33359, 60409, -23105, -27703, -18392], ![45750, 82789, -31509, -38004, -25297]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P1 : CertificateIrreducibleZModOfList' 157 2 2 7 [21, 54, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [103, 156], [0, 1]]
 g := ![![[25, 68], [105], [107, 52], [33, 105], [65, 120], [90], [1]], ![[121, 89], [105], [125, 105], [15, 52], [22, 37], [90], [1]]]
 h' := ![![[103, 156], [39, 142], [108, 24], [92, 44], [48, 133], [121, 77], [136, 103], [0, 1]], ![[0, 1], [64, 15], [68, 133], [71, 113], [88, 24], [45, 80], [69, 54], [103, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [104]]
 b := ![[], [148, 52]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N1 : CertifiedPrimeIdeal' SI157N1 157 where
  n := 2
  hpos := by decide
  P := [21, 54, 1]
  hirr := P157P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10470, 33534, -1035, 10951, 25639]
  a := ![3, -61, 2, -65, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-21048, -33317, -1035, 10951, 25639]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N1 B_one_repr
lemma NI157N1 : Nat.card (O ⧸ I157N1) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N1

def I157N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, 9, -8, 6, -1]] i)))

def SI157N2: IdealEqSpanCertificate' Table ![![-7, 9, -8, 6, -1]] 
 ![![157, 0, 0, 0, 0], ![27, 1, 0, 0, 0], ![56, 0, 1, 0, 0], ![94, 0, 0, 1, 0], ![52, 0, 0, 0, 1]] where
  M :=![![![-7, 9, -8, 6, -1], ![-4, -10, 7, -18, 12], ![48, -3, 14, 38, -36], ![-70, 37, -41, -13, 32], ![66, -41, 47, 0, -19]]]
  hmulB := by decide  
  f := ![![![651, -747, -458, -4, 355]], ![![121, -125, -79, -2, 61]], ![![232, -259, -160, -2, 124]], ![![380, -449, -273, -1, 212]], ![![210, -253, -153, 0, 119]]]
  g := ![![![-2, 9, -8, 6, -1], ![6, -10, 7, -18, 12], ![-15, -3, 14, 38, -36], ![5, 37, -41, -13, 32], ![-3, -41, 47, 0, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N2 : Nat.card (O ⧸ I157N2) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N2)

lemma isPrimeI157N2 : Ideal.IsPrime I157N2 := prime_ideal_of_norm_prime hp157.out _ NI157N2
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![-315, 300, -292, 138, 24]] ![![-1701, -2353, -1876, -2406, -1617]]
  ![![651, -747, -458, -4, 355]] where
 M := ![![![651, -747, -458, -4, 355]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI157N1 : IdealMulLeCertificate' Table 
  ![![651, -747, -458, -4, 355]] ![![-7, 9, -8, 6, -1]]
  ![![157, 0, 0, 0, 0]] where
 M := ![![![157, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC157 : ContainsPrimesAboveP 157 ![I157N0, I157N1, I157N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
    exact isPrimeI157N1
    exact isPrimeI157N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 157 (by decide) (𝕀 ⊙ MulI157N0 ⊙ MulI157N1)
instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-12609, -2054, 1527, 1502, -995]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![-12609, -2054, 1527, 1502, -995]] 
 ![![163, 0, 0, 0, 0], ![0, 163, 0, 0, 0], ![0, 0, 163, 0, 0], ![0, 0, 0, 163, 0], ![13, 140, 54, 113, 1]] where
  M :=![![![-12609, -2054, 1527, 1502, -995], ![-3980, -10575, -4044, 1064, 3004], ![12016, -3956, -4567, -2080, 2128], ![6246, 9036, 2172, -2971, -3582], ![-5174, 6220, 2958, -1942, -4473]]]
  hmulB := by decide  
  f := ![![![523, -670, 609, -464, 95]], ![![380, 763, -480, 1408, -928]], ![![-3712, 380, -1093, -2816, 2816]], ![![5442, -2784, 3246, 1019, -2352]], ![![2881, -1182, 1503, 947, -1478]]]
  g := ![![![2, 842, 339, 699, -995], ![-264, -2645, -1020, -2076, 3004], ![-96, -1852, -733, -1488, 2128], ![324, 3132, 1200, 2465, -3582], ![325, 3880, 1500, 3089, -4473]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 4 2 7 [12, 83, 15, 25, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [150, 83, 81, 47], [58, 76, 136, 9], [93, 3, 109, 107], [0, 1]]
 g := ![![[69, 111, 52, 85], [112, 143, 63, 1], [74, 147, 88], [148, 150, 38], [63, 158, 134], [138, 1], []], ![[75, 36, 113, 38, 97, 83], [135, 79, 30, 40, 162, 58], [22, 72, 65], [100, 44, 53], [61, 78, 10], [40, 110, 32, 69, 2, 10], [22, 148, 90]], ![[106, 16, 12, 14, 97, 33], [125, 36, 55, 72, 144, 14], [132, 161, 90], [36, 16, 56], [102, 93, 135], [145, 133, 114, 116, 38, 158], [87, 97, 81]], ![[110, 42, 23, 19, 54, 12], [124, 113, 144, 98, 33, 106], [134, 45, 152], [128, 75, 121], [134, 99, 100], [123, 120, 11, 30, 128, 159], [28, 20, 39]]]
 h' := ![![[150, 83, 81, 47], [123, 130, 124, 133], [104, 20, 119, 162], [60, 9, 154, 96], [83, 25, 158, 53], [137, 107, 129, 121], [0, 0, 1], [0, 1]], ![[58, 76, 136, 9], [106, 162, 140, 30], [66, 128, 98, 9], [161, 29, 85, 126], [63, 69, 14, 78], [44, 106, 156, 93], [68, 108, 54, 28], [150, 83, 81, 47]], ![[93, 3, 109, 107], [98, 100, 115, 59], [101, 52, 150, 20], [113, 1, 69, 47], [120, 90, 43, 43], [23, 26, 17, 102], [38, 105, 140, 116], [58, 76, 136, 9]], ![[0, 1], [41, 97, 110, 104], [113, 126, 122, 135], [108, 124, 18, 57], [103, 142, 111, 152], [154, 87, 24, 10], [0, 113, 131, 19], [93, 3, 109, 107]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [109, 65, 86], []]
 b := ![[], [], [14, 12, 15, 81], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 4
  hpos := by decide
  P := [12, 83, 15, 25, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11036200, 14022624, 10214814, 12343922, 8296584]
  a := ![1, -6, -1, -5, -4]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-593984, -7039872, -2685894, -5675890, 8296584]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 705911761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-523, 670, -609, 464, -95]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![-523, 670, -609, 464, -95]] 
 ![![163, 0, 0, 0, 0], ![100, 1, 0, 0, 0], ![106, 0, 1, 0, 0], ![29, 0, 0, 1, 0], ![130, 0, 0, 0, 1]] where
  M :=![![![-523, 670, -609, 464, -95], ![-380, -763, 480, -1408, 928], ![3712, -380, 1093, 2816, -2816], ![-5442, 2784, -3246, -1019, 2352], ![4894, -3296, 3504, -190, -1483]]]
  hmulB := by decide  
  f := ![![![12609, 2054, -1527, -1502, 995]], ![![7760, 1325, -912, -928, 592]], ![![8126, 1360, -965, -964, 634]], ![![2205, 310, -285, -249, 199]], ![![10088, 1600, -1236, -1186, 821]]]
  g := ![![![-25, 670, -609, 464, -95], ![-336, -763, 480, -1408, 928], ![1290, -380, 1093, 2816, -2816], ![-1325, 2784, -3246, -1019, 2352], ![990, -3296, 3504, -190, -1483]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![-12609, -2054, 1527, 1502, -995]] ![![-523, 670, -609, 464, -95]]
  ![![163, 0, 0, 0, 0]] where
 M := ![![![-163, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC163 : ContainsPrimesAboveP 163 ![I163N0, I163N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
    exact isPrimeI163N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 163 (by decide) (𝕀 ⊙ MulI163N0)
instance hp167 : Fact (Nat.Prime 167) := {out := by norm_num}

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, -73, 69, -58, 16]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![43, -73, 69, -58, 16]] 
 ![![167, 0, 0, 0, 0], ![0, 167, 0, 0, 0], ![0, 0, 167, 0, 0], ![0, 0, 0, 167, 0], ![34, 152, 140, 59, 1]] where
  M :=![![![43, -73, 69, -58, 16], ![64, 70, -41, 170, -116], ![-464, 77, -162, -314, 340], ![648, -335, 399, 93, -256], ![-544, 407, -403, 58, 151]]]
  hmulB := by decide  
  f := ![![![-11, -3, 1, 2, 0]], ![![0, -8, -3, 2, 4]], ![![16, 3, 0, 2, 4]], ![![8, 15, 7, 3, 0]], ![![14, 0, 0, 5, 7]]]
  g := ![![![-3, -15, -13, -6, 16], ![24, 106, 97, 42, -116], ![-72, -309, -286, -122, 340], ![56, 231, 217, 91, -256], ![-34, -135, -129, -53, 151]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 4 2 7 [149, 78, 39, 48, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 76, 148, 164], [101, 117, 103, 81], [151, 140, 83, 89], [0, 1]]
 g := ![![[39, 6, 64, 62], [37, 116, 13, 27], [139, 54, 65, 96], [22, 32, 38], [40, 151, 152], [119, 1], []], ![[35, 153, 137, 108, 141, 17], [13, 58, 29, 81, 64, 119], [105, 163, 85, 69, 29, 131], [27, 111, 128], [142, 107, 4], [91, 77, 1, 25, 67, 5], [122, 16, 9]], ![[86, 14, 147, 164, 158, 58], [29, 0, 126, 66, 11, 62], [58, 96, 72, 160, 10, 28], [3, 147, 33], [3, 54, 58], [21, 59, 33, 14, 108, 7], [11, 20, 48]], ![[114, 135, 59, 68, 92, 25], [26, 19, 156, 154, 38, 50], [104, 128, 155, 138, 52, 162], [88, 30, 107], [79, 151, 93], [105, 143, 80, 15, 99, 7], [97, 129, 72]]]
 h' := ![![[34, 76, 148, 164], [165, 46, 78, 88], [164, 31, 93, 148], [86, 108, 54, 51], [58, 5, 137, 47], [138, 88, 124, 94], [0, 0, 1], [0, 1]], ![[101, 117, 103, 81], [3, 142, 43, 102], [28, 67, 25, 4], [66, 163, 149, 124], [158, 87, 10, 104], [21, 41, 134, 165], [12, 115, 143, 80], [34, 76, 148, 164]], ![[151, 140, 83, 89], [7, 86, 91, 113], [147, 74, 68, 84], [138, 103, 58, 16], [90, 105, 143, 37], [161, 11, 128, 15], [45, 90, 137, 8], [101, 117, 103, 81]], ![[0, 1], [62, 60, 122, 31], [103, 162, 148, 98], [11, 127, 73, 143], [40, 137, 44, 146], [156, 27, 115, 60], [165, 129, 53, 79], [151, 140, 83, 89]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [75, 12, 46], []]
 b := ![[], [], [144, 50, 103, 152], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 4
  hpos := by decide
  P := [149, 78, 39, 48, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3016695637, 3827868412, 2787377482, 3375089122, 2258511432]
  a := ![1, 26, 4, 18, 15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-441752653, -2032729756, -1876671994, -777707098, 2258511432]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 777796321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 3, -1, -2, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![11, 3, -1, -2, 0]] 
 ![![167, 0, 0, 0, 0], ![49, 1, 0, 0, 0], ![104, 0, 1, 0, 0], ![16, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![11, 3, -1, -2, 0], ![0, 8, 3, -2, -4], ![-16, -3, 0, -2, -4], ![-8, -15, -7, -3, 0], ![0, -13, -9, -6, -1]]]
  hmulB := by decide  
  f := ![![![-43, 73, -69, 58, -16]], ![![-13, 21, -20, 16, -4]], ![![-24, 45, -42, 38, -12]], ![![-8, 9, -9, 5, 0]], ![![3, -2, 2, 0, -1]]]
  g := ![![![0, 3, -1, -2, 0], ![-4, 8, 3, -2, -4], ![1, -3, 0, -2, -4], ![9, -15, -7, -3, 0], ![10, -13, -9, -6, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![43, -73, 69, -58, 16]] ![![11, 3, -1, -2, 0]]
  ![![167, 0, 0, 0, 0]] where
 M := ![![![-167, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC167 : ContainsPrimesAboveP 167 ![I167N0, I167N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
    exact isPrimeI167N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 167 (by decide) (𝕀 ⊙ MulI167N0)
instance hp173 : Fact (Nat.Prime 173) := {out := by norm_num}

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![417, -425, -271, -10, 206]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![417, -425, -271, -10, 206]] 
 ![![173, 0, 0, 0, 0], ![0, 173, 0, 0, 0], ![0, 0, 173, 0, 0], ![30, 132, 69, 1, 0], ![6, 111, 149, 0, 1]] where
  M :=![![![417, -425, -271, -10, 206], ![824, 342, -13, -130, -20], ![-80, 661, 302, -66, -260], ![-932, -223, 77, 107, -56], ![-524, -573, -161, 86, 117]]]
  hmulB := by decide  
  f := ![![![-91, 23, -37, -50, 58]], ![![232, -120, 139, 42, -100]], ![![-400, 313, -320, 78, 84]], ![![2, 36, -27, 53, -32]], ![![-198, 194, -188, 94, 9]]]
  g := ![![![-3, -127, -175, -10, 206], ![28, 114, 69, -130, -20], ![20, 221, 252, -66, -260], ![-22, -47, 6, 107, -56], ![-22, -144, -136, 86, 117]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [97, 130, 79, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [128, 66, 41], [139, 106, 132], [0, 1]]
 g := ![![[29, 26, 10], [31, 122], [53, 115, 126], [148, 135, 119], [82, 43], [56, 94, 1], []], ![[146, 59, 140, 13], [], [38, 136, 29, 25], [97, 34, 63, 149], [17, 55], [115, 11, 169, 150], [114, 124]], ![[17, 109, 101, 43], [101, 122], [4, 42, 53, 55], [131, 54, 84, 172], [102, 132], [77, 3, 107, 113], [23, 124]]]
 h' := ![![[128, 66, 41], [86, 65, 150], [49, 129, 128], [3, 29, 105], [94, 131, 43], [104, 37, 40], [0, 0, 1], [0, 1]], ![[139, 106, 132], [88, 155, 54], [61, 153], [3, 144, 36], [47, 62, 68], [73, 13, 48], [136, 82, 106], [128, 66, 41]], ![[0, 1], [111, 126, 142], [96, 64, 45], [149, 0, 32], [104, 153, 62], [134, 123, 85], [136, 91, 66], [139, 106, 132]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31, 35], []]
 b := ![[], [136, 150, 54], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [97, 130, 79, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-660237, -213928, -596796, -317750, -237536]
  a := ![-1, -6, -4, 5, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![59523, 393616, 327866, -317750, -237536]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 5177717 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-91, 23, -37, -50, 58]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![-91, 23, -37, -50, 58]] 
 ![![173, 0, 0, 0, 0], ![0, 173, 0, 0, 0], ![92, 35, 1, 0, 0], ![120, 126, 0, 1, 0], ![86, 18, 0, 0, 1]] where
  M :=![![![-91, 23, -37, -50, 58], ![232, -120, 139, 42, -100], ![-400, 313, -320, 78, 84], ![52, -219, 171, -257, 128], ![140, 107, -51, 278, -207]]]
  hmulB := by decide  
  f := ![![![417, -425, -271, -10, 206]], ![![824, 342, -13, -130, -20]], ![![388, -153, -145, -32, 104]], ![![884, -47, -197, -101, 128]], ![![290, -179, -137, -18, 101]]]
  g := ![![![25, 38, -37, -50, 58], ![-52, -49, 139, 42, -100], ![72, 1, -320, 78, 84], ![24, 138, 171, -257, 128], ![-62, -170, -51, 278, -207]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P1 : CertificateIrreducibleZModOfList' 173 2 2 7 [101, 58, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [115, 172], [0, 1]]
 g := ![![[4, 167], [15], [3, 15], [130, 57], [73], [157, 77], [1]], ![[6, 6], [15], [171, 158], [111, 116], [73], [16, 96], [1]]]
 h' := ![![[115, 172], [161, 72], [43, 19], [18, 154], [87, 149], [59, 65], [72, 115], [0, 1]], ![[0, 1], [137, 101], [152, 154], [82, 19], [95, 24], [95, 108], [149, 58], [115, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [88, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N1 : CertifiedPrimeIdeal' SI173N1 173 where
  n := 2
  hpos := by decide
  P := [101, 58, 1]
  hirr := P173P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3123, 3060, -2692, 248, 1208]
  a := ![0, -2, 4, -18, 14]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![641, 256, -2692, 248, 1208]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N1 B_one_repr
lemma NI173N1 : Nat.card (O ⧸ I173N1) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![417, -425, -271, -10, 206]] ![![-91, 23, -37, -50, 58]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![12133, 19910, 13500, 13832, 7984]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![12133, 19910, 13500, 13832, 7984]] 
 ![![179, 0, 0, 0, 0], ![0, 179, 0, 0, 0], ![0, 0, 179, 0, 0], ![0, 0, 0, 179, 0], ![114, 128, 125, 22, 1]] where
  M :=![![![12133, 19910, 13500, 13832, 7984], ![31936, 47449, 35878, 42968, 27664], ![110656, 138446, 102777, 127084, 85936], ![155904, 189502, 137220, 167229, 113252], ![210536, 263078, 190064, 228988, 153397]]]
  hmulB := by decide  
  f := ![![![3127, -3354, 3160, -1864, 48]], ![![192, 4471, -3258, 6416, -3728]], ![![-14912, -378, -2985, -13972, 12832]], ![![25568, -11754, 14272, 6639, -12108]], ![![-5278, -564, -739, -5546, 4885]]]
  g := ![![![-5017, -5598, -5500, -904, 7984], ![-17440, -19517, -19118, -3160, 27664], ![-54112, -60678, -59437, -9852, 85936], ![-71256, -79926, -78320, -12985, 113252], ![-96518, -108222, -106059, -17574, 153397]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 4 2 7 [168, 107, 161, 158, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [140, 178, 21, 22], [119, 129, 176, 62], [120, 50, 161, 95], [0, 1]]
 g := ![![[29, 151, 86, 36], [163, 101, 147, 151], [38, 174, 151], [142, 114, 81], [174, 17, 105, 177], [21, 1], []], ![[151, 136, 158, 3, 100, 145], [151, 123, 3, 111, 81, 153], [46, 44, 9], [124, 164, 144], [118, 149, 132, 119, 71, 116], [25, 126, 75, 150, 22, 3], [128, 169, 126]], ![[104, 46, 150, 130, 92, 69], [47, 163, 125, 178, 165, 136], [138, 47, 70], [83, 84, 177], [54, 115, 135, 68, 132, 90], [32, 131, 159, 58, 174, 78], [131, 160, 85]], ![[127, 75, 106, 134, 157, 80], [109, 168, 153, 45, 170, 121], [45, 176, 155], [55, 75, 27], [100, 48, 126, 138, 27, 39], [79, 163, 95, 3, 150, 151], [174, 124, 75]]]
 h' := ![![[140, 178, 21, 22], [3, 65, 153, 6], [74, 30, 79, 144], [112, 136, 16, 35], [124, 25, 118, 170], [52, 91, 92, 101], [0, 0, 1], [0, 1]], ![[119, 129, 176, 62], [141, 80, 101, 116], [98, 50, 42, 32], [147, 176, 125, 3], [6, 75, 149, 167], [1, 67, 95, 40], [65, 55, 80, 156], [140, 178, 21, 22]], ![[120, 50, 161, 95], [108, 125, 118, 2], [42, 99, 170, 80], [99, 58, 142, 41], [9, 137, 49, 78], [12, 85, 127, 27], [29, 8, 131, 136], [119, 129, 176, 62]], ![[0, 1], [121, 88, 165, 55], [129, 0, 67, 102], [156, 167, 75, 100], [154, 121, 42, 122], [152, 115, 44, 11], [25, 116, 146, 66], [120, 50, 161, 95]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [130, 95, 20], []]
 b := ![[], [], [3, 9, 110, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 4
  hpos := by decide
  P := [168, 107, 161, 158, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4369135, 40387378, -2755741, 25760024, 15908029]
  a := ![13, -6, -3, 2, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-10155779, -11149946, -11124354, -1811266, 15908029]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 1026625681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3127, 3354, -3160, 1864, -48]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![-3127, 3354, -3160, 1864, -48]] 
 ![![179, 0, 0, 0, 0], ![135, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![32, 0, 0, 1, 0], ![10, 0, 0, 0, 1]] where
  M :=![![![-3127, 3354, -3160, 1864, -48], ![-192, -4471, 3258, -6416, 3728], ![14912, 378, 2985, 13972, -12832], ![-25568, 11754, -14272, -6639, 12108], ![24312, -14950, 16356, 1044, -8503]]]
  hmulB := by decide  
  f := ![![![-12133, -19910, -13500, -13832, -7984]], ![![-9329, -15281, -10382, -10672, -6176]], ![![-2855, -4444, -3063, -3260, -1952]], ![![-3040, -4618, -3180, -3407, -2060]], ![![-1854, -2582, -1816, -2052, -1303]]]
  g := ![![![-2295, 3354, -3160, 1864, -48], ![3709, -4471, 3258, -6416, 3728], ![-2533, 378, 2985, 13972, -12832], ![-5866, 11754, -14272, -6639, 12108], ![8684, -14950, 16356, 1044, -8503]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![12133, 19910, 13500, 13832, 7984]] ![![-3127, 3354, -3160, 1864, -48]]
  ![![179, 0, 0, 0, 0]] where
 M := ![![![-179, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13673, -17453, -12715, -15340, -10230]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![-13673, -17453, -12715, -15340, -10230]] 
 ![![181, 0, 0, 0, 0], ![0, 181, 0, 0, 0], ![0, 0, 181, 0, 0], ![0, 0, 0, 181, 0], ![28, 22, 168, 13, 1]] where
  M :=![![![-13673, -17453, -12715, -15340, -10230], ![-40920, -51958, -37913, -45890, -30680], ![-122720, -155403, -113318, -137186, -91780], ![-163100, -206523, -150525, -182153, -121846], ![-223232, -282833, -206151, -249426, -166813]]]
  hmulB := by decide  
  f := ![![![-101, 75, -77, 12, 26]], ![![104, -140, 127, -102, 24]], ![![96, 153, -92, 302, -204]], ![![-460, 121, -191, -245, 290]], ![![56, 144, -94, 253, -163]]]
  g := ![![![1507, 1147, 9425, 650, -10230], ![4520, 3442, 28267, 1950, -30680], ![13520, 10297, 84562, 5834, -91780], ![17948, 13669, 112263, 7745, -121846], ![24572, 18713, 153693, 10603, -166813]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 4 2 7 [166, 97, 22, 116, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [82, 96, 170, 132], [87, 67, 135, 69], [77, 17, 57, 161], [0, 1]]
 g := ![![[102, 86, 94, 172], [52, 35, 55], [52, 110, 44, 177], [86, 16, 67], [21, 63, 121, 152], [65, 1], []], ![[84, 47, 133, 121, 71, 108], [42, 119, 170], [52, 75, 74, 111, 16, 177], [142, 109, 9], [154, 148, 79, 91, 161, 111], [65, 123, 116, 10, 131, 56], [77, 35, 48]], ![[142, 125, 54, 111, 58, 158], [30, 117, 33], [155, 3, 28, 161, 147, 149], [160, 165, 129], [3, 161, 30, 6, 139, 26], [103, 86, 123, 53, 28, 54], [47, 123, 55]], ![[95, 3, 104, 157, 79, 148], [5, 68, 52], [100, 115, 167, 56, 49, 135], [154, 158, 1], [43, 87, 131, 6, 104, 39], [124, 178, 142, 75, 6, 152], [146, 9, 38]]]
 h' := ![![[82, 96, 170, 132], [115, 91, 129, 124], [56, 25, 116, 69], [60, 109, 177, 143], [134, 7, 94, 130], [70, 45, 102, 40], [0, 0, 1], [0, 1]], ![[87, 67, 135, 69], [92, 115, 81, 109], [27, 11, 79, 129], [74, 127, 169, 52], [109, 38, 19, 178], [107, 99, 113, 160], [96, 112, 147, 110], [82, 96, 170, 132]], ![[77, 17, 57, 161], [50, 127, 11, 28], [18, 106, 3, 24], [93, 12, 2, 41], [107, 94, 24, 55], [45, 124, 151, 33], [129, 75, 92, 132], [87, 67, 135, 69]], ![[0, 1], [27, 29, 141, 101], [26, 39, 164, 140], [90, 114, 14, 126], [26, 42, 44, 180], [155, 94, 177, 129], [155, 175, 122, 120], [77, 17, 57, 161]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [74, 128, 103], []]
 b := ![[], [], [148, 156, 172, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 4
  hpos := by decide
  P := [166, 97, 22, 116, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5851436, 1775198, 4868403, 3117136, 1427627]
  a := ![-1, 0, 2, -4, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-188520, -163716, -1298193, -85315, 1427627]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 1073283121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-101, 75, -77, 12, 26]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![-101, 75, -77, 12, 26]] 
 ![![181, 0, 0, 0, 0], ![155, 1, 0, 0, 0], ![48, 0, 1, 0, 0], ![94, 0, 0, 1, 0], ![149, 0, 0, 0, 1]] where
  M :=![![![-101, 75, -77, 12, 26], ![104, -140, 127, -102, 24], ![96, 153, -92, 302, -204], ![-460, 121, -191, -245, 290], ![528, -233, 287, 150, -257]]]
  hmulB := by decide  
  f := ![![![-13673, -17453, -12715, -15340, -10230]], ![![-11935, -15233, -11098, -13390, -8930]], ![![-4304, -5487, -3998, -4826, -3220]], ![![-8002, -10205, -7435, -8973, -5986]], ![![-12489, -15930, -11606, -14006, -9343]]]
  g := ![![![-72, 75, -77, 12, 26], ![120, -140, 127, -102, 24], ![-95, 153, -92, 302, -204], ![-167, 121, -191, -245, 290], ![260, -233, 287, 150, -257]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![-13673, -17453, -12715, -15340, -10230]] ![![-101, 75, -77, 12, 26]]
  ![![181, 0, 0, 0, 0]] where
 M := ![![![181, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC181 : ContainsPrimesAboveP 181 ![I181N0, I181N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
    exact isPrimeI181N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 181 (by decide) (𝕀 ⊙ MulI181N0)
instance hp191 : Fact (Nat.Prime 191) := {out := by norm_num}

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, -9, 1, -12, 0]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![-3, -9, 1, -12, 0]] 
 ![![191, 0, 0, 0, 0], ![0, 191, 0, 0, 0], ![0, 0, 191, 0, 0], ![48, 144, 175, 1, 0], ![4, 124, 7, 0, 1]] where
  M :=![![![-3, -9, 1, -12, 0], ![0, -14, -9, 2, -24], ![-96, -31, -62, -66, 4], ![8, -103, -7, -59, -54], ![-108, -49, -101, -62, -47]]]
  hmulB := by decide  
  f := ![![![-5, -35, -15, 4, 12]], ![![48, -4, -11, -6, 8]], ![![32, 39, 12, -6, -12]], ![![64, 24, -1, -9, -2]], ![![32, -2, -7, -4, 5]]]
  g := ![![![3, 9, 11, -12, 0], ![0, 14, -1, 2, -24], ![16, 47, 60, -66, 4], ![16, 79, 56, -59, -54], ![16, 77, 58, -62, -47]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 3 2 7 [101, 107, 101, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [74, 130, 87], [16, 60, 104], [0, 1]]
 g := ![![[56, 178, 133], [159, 5, 180], [133, 50, 40], [113, 105, 30], [46, 33, 128], [162, 90, 1], []], ![[114, 113, 10, 183], [79, 23, 34, 119], [85, 128, 109, 182], [9, 163, 79, 93], [100, 28, 148, 188], [113, 33, 59, 151], [186, 120]], ![[106, 190, 137, 59], [90, 108, 79, 98], [42, 163, 168, 154], [5, 182, 90, 81], [50, 139, 80, 45], [112, 25, 157, 18], [169, 120]]]
 h' := ![![[74, 130, 87], [176, 12, 18], [128, 118, 107], [47, 57, 123], [129, 43, 52], [64, 125, 74], [0, 0, 1], [0, 1]], ![[16, 60, 104], [43, 111, 23], [0, 137, 69], [185, 87, 115], [128, 67, 176], [2, 170, 35], [60, 15, 60], [74, 130, 87]], ![[0, 1], [87, 68, 150], [144, 127, 15], [153, 47, 144], [175, 81, 154], [166, 87, 82], [186, 176, 130], [16, 60, 104]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58, 89], []]
 b := ![[], [37, 107, 179], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 3
  hpos := by decide
  P := [101, 107, 101, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2667580, 3074746, 2364085, 2863823, 1728463]
  a := ![3, 10, 7, -1, 21]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-741936, -3265158, -2674891, 2863823, 1728463]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 6967871 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 340, -13, -414, -421]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![29, 340, -13, -414, -421]] 
 ![![191, 0, 0, 0, 0], ![96, 1, 0, 0, 0], ![143, 0, 1, 0, 0], ![155, 0, 0, 1, 0], ![152, 0, 0, 0, 1]] where
  M :=![![![29, 340, -13, -414, -421], ![-1684, -819, -502, -868, -828], ![-3312, -3882, -2475, -2660, -1736], ![-2630, -4682, -3426, -3777, -2246], ![-3650, -5630, -4336, -5238, -3363]]]
  hmulB := by decide  
  f := ![![![-185027, 207236, -193459, 122552, -9843]], ![![-93204, 102769, -96254, 59468, -3664]], ![![-133395, 155086, -143666, 96284, -11627]], ![![-158565, 172162, -161779, 97435, -4099]], ![![-139366, 159954, -148566, 97698, -10493]]]
  g := ![![![510, 340, -13, -414, -421], ![2142, -819, -502, -868, -828], ![7327, -3882, -2475, -2660, -1736], ![9757, -4682, -3426, -3777, -2246], ![12984, -5630, -4336, -5238, -3363]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1

def I191N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4019, 667, -1372, -2692, 2845]] i)))

def SI191N2: IdealEqSpanCertificate' Table ![![-4019, 667, -1372, -2692, 2845]] 
 ![![191, 0, 0, 0, 0], ![127, 1, 0, 0, 0], ![106, 0, 1, 0, 0], ![177, 0, 0, 1, 0], ![157, 0, 0, 0, 1]] where
  M :=![![![-4019, 667, -1372, -2692, 2845], ![11380, -5238, 6357, 2946, -5384], ![-21536, 15299, -16006, 1946, 5892], ![6094, -12233, 10363, -11587, 4638], ![3586, 7373, -4657, 13528, -8895]]]
  hmulB := by decide  
  f := ![![![43317, 58653, 43194, 51718, 33931]], ![![29513, 39901, 29383, 35196, 23103]], ![![26206, 35273, 25956, 31110, 20446]], ![![43017, 57990, 42673, 51123, 33581]], ![![39525, 53188, 39129, 46890, 30816]]]
  g := ![![![453, 667, -1372, -2692, 2845], ![1710, -5238, 6357, 2946, -5384], ![-8049, 15299, -16006, 1946, 5892], ![9340, -12233, 10363, -11587, 4638], ![-7524, 7373, -4657, 13528, -8895]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N2 : Nat.card (O ⧸ I191N2) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N2)

lemma isPrimeI191N2 : Ideal.IsPrime I191N2 := prime_ideal_of_norm_prime hp191.out _ NI191N2
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![-3, -9, 1, -12, 0]] ![![29, 340, -13, -414, -421]]
  ![![43317, 58653, 43194, 51718, 33931]] where
 M := ![![![43317, 58653, 43194, 51718, 33931]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI191N1 : IdealMulLeCertificate' Table 
  ![![43317, 58653, 43194, 51718, 33931]] ![![-4019, 667, -1372, -2692, 2845]]
  ![![191, 0, 0, 0, 0]] where
 M := ![![![191, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC191 : ContainsPrimesAboveP 191 ![I191N0, I191N1, I191N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI191N0
    exact isPrimeI191N1
    exact isPrimeI191N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 191 (by decide) (𝕀 ⊙ MulI191N0 ⊙ MulI191N1)
instance hp193 : Fact (Nat.Prime 193) := {out := by norm_num}

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![217, -24, -69, -60, 7]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![217, -24, -69, -60, 7]] 
 ![![193, 0, 0, 0, 0], ![0, 193, 0, 0, 0], ![0, 0, 193, 0, 0], ![20, 89, 85, 1, 0], ![37, 15, 57, 0, 1]] where
  M :=![![![217, -24, -69, -60, 7], ![28, 95, -10, -124, -120], ![-480, -226, -145, -260, -248], ![-510, -614, -356, -331, -200], ![-414, -746, -502, -494, -271]]]
  hmulB := by decide  
  f := ![![![-137, 96, -101, 10, 39]], ![![156, -189, 174, -124, 20]], ![![80, 226, -149, 388, -248]], ![![90, 23, 3, 113, -94]], ![![13, 69, -48, 108, -66]]]
  g := ![![![6, 27, 24, -60, 7], ![36, 67, 90, -124, -120], ![72, 138, 187, -260, -248], ![70, 165, 203, -331, -200], ![101, 245, 295, -494, -271]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 3 2 7 [65, 36, 26, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [18, 191, 180], [149, 1, 13], [0, 1]]
 g := ![![[166, 18, 165], [80, 147], [101, 181], [117, 85], [49, 83], [122, 97], [1]], ![[80, 175, 94, 51], [86, 108], [23, 191], [51, 131], [19, 4], [161, 48], [149, 133, 138, 119]], ![[115, 1, 94, 152], [89, 3], [11, 3], [59, 50], [55, 126], [16, 128], [56, 136, 127, 74]]]
 h' := ![![[18, 191, 180], [179, 157, 101], [174, 14, 98], [131, 36, 48], [189, 57, 144], [155, 159, 135], [128, 157, 167], [0, 1]], ![[149, 1, 13], [119, 125, 183], [43, 54, 109], [103, 43, 159], [152, 38, 175], [6, 114, 191], [7, 66, 56], [18, 191, 180]], ![[0, 1], [33, 104, 102], [75, 125, 179], [37, 114, 179], [28, 98, 67], [124, 113, 60], [149, 163, 163], [149, 1, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [131, 181], []]
 b := ![[], [106, 185, 103], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 3
  hpos := by decide
  P := [65, 36, 26, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![133922, 126244, 116054, 126064, 72825]
  a := ![1, 4, 2, -2, 9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-26331, -63139, -76427, 126064, 72825]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 7189057 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-137, 96, -101, 10, 39]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![-137, 96, -101, 10, 39]] 
 ![![193, 0, 0, 0, 0], ![0, 193, 0, 0, 0], ![154, 23, 1, 0, 0], ![159, 6, 0, 1, 0], ![117, 11, 0, 0, 1]] where
  M :=![![![-137, 96, -101, 10, 39], ![156, -189, 174, -124, 20], ![80, 226, -149, 388, -248], ![-574, 130, -222, -335, 378], ![678, -282, 356, 218, -345]]]
  hmulB := by decide  
  f := ![![![217, -24, -69, -60, 7]], ![![28, 95, -10, -124, -120]], ![![174, -9, -57, -64, -10]], ![![177, -20, -59, -55, 1]], ![![131, -13, -45, -46, -4]]]
  g := ![![![48, 10, -101, 10, 39], ![-48, -19, 174, -124, 20], ![-50, 21, -149, 388, -248], ![221, 16, -222, -335, 378], ![-251, -31, 356, 218, -345]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P1 : CertificateIrreducibleZModOfList' 193 2 2 7 [146, 41, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [152, 192], [0, 1]]
 g := ![![[110, 2], [96], [93], [27], [151], [81], [152, 1]], ![[28, 191], [96], [93], [27], [151], [81], [111, 192]]]
 h' := ![![[152, 192], [180, 52], [53, 176], [11, 155], [155, 151], [149, 99], [3, 184], [0, 1]], ![[0, 1], [171, 141], [171, 17], [25, 38], [140, 42], [143, 94], [179, 9], [152, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [76]]
 b := ![[], [7, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N1 : CertifiedPrimeIdeal' SI193N1 193 where
  n := 2
  hpos := by decide
  P := [146, 41, 1]
  hirr := P193P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![352, 77, -35, 152, -108]
  a := ![4, -1, -1, 1, -3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-30, 6, -35, 152, -108]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N1 B_one_repr
lemma NI193N1 : Nat.card (O ⧸ I193N1) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![217, -24, -69, -60, 7]] ![![-137, 96, -101, 10, 39]]
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

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![51, 151, 10, -32, -13]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![51, 151, 10, -32, -13]] 
 ![![197, 0, 0, 0, 0], ![0, 197, 0, 0, 0], ![0, 0, 197, 0, 0], ![0, 0, 0, 197, 0], ![87, 49, 75, 154, 1]] where
  M :=![![![51, 151, 10, -32, -13], ![-52, 16, 125, -6, -64], ![-256, 3, -112, 122, -12], ![2, -137, -73, -121, 154], ![334, -27, 23, 84, -89]]]
  hmulB := by decide  
  f := ![![![9, 11, 8, 10, 7]], ![![28, 34, 25, 30, 20]], ![![80, 103, 74, 90, 60]], ![![106, 135, 99, 119, 80]], ![![125, 159, 116, 140, 94]]]
  g := ![![![6, 4, 5, 10, -13], ![28, 16, 25, 50, -64], ![4, 3, 4, 10, -12], ![-68, -39, -59, -121, 154], ![41, 22, 34, 70, -89]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 4 2 7 [80, 21, 95, 138, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [88, 49, 116, 183], [64, 173, 88, 133], [104, 171, 190, 78], [0, 1]]
 g := ![![[58, 170, 93, 132], [176, 4, 93], [3, 138, 124, 148], [185, 43, 15], [146, 93, 168], [37, 59, 1], []], ![[134, 181, 94, 7, 45, 128], [54, 174, 172], [54, 153, 48, 153, 46, 131], [88, 121, 55], [92, 126, 51], [192, 164, 127], [124, 133, 112, 171, 84, 14]], ![[17, 126, 53, 146, 124, 171], [125, 98, 63], [28, 165, 150, 188, 182, 65], [43, 124, 41], [11, 15, 19], [10, 75, 37], [16, 194, 105, 130, 182, 63]], ![[27, 12, 52, 57, 122, 125], [74, 28, 92], [55, 3, 127, 166, 160, 86], [70, 73, 25], [15, 44, 172], [64, 101, 93], [195, 53, 40, 4, 32, 176]]]
 h' := ![![[88, 49, 116, 183], [180, 9, 60, 59], [154, 125, 190, 68], [14, 130, 60, 99], [165, 139, 132, 58], [192, 19, 91, 103], [0, 0, 0, 1], [0, 1]], ![[64, 173, 88, 133], [69, 55, 138, 77], [152, 132, 16, 70], [58, 187, 55, 88], [177, 175, 101, 45], [53, 154, 148, 144], [176, 57, 174, 18], [88, 49, 116, 183]], ![[104, 171, 190, 78], [46, 57, 150, 39], [183, 173, 6, 76], [2, 88, 168, 165], [68, 157, 183, 89], [102, 58, 154, 77], [36, 98, 79, 49], [64, 173, 88, 133]], ![[0, 1], [158, 76, 46, 22], [94, 161, 182, 180], [21, 186, 111, 42], [156, 120, 175, 5], [78, 163, 1, 70], [154, 42, 141, 129], [104, 171, 190, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [120, 166, 93], []]
 b := ![[], [], [7, 116, 87, 23], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 4
  hpos := by decide
  P := [80, 21, 95, 138, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![235240688321, 301308485558, 217343706328, 265168193759, 177138517119]
  a := ![7, -46, -24, -23, -71]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-77034570056, -42530349509, -66335254201, -137127733211, 177138517119]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 1506138481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, 11, 8, 10, 7]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![9, 11, 8, 10, 7]] 
 ![![197, 0, 0, 0, 0], ![86, 1, 0, 0, 0], ![90, 0, 1, 0, 0], ![27, 0, 0, 1, 0], ![175, 0, 0, 0, 1]] where
  M :=![![![9, 11, 8, 10, 7], ![28, 34, 25, 30, 20], ![80, 103, 74, 90, 60], ![106, 135, 99, 119, 80], ![146, 185, 135, 164, 109]]]
  hmulB := by decide  
  f := ![![![51, 151, 10, -32, -13]], ![![22, 66, 5, -14, -6]], ![![22, 69, 4, -14, -6]], ![![7, 20, 1, -5, -1]], ![![47, 134, 9, -28, -12]]]
  g := ![![![-16, 11, 8, 10, 7], ![-48, 34, 25, 30, 20], ![-144, 103, 74, 90, 60], ![-191, 135, 99, 119, 80], ![-261, 185, 135, 164, 109]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![51, 151, 10, -32, -13]] ![![9, 11, 8, 10, 7]]
  ![![197, 0, 0, 0, 0]] where
 M := ![![![197, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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


lemma PB307I4_primes (p : ℕ) :
  p ∈ Set.range ![157, 163, 167, 173, 179, 181, 191, 193, 197] ↔ Nat.Prime p ∧ 151 < p ∧ p ≤ 197 := by
  rw [← List.mem_ofFn']
  convert primes_range 151 197 (by omega)

def PB307I4 : PrimesBelowBoundCertificateInterval O 151 197 307 where
  m := 9
  g := ![3, 2, 2, 2, 2, 2, 3, 2, 2]
  P := ![157, 163, 167, 173, 179, 181, 191, 193, 197]
  hP := PB307I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I157N0, I157N1, I157N2]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1]
    · exact ![I173N0, I173N1]
    · exact ![I179N0, I179N1]
    · exact ![I181N0, I181N1]
    · exact ![I191N0, I191N1, I191N2]
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
    · exact ![24649, 24649, 157]
    · exact ![705911761, 163]
    · exact ![777796321, 167]
    · exact ![5177717, 29929]
    · exact ![1026625681, 179]
    · exact ![1073283121, 181]
    · exact ![6967871, 191, 191]
    · exact ![7189057, 37249]
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
      exact NI157N2
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
      exact NI163N1
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
      exact NI191N2
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
      exact NI197N1
  β := ![I157N2, I163N1, I167N1, I179N1, I181N1, I191N1, I191N2, I197N1]
  Il := ![[I157N2], [I163N1], [I167N1], [], [I179N1], [I181N1], [I191N1, I191N2], [], [I197N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
