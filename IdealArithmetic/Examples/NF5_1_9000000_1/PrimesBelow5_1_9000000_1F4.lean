
import IdealArithmetic.Examples.NF5_1_9000000_1.RI5_1_9000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0, 0, 0]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0, 0, 0]] 
 ![![157, 0, 0, 0, 0], ![0, 157, 0, 0, 0], ![0, 0, 157, 0, 0], ![0, 0, 0, 157, 0], ![0, 0, 0, 0, 157]] where
  M :=![![![157, 0, 0, 0, 0], ![0, 157, 0, 0, 0], ![0, 0, 157, 0, 0], ![0, 0, 0, 157, 0], ![0, 0, 0, 0, 157]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 5 2 7 [23, 54, 84, 90, 20, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 136, 150, 45, 149], [148, 46, 37, 142, 143], [42, 100, 156, 7, 15], [84, 31, 128, 120, 7], [0, 1]]
 g := ![![[122, 100, 90, 147, 52], [93, 94, 101, 138], [80, 43, 121, 71, 140], [101, 108, 82, 2, 47], [135, 69, 153, 137, 1], [], []], ![[51, 93, 127, 24, 90, 5, 117, 72], [94, 3, 98, 153], [24, 98, 89, 9, 89, 117, 18, 70], [15, 25, 125, 29, 79, 107, 78, 97], [23, 64, 10, 153, 88, 125, 115, 87], [43, 93, 76, 154], [58, 110, 41, 64]], ![[134, 72, 9, 94, 57, 143, 57, 47], [141, 104, 55, 31], [48, 88, 39, 142, 79, 39, 1, 13], [139, 41, 152, 106, 136, 74, 106, 14], [34, 152, 67, 82, 83, 30, 33, 146], [48, 27, 57, 82], [75, 53, 111, 39]], ![[53, 150, 19, 140, 119, 55, 40, 150], [82, 66, 152, 140], [13, 119, 133, 27, 85, 63, 110, 7], [93, 92, 8, 67, 19, 105, 70, 53], [127, 51, 44, 151, 46, 63, 39, 55], [67, 41, 26, 105], [21, 100, 106, 68]], ![[31, 90, 73, 54, 29, 45, 148, 91], [131, 65, 21, 37], [135, 156, 93, 50, 130, 69, 18, 112], [50, 71, 15, 66, 116, 3, 83, 34], [70, 126, 130, 26, 69, 129, 153, 43], [17, 35, 11, 124], [77, 137, 72, 49]]]
 h' := ![![[20, 136, 150, 45, 149], [111, 72, 114, 156, 113], [44, 111, 27, 31, 74], [32, 38, 142, 84, 104], [35, 72, 98, 0, 19], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[148, 46, 37, 142, 143], [146, 140, 110, 124, 84], [96, 151, 59, 31, 56], [1, 148, 111, 111, 100], [70, 11, 20, 110, 137], [17, 151, 36, 23, 26], [8, 92, 24, 119, 132], [20, 136, 150, 45, 149]], ![[42, 100, 156, 7, 15], [106, 123, 118, 18, 77], [113, 8, 56, 44, 38], [100, 29, 105, 156, 147], [0, 127, 145, 57, 28], [133, 4, 86, 154, 13], [83, 26, 97, 25, 125], [148, 46, 37, 142, 143]], ![[84, 31, 128, 120, 7], [91, 10, 140, 84, 18], [67, 96, 109, 141, 104], [95, 11, 6, 98, 124], [37, 115, 39, 81, 64], [26, 75, 105, 127, 29], [25, 99, 0, 80, 133], [42, 100, 156, 7, 15]], ![[0, 1], [63, 126, 146, 89, 22], [90, 105, 63, 67, 42], [18, 88, 107, 22, 153], [45, 146, 12, 66, 66], [63, 84, 87, 10, 88], [104, 97, 35, 90, 81], [84, 31, 128, 120, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48, 6, 77, 140], [], [], []]
 b := ![[], [94, 14, 1, 95, 96], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 5
  hpos := by decide
  P := [23, 54, 84, 90, 20, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-320121273, 148092762, 83092407, 73648386, -90128676]
  a := ![0, -7, 2, -8, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2038989, 943266, 529251, 469098, -574068]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 95388992557 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def PBC157 : ContainsPrimesAboveP 157 ![I157N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![157, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 157 (by decide) 𝕀

instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0, 0, 0]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0, 0, 0]] 
 ![![163, 0, 0, 0, 0], ![0, 163, 0, 0, 0], ![0, 0, 163, 0, 0], ![0, 0, 0, 163, 0], ![0, 0, 0, 0, 163]] where
  M :=![![![163, 0, 0, 0, 0], ![0, 163, 0, 0, 0], ![0, 0, 163, 0, 0], ![0, 0, 0, 163, 0], ![0, 0, 0, 0, 163]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 5 2 7 [6, 120, 0, 92, 138, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [144, 99, 45, 48, 117], [158, 158, 98, 101, 76], [50, 144, 110, 120, 150], [162, 87, 73, 57, 146], [0, 1]]
 g := ![![[139, 141, 63, 28, 161], [98, 120, 18, 143, 62], [73, 142, 139, 16], [26, 30, 162, 126], [66, 19, 104, 136], [1], []], ![[42, 78, 70, 13, 83, 157, 74, 110], [60, 8, 132, 113, 63, 140, 70, 11], [18, 67, 7, 88], [117, 116, 134, 113], [102, 143, 61, 135], [148, 46, 77, 139, 59, 92, 154, 42], [11, 102, 73, 160]], ![[95, 106, 43, 137, 63, 56, 119, 78], [12, 107, 27, 26, 56, 86, 8, 142], [120, 29, 159, 74], [149, 48, 86, 21], [162, 61, 102, 60], [40, 28, 4, 156, 152, 121, 43, 8], [68, 120, 12, 71]], ![[43, 106, 34, 58, 92, 68, 142, 10], [8, 60, 162, 5, 129, 44, 8, 35], [156, 41, 131, 100], [67, 104, 46, 93], [78, 143, 56, 26], [148, 153, 134, 13, 118, 144, 156, 77], [90, 145, 127, 6]], ![[98, 16, 111, 158, 99, 10, 141, 69], [23, 120, 33, 91, 157, 24, 147, 132], [105, 95, 99, 95], [90, 73, 83, 136], [138, 102, 23, 90], [124, 149, 159, 162, 3, 151, 0, 49], [130, 78, 71, 126]]]
 h' := ![![[144, 99, 45, 48, 117], [64, 68, 150, 138, 18], [46, 92, 97, 161, 148], [22, 102, 109, 110, 4], [129, 89, 86, 155, 146], [157, 43, 0, 71, 25], [0, 0, 1], [0, 1]], ![[158, 158, 98, 101, 76], [98, 76, 60, 27, 130], [52, 109, 37, 126, 68], [46, 6, 79, 70, 67], [111, 62, 78, 91, 90], [87, 85, 10, 53, 61], [132, 11, 140, 103, 127], [144, 99, 45, 48, 117]], ![[50, 144, 110, 120, 150], [107, 9, 79, 68, 121], [148, 41, 40, 19, 106], [85, 62, 90, 27, 20], [1, 150, 83, 48, 99], [141, 154, 79, 75, 95], [106, 135, 58, 157, 80], [158, 158, 98, 101, 76]], ![[162, 87, 73, 57, 146], [82, 55, 54, 89, 24], [40, 11, 67, 62, 68], [145, 66, 101, 69, 10], [104, 31, 76, 158, 16], [75, 152, 87, 1, 29], [4, 122, 45, 75, 135], [50, 144, 110, 120, 150]], ![[0, 1], [155, 118, 146, 4, 33], [14, 73, 85, 121, 99], [127, 90, 110, 50, 62], [34, 157, 3, 37, 138], [79, 55, 150, 126, 116], [36, 58, 82, 154, 147], [162, 87, 73, 57, 146]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58, 87, 73, 10], [], [], []]
 b := ![[], [44, 106, 31, 109, 64], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 5
  hpos := by decide
  P := [6, 120, 0, 92, 138, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1602002436541, 688030237526, 271040926999, -905109709389, -2608006988299]
  a := ![3, -62, -1, -63, -119]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9828235807, 4221044402, 1662827773, -5552820303, -16000042873]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 115063617043 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def PBC163 : ContainsPrimesAboveP 163 ![I163N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![163, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 163 (by decide) 𝕀

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


def P167P0 : CertificateIrreducibleZModOfList' 167 5 2 7 [97, 117, 93, 38, 5, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [67, 50, 133, 140, 162], [21, 148, 6, 11, 40], [161, 139, 135, 124, 148], [80, 163, 60, 59, 151], [0, 1]]
 g := ![![[94, 87, 55, 55, 21], [63, 99, 34, 35, 22], [89, 68, 35, 124, 96], [146, 112, 80, 22], [154, 149, 88, 25], [1], []], ![[72, 127, 129, 79, 64, 149, 43, 112], [24, 151, 20, 142, 71, 141, 49, 36], [25, 68, 72, 151, 101, 86, 162, 66], [33, 166, 5, 72], [37, 54, 60, 61], [34, 106, 91, 9, 19, 6, 148, 77], [38, 62, 145, 25]], ![[112, 0, 152, 70, 8, 24, 10, 92], [85, 70, 16, 53, 121, 64, 100, 39], [159, 95, 48, 45, 122, 10, 140, 160], [31, 2, 51, 132], [74, 51, 33, 11], [106, 123, 65, 145, 125, 119, 34, 70], [48, 117, 61, 97]], ![[115, 115, 157, 122, 138, 40, 101, 140], [107, 29, 80, 166, 145, 93, 93, 164], [151, 117, 121, 163, 11, 98, 30, 20], [149, 18, 49, 28], [97, 120, 10, 133], [55, 126, 12, 89, 133, 27, 3, 40], [13, 55, 163, 27]], ![[5, 148, 138, 107, 15, 82, 107, 136], [133, 42, 60, 162, 88, 72, 59, 158], [63, 141, 56, 156, 82, 46, 44, 35], [49, 94, 136, 96], [46, 37, 44, 130], [125, 152, 116, 141, 142, 93, 12, 120], [122, 158, 5, 89]]]
 h' := ![![[67, 50, 133, 140, 162], [68, 156, 30, 76, 45], [51, 53, 79, 16, 135], [23, 69, 59, 150, 51], [149, 80, 124, 44, 135], [70, 50, 74, 129, 162], [0, 0, 1], [0, 1]], ![[21, 148, 6, 11, 40], [150, 99, 110, 120, 41], [115, 129, 74, 166, 107], [26, 48, 154, 84, 33], [87, 139, 67, 149, 78], [13, 65, 86, 115, 27], [135, 81, 145, 116, 39], [67, 50, 133, 140, 162]], ![[161, 139, 135, 124, 148], [109, 63, 126, 79, 112], [115, 87, 89, 58, 40], [35, 28, 46, 128, 165], [6, 112, 48, 55, 93], [105, 152, 140, 164, 41], [127, 106, 90, 41, 131], [21, 148, 6, 11, 40]], ![[80, 163, 60, 59, 151], [81, 30, 42, 46, 112], [47, 7, 61, 158, 93], [35, 155, 82, 120, 150], [31, 161, 114, 152, 144], [64, 53, 31, 54, 48], [111, 160, 91, 59, 54], [161, 139, 135, 124, 148]], ![[0, 1], [10, 153, 26, 13, 24], [3, 58, 31, 103, 126], [75, 34, 160, 19, 102], [94, 9, 148, 101, 51], [106, 14, 3, 39, 56], [77, 154, 7, 118, 110], [80, 163, 60, 59, 151]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [118, 112, 68, 5], [], [], []]
 b := ![[], [56, 37, 57, 80, 1], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 5
  hpos := by decide
  P := [97, 117, 93, 38, 5, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-45706731, 19156737, 9852165, -15585108, -58926117]
  a := ![1, -6, 1, -7, -12]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-273693, 114711, 58995, -93324, -352851]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1279, -559, -394, -270, -468]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![-1279, -559, -394, -270, -468]] 
 ![![173, 0, 0, 0, 0], ![0, 173, 0, 0, 0], ![140, 3, 1, 0, 0], ![99, 148, 0, 1, 0], ![27, 80, 0, 0, 1]] where
  M :=![![![-1279, -559, -394, -270, -468], ![-1872, -809, -578, -392, -684], ![-1368, -591, -417, -286, -492], ![-48, -36, -16, -15, -24], ![168, 81, 52, 38, 65]]]
  hmulB := by decide  
  f := ![![![61, -23, -20, 6, 48]], ![![192, -91, -58, -124, -60]], ![![52, -20, -17, 2, 36]], ![![195, -89, -60, -101, -24]], ![![99, -46, -30, -56, -19]]]
  g := ![![![539, 451, -394, -270, -468], ![788, 657, -578, -392, -684], ![570, 476, -417, -286, -492], ![25, 24, -16, -15, -24], ![-73, -63, 52, 38, 65]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [64, 53, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [120, 172], [0, 1]]
 g := ![![[63, 73], [152], [44, 4], [1, 121], [15], [113, 41], [1]], ![[0, 100], [152], [5, 169], [162, 52], [15], [16, 132], [1]]]
 h' := ![![[120, 172], [15, 108], [125, 124], [109, 171], [23, 162], [34, 154], [109, 120], [0, 1]], ![[0, 1], [0, 65], [127, 49], [42, 2], [87, 11], [3, 19], [150, 53], [120, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66]]
 b := ![[], [96, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [64, 53, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2790, 1505, 3469, 5698, 8079]
  a := ![1, 25, -3, 24, 59]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7345, -8662, 3469, 5698, 8079]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, -57, 23, -16, -3]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![59, -57, 23, -16, -3]] 
 ![![173, 0, 0, 0, 0], ![0, 173, 0, 0, 0], ![170, 81, 1, 0, 0], ![70, 12, 0, 1, 0], ![103, 57, 0, 0, 1]] where
  M :=![![![59, -57, 23, -16, -3], ![-12, 59, -82, 20, -90], ![-180, 108, 39, 28, 150], ![306, -297, 121, -93, -21], ![-172, 166, -68, 50, 1]]]
  hmulB := by decide  
  f := ![![![-5153, -2235, -1583, -1082, -1881]], ![![-7524, -3257, -2306, -1568, -2730]], ![![-8618, -3735, -2645, -1804, -3138]], ![![-2608, -1131, -801, -547, -951]], ![![-5543, -2402, -1701, -1160, -2018]]]
  g := ![![![-14, -9, 23, -16, -3], ![126, 67, -82, 20, -90], ![-140, -69, 39, 28, 150], ![-67, -45, 121, -93, -21], ![45, 29, -68, 50, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P1 : CertificateIrreducibleZModOfList' 173 2 2 7 [47, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [144, 172], [0, 1]]
 g := ![![[100, 81], [122], [112, 118], [151, 152], [21], [135, 149], [1]], ![[0, 92], [122], [150, 55], [68, 21], [21], [139, 24], [1]]]
 h' := ![![[144, 172], [88, 9], [99, 45], [169, 34], [73, 49], [56, 114], [126, 144], [0, 1]], ![[0, 1], [0, 164], [5, 128], [48, 139], [36, 124], [37, 59], [102, 29], [144, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [111]]
 b := ![[], [156, 142]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N1 : CertifiedPrimeIdeal' SI173N1 173 where
  n := 2
  hpos := by decide
  P := [47, 29, 1]
  hirr := P173P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2227, -1746, 394, 364, 990]
  a := ![-1, -7, 5, -5, -27]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1111, -546, 394, 364, 990]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N1 B_one_repr
lemma NI173N1 : Nat.card (O ⧸ I173N1) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N1

def I173N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 2, 1, -4, -9]] i)))

def SI173N2: IdealEqSpanCertificate' Table ![![-1, 2, 1, -4, -9]] 
 ![![173, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![74, 0, 1, 0, 0], ![72, 0, 0, 1, 0], ![112, 0, 0, 0, 1]] where
  M :=![![![-1, 2, 1, -4, -9], ![-36, 19, 12, 12, -6], ![-12, 9, 7, 30, 42], ![102, -45, -27, -11, 51], ![8, -5, -4, -20, -29]]]
  hmulB := by decide  
  f := ![![![43, -128, 209, -38, 249]], ![![7, -7, 5, -2, 3]], ![![10, -47, 87, -14, 108]], ![![18, -57, 93, -17, 111]], ![![28, -81, 132, -24, 157]]]
  g := ![![![7, 2, 1, -4, -9], ![-7, 19, 12, 12, -6], ![-43, 9, 7, 30, 42], ![-15, -45, -27, -11, 51], ![29, -5, -4, -20, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N2 : Nat.card (O ⧸ I173N2) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N2)

lemma isPrimeI173N2 : Ideal.IsPrime I173N2 := prime_ideal_of_norm_prime hp173.out _ NI173N2
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![-1279, -559, -394, -270, -468]] ![![59, -57, 23, -16, -3]]
  ![![43, -128, 209, -38, 249]] where
 M := ![![![43, -128, 209, -38, 249]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI173N1 : IdealMulLeCertificate' Table 
  ![![43, -128, 209, -38, 249]] ![![-1, 2, 1, -4, -9]]
  ![![173, 0, 0, 0, 0]] where
 M := ![![![173, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC173 : ContainsPrimesAboveP 173 ![I173N0, I173N1, I173N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
    exact isPrimeI173N1
    exact isPrimeI173N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 173 (by decide) (𝕀 ⊙ MulI173N0 ⊙ MulI173N1)
instance hp179 : Fact (Nat.Prime 179) := {out := by norm_num}

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, -7, 3, -2, -1]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![7, -7, 3, -2, -1]] 
 ![![179, 0, 0, 0, 0], ![124, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![96, 0, 0, 1, 0], ![34, 0, 0, 0, 1]] where
  M :=![![![7, -7, 3, -2, -1], ![-4, 9, -10, 4, -10], ![-20, 12, 5, 4, 22], ![46, -41, 13, -15, -5], ![-24, 22, -8, 6, -1]]]
  hmulB := by decide  
  f := ![![![4029, 1765, 1247, 856, 1475]], ![![2824, 1237, 874, 600, 1034]], ![![227, 99, 70, 48, 83]], ![![2162, 947, 669, 459, 791]], ![![762, 334, 236, 162, 279]]]
  g := ![![![6, -7, 3, -2, -1], ![-6, 9, -10, 4, -10], ![-15, 12, 5, 4, 22], ![37, -41, 13, -15, -5], ![-18, 22, -8, 6, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N0 : Nat.card (O ⧸ I179N0) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N0)

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := prime_ideal_of_norm_prime hp179.out _ NI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, -2, -1, 0, 3]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![5, -2, -1, 0, 3]] 
 ![![179, 0, 0, 0, 0], ![130, 1, 0, 0, 0], ![142, 0, 1, 0, 0], ![13, 0, 0, 1, 0], ![76, 0, 0, 0, 1]] where
  M :=![![![5, -2, -1, 0, 3], ![12, -5, -4, -8, -6], ![-12, 5, 3, -6, -18], ![-42, 19, 13, 19, 3], ![8, -3, -2, 4, 13]]]
  hmulB := by decide  
  f := ![![![151, 88, 13, 38, 15]], ![![110, 65, 10, 28, 12]], ![![122, 69, 11, 30, 12]], ![![11, 7, 0, 3, 0]], ![![64, 37, 6, 16, 7]]]
  g := ![![![1, -2, -1, 0, 3], ![10, -5, -4, -8, -6], ![2, 5, 3, -6, -18], ![-27, 19, 13, 19, 3], ![-2, -3, -2, 4, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1

def I179N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9665, 4202, 2975, 2032, 3525]] i)))

def SI179N2: IdealEqSpanCertificate' Table ![![9665, 4202, 2975, 2032, 3525]] 
 ![![179, 0, 0, 0, 0], ![141, 1, 0, 0, 0], ![173, 0, 1, 0, 0], ![84, 0, 0, 1, 0], ![97, 0, 0, 0, 1]] where
  M :=![![![9665, 4202, 2975, 2032, 3525], ![14100, 6129, 4340, 2964, 5142], ![10284, 4471, 3165, 2162, 3750], ![450, 197, 139, 95, 165], ![-1312, -571, -404, -276, -479]]]
  hmulB := by decide  
  f := ![![![-197, 68, 73, -66, -171]], ![![-159, 55, 59, -50, -135]], ![![-191, 67, 70, -60, -159]], ![![-78, 25, 31, -35, -75]], ![![-107, 37, 39, -38, -98]]]
  g := ![![![-8995, 4202, 2975, 2032, 3525], ![-13121, 6129, 4340, 2964, 5142], ![-9570, 4471, 3165, 2162, 3750], ![-421, 197, 139, 95, 165], ![1222, -571, -404, -276, -479]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N2 : Nat.card (O ⧸ I179N2) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N2)

lemma isPrimeI179N2 : Ideal.IsPrime I179N2 := prime_ideal_of_norm_prime hp179.out _ NI179N2

def I179N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, -24, 6, -6, -12]] i)))

def SI179N3: IdealEqSpanCertificate' Table ![![47, -24, 6, -6, -12]] 
 ![![179, 0, 0, 0, 0], ![145, 1, 0, 0, 0], ![138, 0, 1, 0, 0], ![36, 0, 0, 1, 0], ![130, 0, 0, 0, 1]] where
  M :=![![![47, -24, 6, -6, -12], ![-48, 77, -36, 24, -12], ![-24, 0, 53, 0, 84], ![192, -150, 18, -43, -78], ![-108, 84, -12, 24, 41]]]
  hmulB := by decide  
  f := ![![![-563, 300, 222, 822, 1032]], ![![-433, 233, 174, 666, 852]], ![![-402, 216, 161, 612, 780]], ![![-156, 78, 54, 149, 150]], ![![-430, 228, 168, 612, 761]]]
  g := ![![![25, -24, 6, -6, -12], ![-31, 77, -36, 24, -12], ![-102, 0, 53, 0, 84], ![174, -150, 18, -43, -78], ![-94, 84, -12, 24, 41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N3 : Nat.card (O ⧸ I179N3) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N3)

lemma isPrimeI179N3 : Ideal.IsPrime I179N3 := prime_ideal_of_norm_prime hp179.out _ NI179N3

def I179N4 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![69, -35, -25, -80, -91]] i)))

def SI179N4: IdealEqSpanCertificate' Table ![![69, -35, -25, -80, -91]] 
 ![![179, 0, 0, 0, 0], ![176, 1, 0, 0, 0], ![85, 0, 1, 0, 0], ![129, 0, 0, 1, 0], ![21, 0, 0, 0, 1]] where
  M :=![![![69, -35, -25, -80, -91], ![-364, 157, 90, -28, -298], ![-596, 282, 185, 360, 214], ![610, -245, -123, 345, 1015], ![396, -188, -124, -250, -161]]]
  hmulB := by decide  
  f := ![![![-3065, -955, -717, -506, -643]], ![![-3028, -955, -710, -504, -642]], ![![-1475, -455, -350, -242, -315]], ![![-2221, -682, -514, -363, -454]], ![![-351, -115, -85, -60, -80]]]
  g := ![![![115, -35, -25, -80, -91], ![-144, 157, 90, -28, -298], ![-653, 282, 185, 360, 214], ![-65, -245, -123, 345, 1015], ![445, -188, -124, -250, -161]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N4 : Nat.card (O ⧸ I179N4) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N4)

lemma isPrimeI179N4 : Ideal.IsPrime I179N4 := prime_ideal_of_norm_prime hp179.out _ NI179N4
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![7, -7, 3, -2, -1]] ![![5, -2, -1, 0, 3]]
  ![![-9, 1, 6, -4, -10]] where
 M := ![![![-9, 1, 6, -4, -10]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI179N1 : IdealMulLeCertificate' Table 
  ![![-9, 1, 6, -4, -10]] ![![9665, 4202, 2975, 2032, 3525]]
  ![![139, 59, 39, 28, 47]] where
 M := ![![![139, 59, 39, 28, 47]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI179N2 : IdealMulLeCertificate' Table 
  ![![139, 59, 39, 28, 47]] ![![47, -24, 6, -6, -12]]
  ![![3065, 955, 717, 506, 643]] where
 M := ![![![3065, 955, 717, 506, 643]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI179N3 : IdealMulLeCertificate' Table 
  ![![3065, 955, 717, 506, 643]] ![![69, -35, -25, -80, -91]]
  ![![179, 0, 0, 0, 0]] where
 M := ![![![-179, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC179 : ContainsPrimesAboveP 179 ![I179N0, I179N1, I179N2, I179N3, I179N4] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI179N0
    exact isPrimeI179N1
    exact isPrimeI179N2
    exact isPrimeI179N3
    exact isPrimeI179N4
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 179 (by decide) (𝕀 ⊙ MulI179N0 ⊙ MulI179N1 ⊙ MulI179N2 ⊙ MulI179N3)
instance hp181 : Fact (Nat.Prime 181) := {out := by norm_num}

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![92211, 40088, 28383, 19386, 33629]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![92211, 40088, 28383, 19386, 33629]] 
 ![![181, 0, 0, 0, 0], ![0, 181, 0, 0, 0], ![156, 177, 1, 0, 0], ![81, 153, 0, 1, 0], ![33, 75, 0, 0, 1]] where
  M :=![![![92211, 40088, 28383, 19386, 33629], ![134516, 58479, 41404, 28280, 49058], ![98116, 42653, 30199, 20626, 35782], ![4306, 1871, 1325, 903, 1567], ![-12524, -5443, -3854, -2632, -4567]]]
  hmulB := by decide  
  f := ![![![-241, 234, -101, 68, -29]], ![![-116, -119, 332, -8, 466]], ![![-316, 82, 237, 50, 428]], ![![-211, 10, 232, 25, 380]], ![![-89, -10, 121, 8, 188]]]
  g := ![![![-38760, -57856, 28383, 19386, 33629], ![-56542, -84399, 41404, 28280, 49058], ![-41240, -61558, 30199, 20626, 35782], ![-1808, -2698, 1325, 903, 1567], ![5263, 7856, -3854, -2632, -4567]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [7, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [161, 180], [0, 1]]
 g := ![![[158, 135], [125], [18, 145], [152], [70, 117], [63, 38], [1]], ![[173, 46], [125], [14, 36], [152], [83, 64], [27, 143], [1]]]
 h' := ![![[161, 180], [159, 42], [55, 135], [116, 114], [53, 40], [102, 152], [174, 161], [0, 1]], ![[0, 1], [43, 139], [70, 46], [8, 67], [158, 141], [139, 29], [31, 20], [161, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [72]]
 b := ![[], [179, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [7, 20, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6727, -3428, -2196, -3452, -5004]
  a := ![0, -4, -2, -14, 18]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![4387, 7120, -2196, -3452, -5004]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![311, 126, 91, 62, 103]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![311, 126, 91, 62, 103]] 
 ![![181, 0, 0, 0, 0], ![0, 181, 0, 0, 0], ![146, 76, 1, 0, 0], ![126, 180, 0, 1, 0], ![176, 12, 0, 0, 1]] where
  M :=![![![311, 126, 91, 62, 103], ![412, 217, 128, 100, 166], ![332, 121, 117, 62, 134], ![62, -23, -5, -5, -31], ![-68, -1, -8, -4, 5]]]
  hmulB := by decide  
  f := ![![![99, -40, -21, 48, 149]], ![![596, -273, -176, -244, -10]], ![![330, -147, -91, -66, 112]], ![![652, -295, -187, -207, 91]], ![![136, -57, -32, 32, 147]]]
  g := ![![![-215, -106, 91, 62, 103], ![-332, -163, 128, 100, 166], ![-266, -119, 117, 62, 134], ![38, 9, -5, -5, -31], ![4, 7, -8, -4, 5]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P1 : CertificateIrreducibleZModOfList' 181 2 2 7 [23, 144, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 180], [0, 1]]
 g := ![![[22, 172], [14], [9, 79], [147], [37, 148], [81, 102], [1]], ![[51, 9], [14], [36, 102], [147], [83, 33], [54, 79], [1]]]
 h' := ![![[37, 180], [173, 57], [155, 75], [78, 160], [54, 50], [128, 94], [158, 37], [0, 1]], ![[0, 1], [110, 124], [34, 106], [25, 21], [94, 131], [167, 87], [79, 144], [37, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [72]]
 b := ![[], [58, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N1 : CertifiedPrimeIdeal' SI181N1 181 where
  n := 2
  hpos := by decide
  P := [23, 144, 1]
  hirr := P181P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2868, -1894, 1041, -436, -2594]
  a := ![13, -7, 4, -6, -23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2002, 158, 1041, -436, -2594]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N1 B_one_repr
lemma NI181N1 : Nat.card (O ⧸ I181N1) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N1

def I181N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1791, -783, -548, -378, -650]] i)))

def SI181N2: IdealEqSpanCertificate' Table ![![-1791, -783, -548, -378, -650]] 
 ![![181, 0, 0, 0, 0], ![37, 1, 0, 0, 0], ![130, 0, 1, 0, 0], ![20, 0, 0, 1, 0], ![82, 0, 0, 0, 1]] where
  M :=![![![-1791, -783, -548, -378, -650], ![-2600, -1145, -810, -552, -968], ![-1936, -805, -593, -394, -688], ![-76, -54, -6, -23, -10], ![240, 115, 64, 54, 77]]]
  hmulB := by decide  
  f := ![![![-4715, 2173, 1374, 1890, 38]], ![![-963, 446, 284, 422, 70]], ![![-3262, 1505, 953, 1334, 72]], ![![-432, 194, 118, 89, -142]], ![![-2222, 1023, 646, 874, -11]]]
  g := ![![![880, -783, -548, -378, -650], ![1301, -1145, -810, -552, -968], ![935, -805, -593, -394, -688], ![22, -54, -6, -23, -10], ![-109, 115, 64, 54, 77]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N2 : Nat.card (O ⧸ I181N2) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N2)

lemma isPrimeI181N2 : Ideal.IsPrime I181N2 := prime_ideal_of_norm_prime hp181.out _ NI181N2
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![92211, 40088, 28383, 19386, 33629]] ![![311, 126, 91, 62, 103]]
  ![![53532193, 23272518, 16477314, 11254182, 19522842]] where
 M := ![![![53532193, 23272518, 16477314, 11254182, 19522842]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI181N1 : IdealMulLeCertificate' Table 
  ![![53532193, 23272518, 16477314, 11254182, 19522842]] ![![-1791, -783, -548, -378, -650]]
  ![![181, 0, 0, 0, 0]] where
 M := ![![![-184454620119, -80189576997, -56775491750, -38778273324, -67269397892]]]
 hmul := by decide  
 g := ![![![![-1019086299, -443036337, -313676750, -214244604, -371654132]]]]
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


lemma PB187I4_primes (p : ℕ) :
  p ∈ Set.range ![157, 163, 167, 173, 179, 181] ↔ Nat.Prime p ∧ 151 < p ∧ p ≤ 186 := by
  rw [← List.mem_ofFn']
  convert primes_range 151 186 (by omega)

def PB187I4 : PrimesBelowBoundCertificateInterval O 151 186 187 where
  m := 6
  g := ![1, 1, 1, 3, 5, 3]
  P := ![157, 163, 167, 173, 179, 181]
  hP := PB187I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I157N0]
    · exact ![I163N0]
    · exact ![I167N0]
    · exact ![I173N0, I173N1, I173N2]
    · exact ![I179N0, I179N1, I179N2, I179N3, I179N4]
    · exact ![I181N0, I181N1, I181N2]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![95388992557]
    · exact ![115063617043]
    · exact ![129891985607]
    · exact ![29929, 29929, 173]
    · exact ![179, 179, 179, 179, 179]
    · exact ![32761, 32761, 181]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
      exact NI173N1
      exact NI173N2
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
      exact NI179N1
      exact NI179N2
      exact NI179N3
      exact NI179N4
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
      exact NI181N2
  β := ![I173N2, I179N0, I179N1, I179N2, I179N3, I179N4, I181N2]
  Il := ![[], [], [], [I173N2], [I179N0, I179N1, I179N2, I179N3, I179N4], [I181N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
