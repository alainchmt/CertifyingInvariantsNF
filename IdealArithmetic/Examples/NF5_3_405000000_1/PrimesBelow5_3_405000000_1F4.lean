
import IdealArithmetic.Examples.NF5_3_405000000_1.RI5_3_405000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![150461, -384825, 65800, -14765, 49116]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![150461, -384825, 65800, -14765, 49116]] 
 ![![157, 0, 0, 0, 0], ![0, 157, 0, 0, 0], ![0, 0, 157, 0, 0], ![0, 0, 0, 157, 0], ![92, 7, 37, 151, 1]] where
  M :=![![![150461, -384825, 65800, -14765, 49116], ![29530, -75533, 12924, -2902, 9642], ![5804, -14842, 2539, -556, 1872], ![1112, -2796, 338, -93, 408], ![37810, -96726, 16568, -3756, 12401]]]
  hmulB := by decide  
  f := ![![![35, -203, 10, -9, 18]], ![![18, -55, -68, -8, -18]], ![![16, 74, -241, -16, -84]], ![![32, 320, -730, -41, -264]], ![![56, 205, -759, -49, -265]]]
  g := ![![![-27823, -4641, -11156, -47333, 49116], ![-5462, -911, -2190, -9292, 9642], ![-1060, -178, -425, -1804, 1872], ![-232, -36, -94, -393, 408], ![-7026, -1169, -2817, -11951, 12401]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 4 2 7 [43, 83, 132, 71, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [149, 74, 57, 100], [123, 5, 134, 55], [128, 77, 123, 2], [0, 1]]
 g := ![![[44, 95, 135, 138], [135, 103, 141], [61, 114, 110, 138], [133, 27, 56, 56], [13, 2, 110, 17], [1], []], ![[18, 68, 44, 98, 37, 130], [69, 49, 19], [145, 104, 50, 123, 32, 82], [16, 68, 116, 39, 28, 81], [101, 72, 114, 39, 108, 118], [91, 89, 145], [111, 50, 109]], ![[98, 62, 52, 148, 0, 70], [67, 0, 115], [62, 129, 155, 108, 46, 28], [66, 79, 9, 81, 88, 85], [87, 73, 28, 19, 18, 7], [84, 108, 48], [39, 140, 42]], ![[0, 73, 37, 142, 88, 53], [80, 13, 89], [131, 68, 155, 23, 3, 114], [49, 61, 13, 40, 38, 88], [93, 115, 90, 89, 98, 26], [105, 10, 105], [141, 51, 4]]]
 h' := ![![[149, 74, 57, 100], [79, 87, 57, 83], [46, 19, 83, 112], [90, 97, 124, 83], [69, 56, 55, 128], [114, 74, 25, 86], [0, 0, 1], [0, 1]], ![[123, 5, 134, 55], [65, 26, 25, 86], [7, 68, 99, 126], [63, 67, 81, 91], [114, 123, 50, 48], [13, 107, 113, 102], [1, 13, 72, 107], [149, 74, 57, 100]], ![[128, 77, 123, 2], [34, 9, 46, 12], [106, 87, 34, 127], [123, 132, 71, 106], [90, 126, 137, 75], [144, 118, 24, 104], [107, 137, 128, 26], [123, 5, 134, 55]], ![[0, 1], [0, 35, 29, 133], [92, 140, 98, 106], [114, 18, 38, 34], [111, 9, 72, 63], [149, 15, 152, 22], [116, 7, 113, 24], [128, 77, 123, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [75, 90, 22], []]
 b := ![[], [], [141, 78, 60, 31], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 4
  hpos := by decide
  P := [43, 83, 132, 71, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-759150350, 3176300001, -4263630512, 432312325, 1180198341]
  a := ![5, -6, -8, 4, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-696416546, -32389098, -305292797, -1132341638, 1180198341]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 607573201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-35, 203, -10, 9, -18]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![-35, 203, -10, 9, -18]] 
 ![![157, 0, 0, 0, 0], ![34, 1, 0, 0, 0], ![100, 0, 1, 0, 0], ![54, 0, 0, 1, 0], ![69, 0, 0, 0, 1]] where
  M :=![![![-35, 203, -10, 9, -18], ![-18, 55, 68, 8, 18], ![-16, -74, 241, 16, 84], ![-32, -320, 730, 41, 264], ![-22, -188, 460, 26, 163]]]
  hmulB := by decide  
  f := ![![![-150461, 384825, -65800, 14765, -49116]], ![![-32772, 83819, -14332, 3216, -10698]], ![![-95872, 245206, -41927, 9408, -31296]], ![![-51758, 132378, -22634, 5079, -16896]], ![![-66367, 169743, -29024, 6513, -21665]]]
  g := ![![![-33, 203, -10, 9, -18], ![-66, 55, 68, 8, 18], ![-180, -74, 241, 16, 84], ![-526, -320, 730, 41, 264], ![-333, -188, 460, 26, 163]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![150461, -384825, 65800, -14765, 49116]] ![![-35, 203, -10, 9, -18]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13, -14, 49, -51, 58]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![-13, -14, 49, -51, 58]] 
 ![![163, 0, 0, 0, 0], ![0, 163, 0, 0, 0], ![94, 17, 1, 0, 0], ![32, 131, 0, 1, 0], ![30, 50, 0, 0, 1]] where
  M :=![![![-13, -14, 49, -51, 58], ![102, -347, 355, 35, -190], ![-70, 932, -1952, 665, -170], ![-1330, 1940, 1397, -2942, 3650], ![534, -3344, 5667, -1345, -341]]]
  hmulB := by decide  
  f := ![![![349, -7954, 12833, 623, 4762]], ![![-1246, -17453, 36773, 2063, 13262]], ![![46, -6715, 11899, 612, 4368]], ![![-1008, -16493, 34026, 1891, 12296]], ![![-364, -7390, 14871, 817, 5387]]]
  g := ![![![-29, 18, 49, -51, 58], ![-176, -9, 355, 35, -190], ![1026, -273, -1952, 665, -170], ![-908, 1111, 1397, -2942, 3650], ![-2938, 574, 5667, -1345, -341]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [106, 103, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [60, 162], [0, 1]]
 g := ![![[104, 51], [65, 25], [77], [15], [26], [19, 14], [1]], ![[67, 112], [98, 138], [77], [15], [26], [44, 149], [1]]]
 h' := ![![[60, 162], [119, 41], [62, 158], [20, 27], [119, 34], [105, 134], [57, 60], [0, 1]], ![[0, 1], [134, 122], [88, 5], [10, 136], [40, 129], [158, 29], [71, 103], [60, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [132]]
 b := ![[], [139, 66]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [106, 103, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![346, -11518, 15421, -4371, 1734]
  a := ![-6, -55, 11, -7, 21]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-8352, 1302, 15421, -4371, 1734]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-541, 1379, -236, 53, -176]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![-541, 1379, -236, 53, -176]] 
 ![![163, 0, 0, 0, 0], ![0, 163, 0, 0, 0], ![91, 75, 1, 0, 0], ![21, 8, 0, 1, 0], ![30, 32, 0, 0, 1]] where
  M :=![![![-541, 1379, -236, 53, -176], ![-106, 269, -46, 10, -34], ![-20, 50, -7, 2, -8], ![-4, 16, -16, 5, -4], ![-138, 354, -66, 12, -41]]]
  hmulB := by decide  
  f := ![![![59, -373, 58, -13, 46]], ![![26, -151, 2, -8, 14]], ![![45, -278, 33, -11, 32]], ![![9, -55, 6, -2, 6]], ![![16, -98, 10, -4, 11]]]
  g := ![![![154, 149, -236, 53, -176], ![30, 29, -46, 10, -34], ![5, 5, -7, 2, -8], ![9, 8, -16, 5, -4], ![42, 40, -66, 12, -41]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P1 : CertificateIrreducibleZModOfList' 163 2 2 7 [12, 116, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [47, 162], [0, 1]]
 g := ![![[64, 6], [132, 35], [118], [57], [119], [5, 90], [1]], ![[20, 157], [147, 128], [118], [57], [119], [160, 73], [1]]]
 h' := ![![[47, 162], [46, 150], [87, 144], [6, 66], [53, 63], [103, 114], [151, 47], [0, 1]], ![[0, 1], [87, 13], [9, 19], [11, 97], [80, 100], [82, 49], [78, 116], [47, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62]]
 b := ![[], [5, 31]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N1 : CertifiedPrimeIdeal' SI163N1 163 where
  n := 2
  hpos := by decide
  P := [12, 116, 1]
  hirr := P163P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![103, -452, 206, -88, -98]
  a := ![1, -3, -1, 0, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-85, -74, 206, -88, -98]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N1 B_one_repr
lemma NI163N1 : Nat.card (O ⧸ I163N1) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N1

def I163N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![369, 4641, -9893, -558, -3564]] i)))

def SI163N2: IdealEqSpanCertificate' Table ![![369, 4641, -9893, -558, -3564]] 
 ![![163, 0, 0, 0, 0], ![71, 1, 0, 0, 0], ![12, 0, 1, 0, 0], ![126, 0, 0, 1, 0], ![151, 0, 0, 0, 1]] where
  M :=![![![369, 4641, -9893, -558, -3564], ![1116, 13509, -29109, -1649, -10476], ![3298, 39722, -85722, -4859, -30846], ![9718, 116964, -252469, -14312, -90846], ![6112, 73584, -158821, -9003, -57149]]]
  hmulB := by decide  
  f := ![![![-263, 473, 357, -290, 198]], ![![-111, 196, 164, -123, 78]], ![![-26, 78, -48, -3, 18]], ![![-240, 382, 405, -342, 270]], ![![-215, 303, 528, -297, 145]]]
  g := ![![![2442, 4641, -9893, -558, -3564], ![7245, 13509, -29109, -1649, -10476], ![21360, 39722, -85722, -4859, -30846], ![62920, 116964, -252469, -14312, -90846], ![39579, 73584, -158821, -9003, -57149]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N2 : Nat.card (O ⧸ I163N2) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N2)

lemma isPrimeI163N2 : Ideal.IsPrime I163N2 := prime_ideal_of_norm_prime hp163.out _ NI163N2
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![-13, -14, 49, -51, 58]] ![![-541, 1379, -236, 53, -176]]
  ![![-263, 473, 357, -290, 198]] where
 M := ![![![-263, 473, 357, -290, 198]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI163N1 : IdealMulLeCertificate' Table 
  ![![-263, 473, 357, -290, 198]] ![![369, 4641, -9893, -558, -3564]]
  ![![163, 0, 0, 0, 0]] where
 M := ![![![163, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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


def P167P0 : CertificateIrreducibleZModOfList' 167 5 2 7 [114, 137, 25, 153, 61, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [89, 101, 151, 88, 23], [108, 36, 83, 93, 116], [36, 1, 95, 22, 66], [40, 28, 5, 131, 129], [0, 1]]
 g := ![![[71, 72, 46, 132, 14], [0, 28, 71, 37, 33], [133, 96, 10, 67, 18], [33, 107, 91, 97], [123, 81, 101, 47], [1], []], ![[61, 50, 1, 9, 96, 143, 78, 166], [30, 0, 67, 65, 122, 145, 81, 159], [151, 49, 119, 30, 105, 72, 65, 82], [149, 89, 154, 107], [24, 131, 36, 100], [12, 60, 25, 11, 12, 130, 25, 103], [84, 97, 2, 28]], ![[36, 13, 34, 95, 47, 100, 86, 85], [9, 48, 138, 149, 113, 38, 90, 6], [79, 81, 53, 79, 164, 92, 46, 42], [97, 94, 96, 144], [26, 115, 66, 108], [120, 142, 37, 99, 160, 108, 101, 127], [59, 18, 22, 96]], ![[72, 153, 145, 5, 48, 166, 152, 3], [155, 122, 91, 47, 107, 54, 48, 50], [19, 99, 88, 24, 12, 13, 15, 122], [94, 25, 82, 96], [54, 134, 47, 127], [90, 31, 62, 158, 88, 156, 49, 48], [111, 60, 46, 14]], ![[13, 34, 36, 69, 133, 12, 138, 155], [166, 133, 141, 150, 117, 12, 31, 37], [34, 103, 95, 12, 120, 142, 31, 5], [121, 51, 22, 147], [106, 50, 118, 9], [43, 60, 145, 104, 12, 101, 96, 20], [7, 93, 156, 108]]]
 h' := ![![[89, 101, 151, 88, 23], [0, 37, 92, 10, 66], [35, 62, 28, 40, 130], [154, 60, 1, 107, 39], [143, 141, 119, 25, 40], [53, 30, 142, 14, 106], [0, 0, 1], [0, 1]], ![[108, 36, 83, 93, 116], [99, 40, 34, 43, 14], [34, 99, 148, 153, 30], [56, 150, 116, 5, 131], [141, 10, 146, 4, 21], [120, 37, 3, 94, 157], [15, 88, 86, 35, 112], [89, 101, 151, 88, 23]], ![[36, 1, 95, 22, 66], [42, 152, 78, 127, 80], [106, 127, 72, 71, 7], [78, 164, 104, 105, 3], [92, 125, 71, 131, 155], [102, 129, 68, 48, 38], [95, 146, 83, 124, 49], [108, 36, 83, 93, 116]], ![[40, 28, 5, 131, 129], [162, 48, 11, 0, 47], [102, 24, 19, 83, 122], [49, 79, 77, 101, 91], [54, 151, 126, 163, 51], [71, 89, 64, 150, 36], [165, 69, 121, 109, 146], [36, 1, 95, 22, 66]], ![[0, 1], [124, 57, 119, 154, 127], [84, 22, 67, 154, 45], [44, 48, 36, 16, 70], [155, 74, 39, 11, 67], [81, 49, 57, 28, 164], [134, 31, 43, 66, 27], [40, 28, 5, 131, 129]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [123, 54, 84, 138], [], [], []]
 b := ![[], [62, 64, 93, 118, 161], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 5
  hpos := by decide
  P := [114, 137, 25, 153, 61, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![282101989156, -25810458427760, 61295790614955, -24090371588195, 10359455500055]
  a := ![-8, 28, 13, -9, 25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1689233468, -154553643280, 367040662365, -144253722085, 62032667665]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![39, -167, 58, -7, 8]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![39, -167, 58, -7, 8]] 
 ![![173, 0, 0, 0, 0], ![0, 173, 0, 0, 0], ![23, 106, 1, 0, 0], ![157, 32, 0, 1, 0], ![62, 82, 0, 0, 1]] where
  M :=![![![39, -167, 58, -7, 8], ![14, -7, -116, 56, -26], ![-112, 230, -73, -176, 284], ![352, -1600, 2258, -289, -488], ![278, -414, -296, 606, -745]]]
  hmulB := by decide  
  f := ![![![-4031, -49013, 105592, 5981, 38002]], ![![-11962, -144077, 310948, 17626, 111890]], ![![-8069, -97247, 209855, 11895, 75514]], ![![-6471, -78353, 168934, 9572, 60794]], ![![-7492, -90400, 195036, 11054, 70183]]]
  g := ![![![-4, -39, 58, -7, 8], ![-26, 73, -116, 56, -26], ![67, -56, -73, -176, 284], ![139, -1108, 2258, -289, -488], ![-242, 420, -296, 606, -745]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [134, 31, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [142, 172], [0, 1]]
 g := ![![[48, 113], [35], [123, 34], [107, 124], [4], [142, 96], [1]], ![[5, 60], [35], [107, 139], [69, 49], [4], [107, 77], [1]]]
 h' := ![![[142, 172], [114, 74], [126, 30], [21, 131], [160, 41], [2, 171], [39, 142], [0, 1]], ![[0, 1], [69, 99], [61, 143], [112, 42], [100, 132], [64, 2], [135, 31], [142, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [162]]
 b := ![[], [131, 81]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [134, 31, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8124, -45728, 72068, -10984, -6848]
  a := ![10, -11, -15, 12, -31]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2888, -39144, 72068, -10984, -6848]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6553, -48869, 8790, -1651, 6428]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![6553, -48869, 8790, -1651, 6428]] 
 ![![173, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![29, 0, 1, 0, 0], ![171, 0, 0, 1, 0], ![71, 0, 0, 0, 1]] where
  M :=![![![6553, -48869, 8790, -1651, 6428], ![3302, -22461, 4030, -764, 2950], ![1528, -10026, 1797, -342, 1316], ![684, -4420, 792, -151, 580], ![598, -5586, 1010, -186, 737]]]
  hmulB := by decide  
  f := ![![![-169, -1919, 4188, 197, 1522]], ![![-14, -167, 362, 18, 130]], ![![-37, -413, 901, 47, 330]], ![![-195, -2177, 4764, 216, 1738]], ![![-81, -981, 2126, 99, 759]]]
  g := ![![![948, -48869, 8790, -1651, 6428], ![446, -22461, 4030, -764, 2950], ![201, -10026, 1797, -342, 1316], ![89, -4420, 792, -151, 580], ![103, -5586, 1010, -186, 737]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1

def I173N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 13, -18, 3, 4]] i)))

def SI173N2: IdealEqSpanCertificate' Table ![![-3, 13, -18, 3, 4]] 
 ![![173, 0, 0, 0, 0], ![110, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![111, 0, 0, 1, 0], ![36, 0, 0, 0, 1]] where
  M :=![![![-3, 13, -18, 3, 4], ![-6, -13, 58, -32, 26], ![64, -174, 125, 70, -140], ![-140, 764, -1224, 265, 140], ![-166, 322, -26, -274, 421]]]
  hmulB := by decide  
  f := ![![![486747, -3117269, 558324, -106541, 408986]], ![![310724, -1989953, 356414, -68012, 261082]], ![![28674, -183628, 32889, -6276, 24092]], ![![312541, -2001599, 358500, -68410, 262610]], ![![101642, -650952, 116590, -22248, 85405]]]
  g := ![![![-10, 13, -18, 3, 4], ![20, -13, 58, -32, 26], ![88, -174, 125, 70, -140], ![-615, 764, -1224, 265, 140], ![-116, 322, -26, -274, 421]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N2 : Nat.card (O ⧸ I173N2) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N2)

lemma isPrimeI173N2 : Ideal.IsPrime I173N2 := prime_ideal_of_norm_prime hp173.out _ NI173N2

def I173N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-435, 1087, -144, 1, -96]] i)))

def SI173N3: IdealEqSpanCertificate' Table ![![-435, 1087, -144, 1, -96]] 
 ![![173, 0, 0, 0, 0], ![118, 1, 0, 0, 0], ![89, 0, 1, 0, 0], ![51, 0, 0, 1, 0], ![112, 0, 0, 0, 1]] where
  M :=![![![-435, 1087, -144, 1, -96], ![-2, -49, 226, 46, -186], ![-92, 834, -1585, 506, -96], ![-1012, 1304, 1488, -2405, 2844], ![366, -2470, 4446, -968, -431]]]
  hmulB := by decide  
  f := ![![![-1623557, 10372421, -1867042, 353849, -1363866]], ![![-1111488, 7101071, -1278334, 242238, -933762]], ![![-837009, 5347759, -963063, 182399, -703326]], ![![-479343, 3063455, -552814, 104398, -403266]], ![![-1052238, 6723108, -1211034, 229286, -884303]]]
  g := ![![![-608, 1087, -144, 1, -96], ![24, -49, 226, 46, -186], ![159, 834, -1585, 506, -96], ![-2793, 1304, 1488, -2405, 2844], ![-36, -2470, 4446, -968, -431]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N3 : Nat.card (O ⧸ I173N3) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N3)

lemma isPrimeI173N3 : Ideal.IsPrime I173N3 := prime_ideal_of_norm_prime hp173.out _ NI173N3
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![39, -167, 58, -7, 8]] ![![6553, -48869, 8790, -1651, 6428]]
  ![![-207247, 1249840, -223438, 42932, -163794]] where
 M := ![![![-207247, 1249840, -223438, 42932, -163794]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI173N1 : IdealMulLeCertificate' Table 
  ![![-207247, 1249840, -223438, 42932, -163794]] ![![-3, 13, -18, 3, 4]]
  ![![1993, -5539, 1292, -745, 1378]] where
 M := ![![![1993, -5539, 1292, -745, 1378]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI173N2 : IdealMulLeCertificate' Table 
  ![![1993, -5539, 1292, -745, 1378]] ![![-435, 1087, -144, 1, -96]]
  ![![173, 0, 0, 0, 0]] where
 M := ![![![283547, -859810, 1431402, 858772, -1997804]]]
 hmul := by decide  
 g := ![![![![1639, -4970, 8274, 4964, -11548]]]]
 hle2 := by decide  


def PBC173 : ContainsPrimesAboveP 173 ![I173N0, I173N1, I173N2, I173N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
    exact isPrimeI173N1
    exact isPrimeI173N2
    exact isPrimeI173N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 173 (by decide) (𝕀 ⊙ MulI173N0 ⊙ MulI173N1 ⊙ MulI173N2)
instance hp179 : Fact (Nat.Prime 179) := {out := by norm_num}

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6455, -16541, 2896, -669, 2130]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![6455, -16541, 2896, -669, 2130]] 
 ![![179, 0, 0, 0, 0], ![0, 179, 0, 0, 0], ![0, 0, 179, 0, 0], ![15, 113, 66, 1, 0], ![138, 140, 91, 0, 1]] where
  M :=![![![6455, -16541, 2896, -669, 2130], ![1338, -3403, 622, -26, 246], ![52, 302, -1267, 182, 336], ![-364, -928, 3872, -2303, 1764], ![2326, -6844, 4022, -248, -667]]]
  hmulB := by decide  
  f := ![![![52567, -335685, 60230, -11467, 44076]], ![![22934, -146671, 26598, -4988, 19350]], ![![9976, -64442, 12515, -2126, 8772]], ![![22585, -144646, 26498, -4898, 19170]], ![![63572, -406514, 73653, -13830, 53609]]]
  g := ![![![-1550, -1336, -820, -669, 2130], ![-180, -195, -112, -26, 246], ![-274, -376, -245, 182, 336], ![-1169, 69, -26, -2303, 1764], ![548, 640, 453, -248, -667]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 3 2 7 [113, 45, 168, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 49, 97], [175, 129, 82], [0, 1]]
 g := ![![[106, 35, 87], [3, 136, 93], [171, 4], [34, 155], [154, 111, 74], [76, 11, 1], []], ![[156, 166, 48, 109], [77, 30, 169, 99], [135, 29], [164, 151], [165, 79, 131, 164], [96, 13, 155, 134], [56, 101]], ![[121, 139, 163, 1], [85, 50, 117, 36], [109, 138], [119, 108], [52, 37, 63, 126], [24, 171, 60, 161], [71, 101]]]
 h' := ![![[15, 49, 97], [19, 126, 83], [45, 64, 56], [6, 13, 177], [140, 54, 79], [4, 170, 49], [0, 0, 1], [0, 1]], ![[175, 129, 82], [140, 100, 17], [53, 86, 7], [56, 145, 108], [144, 63, 35], [110, 157, 78], [162, 67, 129], [15, 49, 97]], ![[0, 1], [98, 132, 79], [150, 29, 116], [37, 21, 73], [136, 62, 65], [65, 31, 52], [48, 112, 49], [175, 129, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [176, 25], []]
 b := ![[], [142, 130, 116], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 3
  hpos := by decide
  P := [113, 45, 168, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6572181, 33664182, -51606534, 9187808, 7492098]
  a := ![-6, 6, 10, -16, 18]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6582675, -11471798, -7484820, 9187808, 7492098]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 5735339 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![52567, -335685, 60230, -11467, 44076]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![52567, -335685, 60230, -11467, 44076]] 
 ![![179, 0, 0, 0, 0], ![0, 179, 0, 0, 0], ![131, 113, 1, 0, 0], ![54, 71, 0, 1, 0], ![13, 131, 0, 0, 1]] where
  M :=![![![52567, -335685, 60230, -11467, 44076], ![22934, -146671, 26598, -4988, 19350], ![9976, -64442, 12515, -2126, 8772], ![4252, -29364, 8128, -777, 4788], ![6566, -43314, 9562, -1338, 6271]]]
  hmulB := by decide  
  f := ![![![6455, -16541, 2896, -669, 2130]], ![![1338, -3403, 622, -26, 246]], ![![5569, -14252, 2505, -505, 1716]], ![![2476, -6345, 1142, -225, 750]], ![![1461, -3730, 688, -69, 331]]]
  g := ![![![-43527, -67606, 60230, -11467, 44076], ![-19238, -29793, 26598, -4988, 19350], ![-9099, -13837, 12515, -2126, 8772], ![-6038, -8491, 8128, -777, 4788], ![-7013, -10337, 9562, -1338, 6271]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P1 : CertificateIrreducibleZModOfList' 179 2 2 7 [159, 77, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [102, 178], [0, 1]]
 g := ![![[23, 156], [52, 126], [125], [158], [57, 93], [59, 22], [1]], ![[4, 23], [16, 53], [125], [158], [56, 86], [155, 157], [1]]]
 h' := ![![[102, 178], [145, 131], [177, 157], [177, 150], [66, 115], [106, 56], [20, 102], [0, 1]], ![[0, 1], [82, 48], [81, 22], [83, 29], [161, 64], [90, 123], [42, 77], [102, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [1, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N1 : CertifiedPrimeIdeal' SI179N1 179 where
  n := 2
  hpos := by decide
  P := [159, 77, 1]
  hirr := P179P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-871, -28097, 69440, -17751, 17872]
  a := ![-6, 18, 16, -5, 31]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-46767, -50032, 69440, -17751, 17872]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N1 B_one_repr
lemma NI179N1 : Nat.card (O ⧸ I179N1) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![6455, -16541, 2896, -669, 2130]] ![![52567, -335685, 60230, -11467, 44076]]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-507, -6106, 13179, 747, 4742]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![-507, -6106, 13179, 747, 4742]] 
 ![![181, 0, 0, 0, 0], ![0, 181, 0, 0, 0], ![141, 100, 1, 0, 0], ![18, 96, 0, 1, 0], ![2, 135, 0, 0, 1]] where
  M :=![![![-507, -6106, 13179, 747, 4742], ![-1494, -17981, 38813, 2201, 13966], ![-4402, -52956, 114316, 6479, 41138], ![-12958, -155996, 336723, 19082, 121150], ![-8150, -98128, 211805, 12013, 76205]]]
  hmulB := by decide  
  f := ![![![-12771, 89302, -16035, 3031, -11734]], ![![-6062, 40227, -7211, 1371, -5282]], ![![-13313, 91890, -16493, 3122, -12072]], ![![-4492, 30260, -5427, 1030, -3974]], ![![-4670, 31049, -5566, 1058, -4077]]]
  g := ![![![-10396, -11248, 13179, 747, 4742], ![-30617, -33127, 38813, 2201, 13966], ![-90176, -97570, 114316, 6479, 41138], ![-265617, -287378, 336723, 19082, 121150], ![-167079, -180771, 211805, 12013, 76205]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [123, 99, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [82, 180], [0, 1]]
 g := ![![[120, 27], [33], [85, 4], [11], [155, 111], [142, 27], [1]], ![[162, 154], [33], [51, 177], [11], [26, 70], [3, 154], [1]]]
 h' := ![![[82, 180], [143, 99], [43, 157], [75, 2], [121, 98], [91, 103], [58, 82], [0, 1]], ![[0, 1], [116, 82], [66, 24], [58, 179], [12, 83], [30, 78], [85, 99], [82, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [131, 116]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [123, 99, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![315, -1587, 1892, -229, -214]
  a := ![-2, -2, 3, -3, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1447, -773, 1892, -229, -214]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, -30, -28, -12, 40]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![-3, -30, -28, -12, 40]] 
 ![![181, 0, 0, 0, 0], ![0, 181, 0, 0, 0], ![173, 124, 1, 0, 0], ![87, 1, 0, 1, 0], ![34, 23, 0, 0, 1]] where
  M :=![![![-3, -30, -28, -12, 40], ![24, -187, 294, -84, 8], ![168, -176, -367, 446, -488], ![-892, 3012, -3230, -283, 1700], ![-296, -232, 1910, -1304, 1105]]]
  hmulB := by decide  
  f := ![![![-1386119, 3545094, -606176, 136020, -452456]], ![![-272040, 695745, -118950, 26696, -88792]], ![![-1511519, 3865802, -661003, 148326, -493384]], ![![-667817, 1707987, -292048, 65533, -217988]], ![![-296870, 759263, -129824, 29132, -96903]]]
  g := ![![![25, 14, -28, -12, 40], ![-242, -203, 294, -84, 8], ![229, 310, -367, 446, -488], ![2899, 2015, -3230, -283, 1700], ![-1408, -1443, 1910, -1304, 1105]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P1 : CertificateIrreducibleZModOfList' 181 2 2 7 [76, 144, 1] where
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
 g := ![![[40, 36], [176], [129, 165], [39], [5, 108], [141, 102], [1]], ![[105, 145], [176], [80, 16], [39], [19, 73], [114, 79], [1]]]
 h' := ![![[37, 180], [13, 6], [151, 30], [75, 76], [163, 43], [144, 164], [105, 37], [0, 1]], ![[0, 1], [54, 175], [175, 151], [172, 105], [125, 138], [58, 17], [26, 144], [37, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [95]]
 b := ![[], [162, 138]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N1 : CertifiedPrimeIdeal' SI181N1 181 where
  n := 2
  hpos := by decide
  P := [76, 144, 1]
  hirr := P181P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9406, -52949, 83714, -10422, -7413]
  a := ![-10, 13, 20, -14, 33]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-73560, -56644, 83714, -10422, -7413]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N1 B_one_repr
lemma NI181N1 : Nat.card (O ⧸ I181N1) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N1

def I181N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![499, 5411, -12070, -693, -4330]] i)))

def SI181N2: IdealEqSpanCertificate' Table ![![499, 5411, -12070, -693, -4330]] 
 ![![181, 0, 0, 0, 0], ![138, 1, 0, 0, 0], ![142, 0, 1, 0, 0], ![133, 0, 0, 1, 0], ![126, 0, 0, 0, 1]] where
  M :=![![![499, 5411, -12070, -693, -4330], ![1386, 16433, -35638, -2024, -12818], ![4048, 48610, -105001, -5954, -37780], ![11908, 143260, -309272, -17533, -111284], ![7494, 90104, -194550, -11030, -70003]]]
  hmulB := by decide  
  f := ![![![173, 253, -1604, 715, -328]], ![![124, 209, -1226, 532, -230]], ![![162, 84, -1101, 544, -296]], ![![161, 333, -1692, 794, -420]], ![![32, 492, -1478, 486, -67]]]
  g := ![![![8870, 5411, -12070, -693, -4330], ![25848, 16433, -35638, -2024, -12818], ![76012, 48610, -105001, -5954, -37780], ![223825, 143260, -309272, -17533, -111284], ![140810, 90104, -194550, -11030, -70003]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N2 : Nat.card (O ⧸ I181N2) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N2)

lemma isPrimeI181N2 : Ideal.IsPrime I181N2 := prime_ideal_of_norm_prime hp181.out _ NI181N2
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![-507, -6106, 13179, 747, 4742]] ![![-3, -30, -28, -12, 40]]
  ![![-907, -12652, 26749, 1853, 9330]] where
 M := ![![![-907, -12652, 26749, 1853, 9330]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI181N1 : IdealMulLeCertificate' Table 
  ![![-907, -12652, 26749, 1853, 9330]] ![![499, 5411, -12070, -693, -4330]]
  ![![181, 0, 0, 0, 0]] where
 M := ![![![182276231, 2193581897, -4735064799, -268425896, -1703813816]]]
 hmul := by decide  
 g := ![![![![1007051, 12119237, -26160579, -1483016, -9413336]]]]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 1227, -2657, -158, -972]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![107, 1227, -2657, -158, -972]] 
 ![![191, 0, 0, 0, 0], ![0, 191, 0, 0, 0], ![0, 0, 191, 0, 0], ![0, 0, 0, 191, 0], ![151, 175, 190, 43, 1]] where
  M :=![![![107, 1227, -2657, -158, -972], ![316, 3679, -7995, -397, -2892], ![794, 11090, -23540, -1417, -8166], ![2834, 30624, -66655, -4374, -24834], ![1936, 19416, -43003, -2043, -16207]]]
  hmulB := by decide  
  f := ![![![-3329, 9767, -1687, 366, -1254]], ![![-732, 2419, -421, 89, -312]], ![![-178, 694, -122, 25, -90]], ![![-50, 232, -41, 8, -30]], ![![-3495, 10692, -1852, 398, -1375]]]
  g := ![![![769, 897, 953, 218, -972], ![2288, 2669, 2835, 649, -2892], ![6460, 7540, 8000, 1831, -8166], ![19648, 22914, 24355, 5568, -24834], ![12823, 14951, 15897, 3638, -16207]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 4 2 7 [133, 183, 153, 174, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [156, 35, 131, 121], [37, 165, 5, 177], [15, 181, 55, 84], [0, 1]]
 g := ![![[141, 105, 140, 138], [35, 111, 73, 162], [135, 151, 23, 64], [43, 90, 175, 117], [114, 98, 113, 160], [17, 1], []], ![[125, 171, 41, 133, 2, 4], [172, 136, 86, 157, 141, 86], [67, 163, 20, 106, 151, 50], [68, 154, 92, 25, 22, 125], [182, 17, 157, 70, 23, 133], [156, 36, 170, 88, 142, 117], [161, 20, 125]], ![[138, 80, 124, 181, 81, 69], [106, 69, 126, 134, 78, 103], [72, 178, 68, 173, 26, 115], [146, 149, 48, 72, 29, 135], [172, 36, 13, 181, 96, 51], [19, 9, 65, 14, 12, 125], [8, 136, 5]], ![[81, 28, 171, 168, 35, 190], [147, 96, 41, 86, 89, 66], [133, 64, 126, 4, 123, 159], [14, 1, 145, 110, 142, 42], [13, 25, 47, 69, 65, 137], [182, 19, 167, 9, 31, 99], [118, 76, 180]]]
 h' := ![![[156, 35, 131, 121], [120, 34, 95, 105], [190, 27, 164, 131], [11, 6, 174, 183], [118, 108, 14, 58], [31, 3, 81, 136], [0, 0, 1], [0, 1]], ![[37, 165, 5, 177], [44, 96, 84, 87], [0, 124, 4, 111], [54, 0, 171, 113], [57, 173, 0, 11], [178, 80, 168, 172], [58, 189, 44, 40], [156, 35, 131, 121]], ![[15, 181, 55, 84], [91, 20, 47, 185], [69, 173, 178, 172], [135, 144, 178, 92], [10, 183, 157, 189], [61, 70, 19, 157], [114, 107, 54, 37], [37, 165, 5, 177]], ![[0, 1], [38, 41, 156, 5], [142, 58, 36, 159], [52, 41, 50, 185], [108, 109, 20, 124], [111, 38, 114, 108], [2, 86, 92, 114], [15, 181, 55, 84]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [185, 93, 58], []]
 b := ![[], [], [130, 69, 117, 86], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 4
  hpos := by decide
  P := [133, 183, 153, 174, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2798417127, 10573558566, -12923526907, 401337831, 4844463747]
  a := ![-6, 8, 9, -7, 19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3844567764, -4383285849, -4886762507, -1088537190, 4844463747]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 1330863361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3329, 9767, -1687, 366, -1254]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![-3329, 9767, -1687, 366, -1254]] 
 ![![191, 0, 0, 0, 0], ![122, 1, 0, 0, 0], ![14, 0, 1, 0, 0], ![11, 0, 0, 1, 0], ![114, 0, 0, 0, 1]] where
  M :=![![![-3329, 9767, -1687, 366, -1254], ![-732, 2419, -421, 89, -312], ![-178, 694, -122, 25, -90], ![-50, 232, -41, 8, -30], ![-796, 2194, -377, 83, -281]]]
  hmulB := by decide  
  f := ![![![107, 1227, -2657, -158, -972]], ![![70, 803, -1739, -103, -636]], ![![12, 148, -318, -19, -114]], ![![21, 231, -502, -32, -186]], ![![74, 834, -1811, -105, -665]]]
  g := ![![![-5405, 9767, -1687, 366, -1254], ![-1337, 2419, -421, 89, -312], ![-383, 694, -122, 25, -90], ![-128, 232, -41, 8, -30], ![-1215, 2194, -377, 83, -281]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![107, 1227, -2657, -158, -972]] ![![-3329, 9767, -1687, 366, -1254]]
  ![![191, 0, 0, 0, 0]] where
 M := ![![![191, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC191 : ContainsPrimesAboveP 191 ![I191N0, I191N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI191N0
    exact isPrimeI191N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 191 (by decide) (𝕀 ⊙ MulI191N0)
instance hp193 : Fact (Nat.Prime 193) := {out := by norm_num}

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-31083695, 79499418, -13593748, 3050260, -10146458]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![-31083695, 79499418, -13593748, 3050260, -10146458]] 
 ![![193, 0, 0, 0, 0], ![0, 193, 0, 0, 0], ![0, 0, 193, 0, 0], ![0, 0, 0, 193, 0], ![76, 62, 6, 148, 1]] where
  M :=![![![-31083695, 79499418, -13593748, 3050260, -10146458], ![-6100520, 15602657, -2667924, 598648, -1991356], ![-1197296, 3062200, -523603, 117492, -390824], ![-234984, 600984, -102740, 23061, -76696], ![-7815092, 19987802, -3417736, 766900, -2551025]]]
  hmulB := by decide  
  f := ![![![-7, 42, -20, 4, -2]], ![![-8, 9, 36, -24, 20]], ![![48, -136, 117, 44, -104]], ![![-88, 552, -940, 237, 56]], ![![-72, 440, -714, 176, 47]]]
  g := ![![![3834441, 3671398, 245000, 7796508, -10146458], ![752552, 720553, 48084, 1530152, -1991356], ![147696, 141416, 9437, 300308, -390824], ![28984, 27752, 1852, 58933, -76696], ![964056, 923064, 61598, 1960200, -2551025]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 4 2 7 [80, 182, 20, 43, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 7, 124, 143], [120, 37, 180, 139], [13, 148, 82, 104], [0, 1]]
 g := ![![[118, 54, 10, 49], [110, 55, 100], [150, 183, 166], [12, 150, 72], [67, 116, 9], [92, 150, 1], []], ![[109, 143, 175, 185, 148, 168], [173, 28, 85], [19, 89, 143], [105, 162, 81], [87, 127, 2], [81, 159, 21], [57, 185, 113, 38, 76, 64]], ![[147, 180, 118, 185, 92, 109], [156, 64, 27], [21, 178, 56], [70, 77, 129], [17, 109, 128], [115, 44, 151], [84, 99, 127, 26, 79, 24]], ![[50, 77, 148, 16, 105, 148], [157, 183, 96], [5, 82, 8], [104, 185, 3], [173, 82, 46], [150, 146, 137], [150, 94, 126, 82, 160, 60]]]
 h' := ![![[17, 7, 124, 143], [110, 21, 165, 7], [15, 62, 120, 183], [7, 50, 146, 72], [141, 45, 108, 74], [167, 13, 116, 3], [0, 0, 0, 1], [0, 1]], ![[120, 37, 180, 139], [83, 110, 57, 167], [42, 26, 118, 144], [37, 112, 49, 170], [157, 191, 106, 9], [13, 5, 67, 52], [160, 2, 151, 139], [17, 7, 124, 143]], ![[13, 148, 82, 104], [0, 167, 177, 122], [30, 37, 95, 42], [121, 7, 124, 40], [33, 73, 4, 124], [106, 6, 167, 163], [106, 119, 5, 94], [120, 37, 180, 139]], ![[0, 1], [49, 88, 180, 90], [185, 68, 53, 17], [149, 24, 67, 104], [154, 77, 168, 179], [22, 169, 36, 168], [40, 72, 37, 152], [13, 148, 82, 104]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [10, 42, 147], []]
 b := ![[], [], [159, 115, 59, 185], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 4
  hpos := by decide
  P := [80, 182, 20, 43, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![26763860, 697735034, -1885696512, 928900096, -390140244]
  a := ![-3, 7, 6, -2, 13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![153769028, 128945234, 2358264, 303987856, -390140244]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 1387488001 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, -42, 20, -4, 2]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![7, -42, 20, -4, 2]] 
 ![![193, 0, 0, 0, 0], ![75, 1, 0, 0, 0], ![165, 0, 1, 0, 0], ![170, 0, 0, 1, 0], ![172, 0, 0, 0, 1]] where
  M :=![![![7, -42, 20, -4, 2], ![8, -9, -36, 24, -20], ![-48, 136, -117, -44, 104], ![88, -552, 940, -237, -56], ![132, -290, 96, 188, -319]]]
  hmulB := by decide  
  f := ![![![31083695, -79499418, 13593748, -3050260, 10146458]], ![![12110765, -30974399, 5296368, -1188436, 3953242]], ![![26580347, -67981690, 11624311, -2608344, 8676458]], ![![27380638, -70028508, 11974300, -2686877, 8937692]], ![![27742024, -70952786, 12132344, -2722340, 9055657]]]
  g := ![![![1, -42, 20, -4, 2], ![31, -9, -36, 24, -20], ![-7, 136, -117, -44, 104], ![-330, -552, 940, -237, -56], ![150, -290, 96, 188, -319]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![-31083695, 79499418, -13593748, 3050260, -10146458]] ![![7, -42, 20, -4, 2]]
  ![![193, 0, 0, 0, 0]] where
 M := ![![![-193, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, -610, 61, 15, 48]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![113, -610, 61, 15, 48]] 
 ![![197, 0, 0, 0, 0], ![0, 197, 0, 0, 0], ![0, 0, 197, 0, 0], ![0, 0, 0, 197, 0], ![146, 94, 30, 185, 1]] where
  M :=![![![113, -610, 61, 15, 48], ![-30, -49, -133, -65, 186], ![130, -904, 1430, -375, -18], ![750, -548, -2191, 2216, -2286], ![-506, 2470, -3793, 611, 655]]]
  hmulB := by decide  
  f := ![![![41, -142, 79, -1, 36]], ![![2, -105, 179, 9, 66]], ![![-18, -244, 516, 29, 186]], ![![-58, -704, 1517, 86, 546]], ![![-26, -856, 1652, 89, 601]]]
  g := ![![![-35, -26, -7, -45, 48], ![-138, -89, -29, -175, 186], ![14, 4, 10, 15, -18], ![1698, 1088, 337, 2158, -2286], ![-488, -300, -119, -612, 655]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 4 2 7 [2, 126, 139, 9, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [13, 64, 152, 64], [105, 146, 24, 22], [70, 183, 21, 111], [0, 1]]
 g := ![![[92, 11, 51, 34], [196, 100, 7], [116, 180, 75, 121], [63, 12, 26], [126, 167, 116], [139, 188, 1], []], ![[79, 105, 116, 16, 81, 59], [79, 13, 34], [115, 77, 103, 137, 65, 132], [181, 77, 76], [61, 99, 146], [113, 3, 116], [165, 63, 81, 64, 192, 134]], ![[67, 141, 18, 56, 105, 34], [196, 100, 7], [37, 6, 74, 182, 78, 109], [119, 196, 83], [101, 142, 138], [113, 108, 105], [163, 80, 8, 18, 86, 10]], ![[152, 81, 72, 101, 32, 77], [79, 13, 34], [149, 57, 119, 117, 92, 153], [34, 125, 28], [96, 39, 4], [94, 46, 107], [175, 129, 62, 175, 121, 57]]]
 h' := ![![[13, 64, 152, 64], [45, 64, 82, 25], [162, 150, 173, 91], [96, 94, 35, 11], [5, 57, 100, 82], [116, 37, 132, 71], [0, 0, 0, 1], [0, 1]], ![[105, 146, 24, 22], [80, 131, 40, 195], [89, 7, 100, 172], [55, 99, 90, 32], [90, 11, 144, 43], [139, 168, 81, 151], [94, 106, 105, 126], [13, 64, 152, 64]], ![[70, 183, 21, 111], [180, 49, 45, 75], [104, 47, 24, 106], [132, 70, 36, 169], [166, 132, 156, 87], [34, 60, 113, 170], [121, 73, 28, 156], [105, 146, 24, 22]], ![[0, 1], [45, 150, 30, 99], [177, 190, 97, 25], [190, 131, 36, 182], [109, 194, 191, 182], [164, 129, 68, 2], [67, 18, 64, 111], [70, 183, 21, 111]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [157, 28, 130], []]
 b := ![[], [], [164, 33, 22, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 4
  hpos := by decide
  P := [2, 126, 139, 9, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-54615129002, 126380563641, -57801324795, -71010042390, 129562706165]
  a := ![16, -7, -33, 16, -41]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-96298326036, -61180273177, -20023769085, -122031018695, 129562706165]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 1506138481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, -142, 79, -1, 36]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![41, -142, 79, -1, 36]] 
 ![![197, 0, 0, 0, 0], ![70, 1, 0, 0, 0], ![25, 0, 1, 0, 0], ![23, 0, 0, 1, 0], ![130, 0, 0, 0, 1]] where
  M :=![![![41, -142, 79, -1, 36], ![2, -105, 179, 9, 66], ![-18, -244, 516, 29, 186], ![-58, -704, 1517, 86, 546], ![-26, -470, 959, 53, 347]]]
  hmulB := by decide  
  f := ![![![113, -610, 61, 15, 48]], ![![40, -217, 21, 5, 18]], ![![15, -82, 15, 0, 6]], ![![17, -74, -4, 13, -6]], ![![72, -390, 21, 13, 35]]]
  g := ![![![17, -142, 79, -1, 36], ![-30, -105, 179, 9, 66], ![-105, -244, 516, 29, 186], ![-313, -704, 1517, 86, 546], ![-190, -470, 959, 53, 347]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![113, -610, 61, 15, 48]] ![![41, -142, 79, -1, 36]]
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


lemma PB984I4_primes (p : ℕ) :
  p ∈ Set.range ![157, 163, 167, 173, 179, 181, 191, 193, 197] ↔ Nat.Prime p ∧ 151 < p ∧ p ≤ 197 := by
  rw [← List.mem_ofFn']
  convert primes_range 151 197 (by omega)

def PB984I4 : PrimesBelowBoundCertificateInterval O 151 197 984 where
  m := 9
  g := ![2, 3, 1, 4, 2, 3, 2, 2, 2]
  P := ![157, 163, 167, 173, 179, 181, 191, 193, 197]
  hP := PB984I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1, I163N2]
    · exact ![I167N0]
    · exact ![I173N0, I173N1, I173N2, I173N3]
    · exact ![I179N0, I179N1]
    · exact ![I181N0, I181N1, I181N2]
    · exact ![I191N0, I191N1]
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
    · exact ![26569, 26569, 163]
    · exact ![129891985607]
    · exact ![29929, 173, 173, 173]
    · exact ![5735339, 32041]
    · exact ![32761, 32761, 181]
    · exact ![1330863361, 191]
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
      exact NI173N2
      exact NI173N3
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
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
      exact NI197N1
  β := ![I157N1, I163N2, I173N1, I173N2, I173N3, I181N2, I191N1, I193N1, I197N1]
  Il := ![[I157N1], [I163N2], [], [I173N1, I173N2, I173N3], [], [I181N2], [I191N1], [I193N1], [I197N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
