
import IdealArithmetic.Examples.NF5_3_125000000_1.RI5_3_125000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6291, 1760, -1480, 925, -760]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![6291, 1760, -1480, 925, -760]] 
 ![![157, 0, 0, 0, 0], ![0, 157, 0, 0, 0], ![0, 0, 157, 0, 0], ![0, 0, 0, 157, 0], ![13, 39, 35, 37, 1]] where
  M :=![![![6291, 1760, -1480, 925, -760], ![-15200, -4309, 3520, -2200, 1850], ![18500, 5260, -4309, 2595, -2200], ![-14400, -3950, 3500, -2109, 1670], ![16700, 4570, -3950, 2665, -2109]]]
  hmulB := by decide  
  f := ![![![327, 30, -40, 25, -30]], ![![-600, -73, 60, -50, 50]], ![![500, 30, -73, 35, -50]], ![![-200, -50, 0, -23, 10]], ![![-57, -21, -5, -8, 1]]]
  g := ![![![103, 200, 160, 185, -760], ![-250, -487, -390, -450, 1850], ![300, 580, 463, 535, -2200], ![-230, -440, -350, -407, 1670], ![281, 553, 445, 514, -2109]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 4 2 7 [14, 47, 58, 85, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [148, 50, 121, 57], [126, 71, 62, 21], [112, 35, 131, 79], [0, 1]]
 g := ![![[124, 121, 61, 101], [49, 100, 4], [23, 75, 116, 153], [51, 74, 6, 52], [49, 8, 28, 3], [1], []], ![[152, 149, 67, 1, 42, 57], [38, 84, 39], [144, 97, 61, 143, 155, 57], [112, 36, 128, 19, 76, 30], [100, 3, 24, 82, 82, 156], [137, 88, 14], [45, 133, 109]], ![[29, 156, 88, 14, 110, 24], [10, 80, 138], [29, 79, 86, 28, 98, 104], [104, 139, 108, 61, 44, 24], [85, 42, 113, 34, 8, 142], [112, 96, 117], [28, 130, 127]], ![[21, 82, 120, 13, 141, 29], [55, 60, 17], [29, 102, 7, 27, 64, 131], [62, 36, 57, 87, 122, 151], [97, 63, 104, 32, 14, 62], [139, 14, 4], [42, 149, 118]]]
 h' := ![![[148, 50, 121, 57], [6, 134, 119, 130], [149, 84, 47, 155], [71, 88, 155, 56], [99, 136, 61, 44], [143, 110, 99, 72], [0, 0, 1], [0, 1]], ![[126, 71, 62, 21], [148, 14, 6, 1], [44, 148, 127, 14], [77, 154, 91, 1], [94, 57, 111, 112], [84, 12, 51, 110], [79, 147, 140, 64], [148, 50, 121, 57]], ![[112, 35, 131, 79], [143, 76, 88, 49], [35, 118, 31, 74], [32, 103, 40, 124], [57, 116, 156, 108], [29, 65, 152, 51], [98, 155, 6, 91], [126, 71, 62, 21]], ![[0, 1], [104, 90, 101, 134], [106, 121, 109, 71], [98, 126, 28, 133], [60, 5, 143, 50], [43, 127, 12, 81], [24, 12, 10, 2], [112, 35, 131, 79]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [117, 80, 88], []]
 b := ![[], [], [68, 48, 128, 93], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 4
  hpos := by decide
  P := [14, 47, 58, 85, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9735514, 9798045, 5020673, 903122, 466805]
  a := ![0, -2, -3, -3, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![23357, -53550, -72086, -104259, 466805]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 607573201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![327, 30, -40, 25, -30]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![327, 30, -40, 25, -30]] 
 ![![157, 0, 0, 0, 0], ![83, 1, 0, 0, 0], ![88, 0, 1, 0, 0], ![153, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  M :=![![![327, 30, -40, 25, -30], ![-600, -73, 60, -50, 50], ![500, 30, -73, 35, -50], ![-200, -50, 0, -23, 10], ![100, -40, -50, -5, -23]]]
  hmulB := by decide  
  f := ![![![6291, 1760, -1480, 925, -760]], ![![3229, 903, -760, 475, -390]], ![![3644, 1020, -857, 535, -440]], ![![6039, 1690, -1420, 888, -730]], ![![467, 130, -110, 70, -57]]]
  g := ![![![-14, 30, -40, 25, -30], ![47, -73, 60, -50, 50], ![-3, 30, -73, 35, -50], ![47, -50, 0, -23, 10], ![56, -40, -50, -5, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![6291, 1760, -1480, 925, -760]] ![![327, 30, -40, 25, -30]]
  ![![157, 0, 0, 0, 0]] where
 M := ![![![157, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 7, 8, 7, -12]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![43, 7, 8, 7, -12]] 
 ![![163, 0, 0, 0, 0], ![0, 163, 0, 0, 0], ![0, 0, 163, 0, 0], ![157, 60, 69, 1, 0], ![88, 48, 26, 0, 1]] where
  M :=![![![43, 7, 8, 7, -12], ![-240, -93, 14, 28, 14], ![140, -29, -93, 7, 28], ![400, 238, -36, -121, 0], ![0, 182, 238, -36, -121]]]
  hmulB := by decide  
  f := ![![![-319, -93, 74, -47, 38]], ![![760, 211, -186, 110, -94]], ![![-940, -277, 211, -139, 110]], ![![-421, -128, 91, -63, 48]], ![![-104, -34, 20, -16, 11]]]
  g := ![![![0, 1, -1, 7, -12], ![-36, -15, -14, 28, 14], ![-21, -11, -8, 7, 28], ![119, 46, 51, -121, 0], ![100, 50, 36, -36, -121]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [34, 44, 15, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [142, 114, 133], [6, 48, 30], [0, 1]]
 g := ![![[15, 12, 10], [12, 50, 132], [11, 74], [12, 49], [61, 85], [18, 148, 1], []], ![[120, 27, 3, 55], [143, 63, 91, 81], [86, 9], [79, 93], [148, 56], [125, 15, 50, 155], [35, 85]], ![[55, 129, 55, 116], [60, 45, 10, 78], [155, 126], [6, 40], [1, 6], [3, 89, 33, 147], [138, 85]]]
 h' := ![![[142, 114, 133], [81, 78, 70], [26, 77, 28], [143, 82, 143], [15, 65, 7], [40, 44, 30], [0, 0, 1], [0, 1]], ![[6, 48, 30], [129, 147, 42], [94, 64, 12], [35, 64, 3], [90, 97, 16], [118, 34, 120], [66, 73, 48], [142, 114, 133]], ![[0, 1], [140, 101, 51], [31, 22, 123], [30, 17, 17], [87, 1, 140], [152, 85, 13], [71, 90, 114], [6, 48, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 52], []]
 b := ![[], [162, 152, 143], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [34, 44, 15, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-72629552, -44369314, -3259122, -10103354, -4448964]
  a := ![3, -65, 2, -66, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![11687766, 4756946, 4966536, -10103354, -4448964]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 4330747 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, -6, -4, 2, 2]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![-3, -6, -4, 2, 2]] 
 ![![163, 0, 0, 0, 0], ![69, 1, 0, 0, 0], ![146, 0, 1, 0, 0], ![63, 0, 0, 1, 0], ![27, 0, 0, 0, 1]] where
  M :=![![![-3, -6, -4, 2, 2], ![40, 17, -12, -10, 4], ![40, 38, 17, -14, -10], ![-120, -40, 44, 27, -16], ![-160, -134, -40, 52, 27]]]
  hmulB := by decide  
  f := ![![![-321, -410, -196, -118, -58]], ![![-143, -181, -88, -52, -26]], ![![-302, -382, -183, -110, -54]], ![![-141, -178, -88, -51, -26]], ![![-89, -104, -52, -30, -15]]]
  g := ![![![5, -6, -4, 2, 2], ![7, 17, -12, -10, 4], ![-24, 38, 17, -14, -10], ![-31, -40, 44, 27, -16], ![67, -134, -40, 52, 27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1

def I163N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4567, 466, -524, 361, -406]] i)))

def SI163N2: IdealEqSpanCertificate' Table ![![4567, 466, -524, 361, -406]] 
 ![![163, 0, 0, 0, 0], ![119, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![79, 0, 0, 1, 0], ![108, 0, 0, 0, 1]] where
  M :=![![![4567, 466, -524, 361, -406], ![-8120, -829, 932, -642, 722], ![7220, 738, -829, 571, -642], ![-2360, -242, 272, -187, 210], ![2100, 216, -242, 167, -187]]]
  hmulB := by decide  
  f := ![![![189, 140, 36, -13, -8]], ![![137, 103, 28, -9, -6]], ![![10, 8, 3, 1, 0]], ![![97, 70, 16, -6, -2]], ![![144, 106, 26, -11, -5]]]
  g := ![![![-186, 466, -524, 361, -406], ![331, -829, 932, -642, 722], ![-295, 738, -829, 571, -642], ![97, -242, 272, -187, 210], ![-87, 216, -242, 167, -187]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N2 : Nat.card (O ⧸ I163N2) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N2)

lemma isPrimeI163N2 : Ideal.IsPrime I163N2 := prime_ideal_of_norm_prime hp163.out _ NI163N2
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![43, 7, 8, 7, -12]] ![![-3, -6, -4, 2, 2]]
  ![![1551, 1493, 668, -531, -402]] where
 M := ![![![1551, 1493, 668, -531, -402]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI163N1 : IdealMulLeCertificate' Table 
  ![![1551, 1493, 668, -531, -402]] ![![4567, 466, -524, 361, -406]]
  ![![163, 0, 0, 0, 0]] where
 M := ![![![192177, 19723, -22168, 14996, -16952]]]
 hmul := by decide  
 g := ![![![![1179, 121, -136, 92, -104]]]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-333, -138, 32, -57, 24]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![-333, -138, 32, -57, 24]] 
 ![![167, 0, 0, 0, 0], ![0, 167, 0, 0, 0], ![0, 0, 167, 0, 0], ![33, 19, 36, 1, 0], ![148, 102, 59, 0, 1]] where
  M :=![![![-333, -138, 32, -57, 24], ![480, -13, -276, 40, -114], ![-1140, -582, -13, -219, 40], ![160, -330, -444, -53, -162], ![-1620, -1114, -330, -363, -53]]]
  hmulB := by decide  
  f := ![![![101, 16, -8, 5, -10]], ![![-200, -27, 32, -6, 10]], ![![100, -24, -27, 27, -6]], ![![19, -5, -4, 6, -2]], ![![4, -10, 3, 10, -5]]]
  g := ![![![-12, -9, 4, -57, 24], ![96, 65, 30, 40, -114], ![1, -3, 33, -219, 40], ![155, 103, 66, -53, -162], ![109, 67, 95, -363, -53]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [86, 155, 128, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [91, 28, 40], [115, 138, 127], [0, 1]]
 g := ![![[164, 138, 132], [124, 68, 48], [118, 29, 19], [64, 87], [126, 63], [30, 39, 1], []], ![[51, 104, 90, 117], [57, 131, 136, 129], [114, 84, 31, 129], [152, 16], [71, 47], [21, 42, 69, 73], [11, 97]], ![[37, 79, 96, 76], [157, 95, 35, 65], [3, 27, 160, 31], [103, 6], [116, 76], [109, 118, 107, 36], [91, 97]]]
 h' := ![![[91, 28, 40], [24, 0, 74], [39, 127, 81], [161, 33, 55], [133, 139, 134], [92, 12, 49], [0, 0, 1], [0, 1]], ![[115, 138, 127], [64, 24, 25], [22, 152, 59], [111, 161, 59], [18, 108, 4], [46, 54, 61], [154, 59, 138], [91, 28, 40]], ![[0, 1], [86, 143, 68], [61, 55, 27], [134, 140, 53], [108, 87, 29], [159, 101, 57], [55, 108, 28], [115, 138, 127]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24, 133], []]
 b := ![[], [148, 107, 76], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [86, 155, 128, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-51010, -15044, 27548, 19919, 3292]
  a := ![1, -4, -1, -5, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7159, -4367, -5292, 19919, 3292]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 4657463 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![697, 71, -80, 55, -62]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![697, 71, -80, 55, -62]] 
 ![![167, 0, 0, 0, 0], ![112, 1, 0, 0, 0], ![74, 0, 1, 0, 0], ![142, 0, 0, 1, 0], ![64, 0, 0, 0, 1]] where
  M :=![![![697, 71, -80, 55, -62], ![-1240, -127, 142, -98, 110], ![1100, 111, -127, 87, -98], ![-360, -38, 40, -29, 32], ![320, 32, -38, 24, -29]]]
  hmulB := by decide  
  f := ![![![391, 91, -106, 73, -52]], ![![256, 59, -70, 48, -34]], ![![182, 43, -49, 33, -24]], ![![326, 76, -88, 61, -44]], ![![152, 34, -42, 30, -21]]]
  g := ![![![-31, 71, -80, 55, -62], ![56, -127, 142, -98, 110], ![-48, 111, -127, 87, -98], ![18, -38, 40, -29, 32], ![-12, 32, -38, 24, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1

def I167N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13, -3, 6, 2, -2]] i)))

def SI167N2: IdealEqSpanCertificate' Table ![![-13, -3, 6, 2, -2]] 
 ![![167, 0, 0, 0, 0], ![150, 1, 0, 0, 0], ![106, 0, 1, 0, 0], ![158, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![-13, -3, 6, 2, -2], ![-40, -31, -6, 14, 4], ![40, 1, -31, -8, 14], ![160, 104, 4, -45, -10], ![-100, 22, 104, 9, -45]]]
  hmulB := by decide  
  f := ![![![-2419, -369, 212, -222, 190]], ![![-2150, -331, 186, -198, 168]], ![![-1562, -241, 135, -144, 122]], ![![-2286, -354, 196, -211, 178]], ![![-119, -27, 4, -13, 7]]]
  g := ![![![-3, -3, 6, 2, -2], ![18, -31, -6, 14, 4], ![26, 1, -31, -8, 14], ![-52, 104, 4, -45, -10], ![-93, 22, 104, 9, -45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N2 : Nat.card (O ⧸ I167N2) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N2)

lemma isPrimeI167N2 : Ideal.IsPrime I167N2 := prime_ideal_of_norm_prime hp167.out _ NI167N2
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![-333, -138, 32, -57, 24]] ![![697, 71, -80, 55, -62]]
  ![![2419, 369, -212, 222, -190]] where
 M := ![![![2419, 369, -212, 222, -190]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI167N1 : IdealMulLeCertificate' Table 
  ![![2419, 369, -212, 222, -190]] ![![-13, -3, 6, 2, -2]]
  ![![167, 0, 0, 0, 0]] where
 M := ![![![-167, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC167 : ContainsPrimesAboveP 167 ![I167N0, I167N1, I167N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
    exact isPrimeI167N1
    exact isPrimeI167N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 167 (by decide) (𝕀 ⊙ MulI167N0 ⊙ MulI167N1)
instance hp173 : Fact (Nat.Prime 173) := {out := by norm_num}

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1233, -130, 142, -97, 110]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![-1233, -130, 142, -97, 110]] 
 ![![173, 0, 0, 0, 0], ![0, 173, 0, 0, 0], ![0, 0, 173, 0, 0], ![42, 131, 15, 1, 0], ![62, 53, 79, 0, 1]] where
  M :=![![![-1233, -130, 142, -97, 110], ![2200, 229, -260, 174, -194], ![-1940, -194, 229, -163, 174], ![640, 74, -64, 55, -66], ![-660, -108, 74, -31, 55]]]
  hmulB := by decide  
  f := ![![![-21, -12, -2, -5, 0]], ![![0, -23, -24, -4, -10]], ![![-100, -72, -23, -19, -4]], ![![-14, -27, -21, -6, -8]], ![![-54, -45, -19, -12, -5]]]
  g := ![![![-23, 39, -41, -97, 110], ![40, -71, 72, 174, -194], ![-34, 69, -64, -163, 174], ![14, -21, 25, 55, -66], ![-16, 6, -22, -31, 55]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [157, 92, 152, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [146, 107, 166], [48, 65, 7], [0, 1]]
 g := ![![[74, 130, 137], [121, 136], [123, 45, 152], [161, 136, 43], [26, 78], [3, 21, 1], []], ![[72, 101, 160, 145], [126, 113], [145, 58, 165, 76], [82, 98, 146, 115], [3, 38], [56, 39, 116, 8], [50, 49]], ![[93, 119, 5, 68], [116, 52], [81, 100, 94, 103], [21, 124, 121, 87], [90, 88], [96, 81, 8, 44], [36, 49]]]
 h' := ![![[146, 107, 166], [106, 33, 134], [65, 145, 89], [154, 48, 124], [125, 118, 40], [48, 60, 50], [0, 0, 1], [0, 1]], ![[48, 65, 7], [134, 38, 2], [59, 7, 99], [57, 11, 112], [144, 124, 44], [142, 48, 62], [145, 94, 65], [146, 107, 166]], ![[0, 1], [90, 102, 37], [39, 21, 158], [84, 114, 110], [62, 104, 89], [51, 65, 61], [112, 79, 107], [48, 65, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [115, 159], []]
 b := ![[], [92, 127, 171], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [157, 92, 152, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3544922, 4434278, 3100838, 1382105, 565947]
  a := ![1, 18, 4, 17, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-517874, -1194316, -360350, 1382105, 565947]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 5177717 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-21, -12, -2, -5, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![-21, -12, -2, -5, 0]] 
 ![![173, 0, 0, 0, 0], ![0, 173, 0, 0, 0], ![16, 158, 1, 0, 0], ![67, 43, 0, 1, 0], ![4, 73, 0, 0, 1]] where
  M :=![![![-21, -12, -2, -5, 0], ![0, -23, -24, -4, -10], ![-100, -72, -23, -19, -4], ![-40, -74, -60, -19, -14], ![-140, -134, -74, -53, -19]]]
  hmulB := by decide  
  f := ![![![-1233, -130, 142, -97, 110]], ![![2200, 229, -260, 174, -194]], ![![1884, 196, -223, 149, -166]], ![![73, 7, -10, 6, -6]], ![![896, 93, -106, 71, -79]]]
  g := ![![![2, 3, -2, -5, 0], ![4, 27, -24, -4, -10], ![9, 27, -23, -19, -4], ![13, 65, -60, -19, -14], ![27, 88, -74, -53, -19]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P1 : CertificateIrreducibleZModOfList' 173 2 2 7 [151, 157, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 172], [0, 1]]
 g := ![![[158, 55], [37], [144, 121], [155, 78], [152], [129, 83], [1]], ![[0, 118], [37], [4, 52], [19, 95], [152], [73, 90], [1]]]
 h' := ![![[16, 172], [97, 48], [54, 27], [123, 11], [113, 123], [70, 49], [22, 16], [0, 1]], ![[0, 1], [0, 125], [140, 146], [126, 162], [5, 50], [162, 124], [105, 157], [16, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [165, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N1 : CertifiedPrimeIdeal' SI173N1 173 where
  n := 2
  hpos := by decide
  P := [151, 157, 1]
  hirr := P173P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![75, 385, -746, 530, -382]
  a := ![-1, 2, -4, 4, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-127, 713, -746, 530, -382]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N1 B_one_repr
lemma NI173N1 : Nat.card (O ⧸ I173N1) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![-1233, -130, 142, -97, 110]] ![![-21, -12, -2, -5, 0]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![169, 171, 98, 53, 22]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![169, 171, 98, 53, 22]] 
 ![![179, 0, 0, 0, 0], ![0, 179, 0, 0, 0], ![0, 0, 179, 0, 0], ![0, 0, 0, 179, 0], ![146, 81, 37, 157, 1]] where
  M :=![![![169, 171, 98, 53, 22], ![440, 531, 342, 174, 106], ![1060, 1027, 531, 289, 174], ![1520, 1574, 856, 357, 236], ![2360, 2604, 1574, 738, 357]]]
  hmulB := by decide  
  f := ![![![131, 15, -16, 11, -12]], ![![-240, -29, 30, -20, 22]], ![![220, 27, -29, 19, -20]], ![![-80, -10, 12, -9, 8]], ![![-26, -4, 5, -4, 3]]]
  g := ![![![-17, -9, -4, -19, 22], ![-84, -45, -20, -92, 106], ![-136, -73, -33, -151, 174], ![-184, -98, -44, -205, 236], ![-278, -147, -65, -309, 357]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 4 2 7 [32, 36, 96, 87, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [108, 161, 96, 17], [153, 155, 62, 159], [10, 41, 21, 3], [0, 1]]
 g := ![![[19, 40, 9, 80], [88, 42, 125, 108], [58, 137, 25], [3, 121, 89], [85, 135, 99, 56], [92, 1], []], ![[30, 103, 143, 66, 67, 93], [65, 17, 81, 59, 50, 43], [79, 97, 12], [88, 19, 75], [65, 108, 88, 14, 70, 13], [35, 71, 5, 169, 174, 9], [0, 138, 110]], ![[47, 17, 98, 79, 28, 102], [99, 155, 26, 128, 141, 122], [84, 173, 70], [178, 136, 80], [82, 130, 114, 12, 97, 53], [111, 60, 81, 160, 0, 28], [115, 131, 42]], ![[59, 0, 145, 172, 134, 138], [67, 19, 107, 6, 101, 64], [37, 81, 106], [101, 105, 158], [99, 167, 61, 16, 28, 31], [127, 90, 54, 122, 111, 65], [60, 59, 9]]]
 h' := ![![[108, 161, 96, 17], [48, 38, 9, 59], [95, 82, 171, 65], [55, 1, 88, 5], [144, 94, 110, 39], [99, 57, 82, 134], [0, 0, 1], [0, 1]], ![[153, 155, 62, 159], [85, 5, 25, 4], [25, 167, 164, 23], [91, 129, 58, 141], [143, 172, 56, 84], [29, 16, 99, 117], [29, 109, 42, 13], [108, 161, 96, 17]], ![[10, 41, 21, 3], [110, 91, 118, 131], [114, 63, 123, 100], [98, 65, 131, 138], [31, 62, 131, 120], [41, 173, 14, 66], [39, 76, 121, 105], [153, 155, 62, 159]], ![[0, 1], [137, 45, 27, 164], [70, 46, 79, 170], [178, 163, 81, 74], [176, 30, 61, 115], [103, 112, 163, 41], [149, 173, 15, 61], [10, 41, 21, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [154, 64, 125], []]
 b := ![[], [], [100, 127, 177, 51], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 4
  hpos := by decide
  P := [32, 36, 96, 87, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-286887968, -33198640, 155134640, -6674800, -30815392]
  a := ![0, -10, 4, -20, 6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![23531616, 13758928, 7236336, 26990736, -30815392]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 1026625681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 15, -16, 11, -12]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![131, 15, -16, 11, -12]] 
 ![![179, 0, 0, 0, 0], ![44, 1, 0, 0, 0], ![106, 0, 1, 0, 0], ![152, 0, 0, 1, 0], ![57, 0, 0, 0, 1]] where
  M :=![![![131, 15, -16, 11, -12], ![-240, -29, 30, -20, 22], ![220, 27, -29, 19, -20], ![-80, -10, 12, -9, 8], ![80, 14, -10, 8, -9]]]
  hmulB := by decide  
  f := ![![![169, 171, 98, 53, 22]], ![![44, 45, 26, 14, 6]], ![![106, 107, 61, 33, 14]], ![![152, 154, 88, 47, 20]], ![![67, 69, 40, 21, 9]]]
  g := ![![![1, 15, -16, 11, -12], ![-2, -29, 30, -20, 22], ![2, 27, -29, 19, -20], ![0, -10, 12, -9, 8], ![-1, 14, -10, 8, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![169, 171, 98, 53, 22]] ![![131, 15, -16, 11, -12]]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1059, 708, 320, 224, 66]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![1059, 708, 320, 224, 66]] 
 ![![181, 0, 0, 0, 0], ![0, 181, 0, 0, 0], ![0, 0, 181, 0, 0], ![46, 6, 163, 1, 0], ![104, 122, 44, 0, 1]] where
  M :=![![![1059, 708, 320, 224, 66], ![1320, 2171, 1416, 574, 448], ![4480, 4056, 2171, 1192, 574], ![5080, 5684, 3348, 1597, 968], ![9680, 10022, 5684, 2864, 1597]]]
  hmulB := by decide  
  f := ![![![39, 56, 40, -16, -22]], ![![-440, -185, 112, 102, -32]], ![![-320, -356, -185, 128, 102]], ![![-286, -310, -155, 113, 86]], ![![-344, -172, 56, 88, -11]]]
  g := ![![![-89, -48, -216, 224, 66], ![-396, -309, -618, 574, 448], ![-608, -404, -1201, 1192, 574], ![-934, -674, -1655, 1597, 968], ![-1592, -1116, -2936, 2864, 1597]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [94, 107, 127, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [89, 135, 62], [146, 45, 119], [0, 1]]
 g := ![![[78, 42, 94], [8, 25], [64, 61, 133], [132, 55], [139, 166, 116], [94, 54, 1], []], ![[128, 167, 144, 161], [14, 42], [177, 156, 64, 55], [147, 39], [26, 27, 29, 25], [24, 173, 88, 117], [57, 43]], ![[91, 45, 39, 169], [143, 20], [55, 58, 165, 117], [164, 133], [45, 45, 90, 125], [28, 45, 106, 33], [0, 43]]]
 h' := ![![[89, 135, 62], [11, 154, 53], [138, 83, 5], [151, 36, 155], [147, 115, 112], [33, 70, 109], [0, 0, 1], [0, 1]], ![[146, 45, 119], [50, 146, 168], [68, 105, 122], [67, 135, 157], [55, 13, 43], [12, 55, 14], [29, 133, 45], [89, 135, 62]], ![[0, 1], [178, 62, 141], [100, 174, 54], [164, 10, 50], [106, 53, 26], [64, 56, 58], [139, 48, 135], [146, 45, 119]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [69, 175], []]
 b := ![[], [100, 25, 76], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [94, 107, 127, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![38845, 14698, -13475, -6153, 18983]
  a := ![13, 0, -3, 1, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9129, -12510, 852, -6153, 18983]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 5929741 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-91, -9, 10, -7, 8]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![-91, -9, 10, -7, 8]] 
 ![![181, 0, 0, 0, 0], ![108, 1, 0, 0, 0], ![141, 0, 1, 0, 0], ![115, 0, 0, 1, 0], ![125, 0, 0, 0, 1]] where
  M :=![![![-91, -9, 10, -7, 8], ![160, 15, -18, 12, -14], ![-140, -13, 15, -11, 12], ![40, 2, -4, 3, -4], ![-40, -6, 2, -2, 3]]]
  hmulB := by decide  
  f := ![![![89, 29, -24, -3, -10]], ![![52, 17, -14, -2, -6]], ![![69, 22, -19, -2, -8]], ![![55, 17, -16, -2, -6]], ![![65, 21, -18, -3, -7]]]
  g := ![![![-4, -9, 10, -7, 8], ![8, 15, -18, 12, -14], ![-6, -13, 15, -11, 12], ![3, 2, -4, 3, -4], ![1, -6, 2, -2, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1

def I181N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-71, -82, -48, -23, -14]] i)))

def SI181N2: IdealEqSpanCertificate' Table ![![-71, -82, -48, -23, -14]] 
 ![![181, 0, 0, 0, 0], ![109, 1, 0, 0, 0], ![123, 0, 1, 0, 0], ![120, 0, 0, 1, 0], ![157, 0, 0, 0, 1]] where
  M :=![![![-71, -82, -48, -23, -14], ![-280, -287, -164, -82, -46], ![-460, -498, -287, -141, -82], ![-680, -722, -416, -205, -118], ![-1180, -1256, -722, -357, -205]]]
  hmulB := by decide  
  f := ![![![-171, -140, -24, 29, 36]], ![![-99, -83, -16, 17, 22]], ![![-113, -92, -15, 18, 24]], ![![-120, -94, -12, 21, 22]], ![![-167, -134, -22, 30, 33]]]
  g := ![![![109, -82, -48, -23, -14], ![377, -287, -164, -82, -46], ![657, -498, -287, -141, -82], ![952, -722, -416, -205, -118], ![1655, -1256, -722, -357, -205]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N2 : Nat.card (O ⧸ I181N2) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N2)

lemma isPrimeI181N2 : Ideal.IsPrime I181N2 := prime_ideal_of_norm_prime hp181.out _ NI181N2
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![1059, 708, 320, 224, 66]] ![![-91, -9, 10, -7, 8]]
  ![![-21569, -3019, 1882, -1897, 1702]] where
 M := ![![![-21569, -3019, 1882, -1897, 1702]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI181N1 : IdealMulLeCertificate' Table 
  ![![-21569, -3019, 1882, -1897, 1702]] ![![-71, -82, -48, -23, -14]]
  ![![181, 0, 0, 0, 0]] where
 M := ![![![792599, 929797, 550602, 259554, 161452]]]
 hmul := by decide  
 g := ![![![![4379, 5137, 3042, 1434, 892]]]]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1529, -199, 198, -135, 142]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![-1529, -199, 198, -135, 142]] 
 ![![191, 0, 0, 0, 0], ![0, 191, 0, 0, 0], ![0, 0, 191, 0, 0], ![0, 0, 0, 191, 0], ![39, 121, 109, 108, 1]] where
  M :=![![![-1529, -199, 198, -135, 142], ![2840, 373, -398, 254, -270], ![-2700, -399, 373, -263, 254], ![1120, 174, -200, 119, -128], ![-1280, -308, 174, -136, 119]]]
  hmulB := by decide  
  f := ![![![1, 1, 0, -1, 0]], ![![0, 1, 2, 0, -2]], ![![-20, -11, 1, 3, 0]], ![![0, -10, -12, 1, 4]], ![![-11, -11, -5, 2, 1]]]
  g := ![![![-37, -91, -80, -81, 142], ![70, 173, 152, 154, -270], ![-66, -163, -143, -145, 254], ![32, 82, 72, 73, -128], ![-31, -77, -67, -68, 119]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 4 2 7 [59, 33, 158, 78, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [179, 9, 107, 97], [141, 23, 3, 5], [175, 158, 81, 89], [0, 1]]
 g := ![![[52, 26, 110, 86], [174, 39, 121, 26], [37, 35, 77, 69], [121, 40, 146, 40], [147, 42, 57, 25], [113, 1], []], ![[85, 107, 68, 188, 7, 16], [51, 188, 125, 63, 123, 150], [186, 161, 46, 159, 171, 60], [129, 65, 79, 128, 96, 54], [84, 132, 2, 120, 184, 79], [124, 106, 167, 93, 34, 108], [58, 50, 50]], ![[4, 93, 160, 179, 52, 8], [80, 56, 167, 125, 83, 9], [162, 36, 74, 2, 61, 15], [48, 105, 69, 132, 176, 130], [45, 28, 189, 42, 2, 92], [12, 48, 99, 170, 175, 20], [125, 181, 25]], ![[93, 137, 89, 129, 89, 21], [145, 67, 18, 5, 96, 126], [137, 116, 130, 122, 187, 83], [16, 119, 102, 147, 153, 28], [109, 146, 55, 183, 102, 181], [111, 183, 114, 162, 8, 185], [186, 140, 90]]]
 h' := ![![[179, 9, 107, 97], [48, 18, 48, 75], [109, 179, 70, 44], [119, 113, 49, 159], [113, 62, 108, 123], [18, 32, 67, 5], [0, 0, 1], [0, 1]], ![[141, 23, 3, 5], [187, 40, 176, 105], [25, 144, 109, 181], [51, 88, 103, 123], [52, 76, 102, 185], [61, 10, 20, 84], [160, 77, 175, 40], [179, 9, 107, 97]], ![[175, 158, 81, 89], [40, 10, 51, 90], [33, 126, 183, 123], [24, 116, 99, 24], [2, 88, 54, 147], [94, 173, 78, 173], [91, 86, 153, 2], [141, 23, 3, 5]], ![[0, 1], [54, 123, 107, 112], [126, 124, 20, 34], [95, 65, 131, 76], [105, 156, 118, 118], [32, 167, 26, 120], [169, 28, 53, 149], [175, 158, 81, 89]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [93, 165, 101], []]
 b := ![[], [], [125, 143, 176, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 4
  hpos := by decide
  P := [59, 33, 158, 78, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-396813, 1048315, 930530, -1664359, 375278]
  a := ![-1, -4, 2, -5, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-78705, -232253, -209292, -220913, 375278]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 1330863361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 1, 0, -1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![1, 1, 0, -1, 0]] 
 ![![191, 0, 0, 0, 0], ![166, 1, 0, 0, 0], ![165, 0, 1, 0, 0], ![165, 0, 0, 1, 0], ![57, 0, 0, 0, 1]] where
  M :=![![![1, 1, 0, -1, 0], ![0, 1, 2, 0, -2], ![-20, -11, 1, 3, 0], ![0, -10, -12, 1, 4], ![40, 18, -10, -14, 1]]]
  hmulB := by decide  
  f := ![![![-1529, -199, 198, -135, 142]], ![![-1314, -171, 170, -116, 122]], ![![-1335, -174, 173, -118, 124]], ![![-1315, -171, 170, -116, 122]], ![![-463, -61, 60, -41, 43]]]
  g := ![![![0, 1, 0, -1, 0], ![-2, 1, 2, 0, -2], ![6, -11, 1, 3, 0], ![17, -10, -12, 1, 4], ![5, 18, -10, -14, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![-1529, -199, 198, -135, 142]] ![![1, 1, 0, -1, 0]]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-93, 6, 20, -3, 12]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![-93, 6, 20, -3, 12]] 
 ![![193, 0, 0, 0, 0], ![0, 193, 0, 0, 0], ![0, 0, 193, 0, 0], ![51, 21, 121, 1, 0], ![5, 54, 48, 0, 1]] where
  M :=![![![-93, 6, 20, -3, 12], ![240, 71, 12, 28, -6], ![-60, 90, 71, 15, 28], ![160, 138, 84, 43, 18], ![180, 230, 138, 75, 43]]]
  hmulB := by decide  
  f := ![![![19, 8, -4, 1, -2]], ![![-40, -9, 16, -6, 2]], ![![20, 0, -9, 15, -6]], ![![13, 1, -5, 9, -4]], ![![-5, -2, 2, 2, -1]]]
  g := ![![![0, -3, -1, -3, 12], ![-6, -1, -16, 28, -6], ![-5, -9, -16, 15, 28], ![-11, -9, -31, 43, 18], ![-20, -19, -57, 75, 43]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 3 2 7 [14, 80, 20, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [94, 13, 188], [79, 179, 5], [0, 1]]
 g := ![![[76, 126, 124], [73, 118], [82, 16], [14, 96], [70, 43], [25, 14], [1]], ![[44, 31, 96, 125], [44, 21], [56, 110], [105, 175], [116, 145], [52, 165], [3, 20, 1, 68]], ![[178, 35, 60, 10], [159, 110], [156, 177], [124, 72], [111, 124], [111, 192], [78, 192, 117, 125]]]
 h' := ![![[94, 13, 188], [152, 174, 33], [4, 138, 120], [90, 2, 4], [155, 125, 17], [39, 44, 129], [179, 113, 173], [0, 1]], ![[79, 179, 5], [84, 73, 19], [11, 10, 139], [71, 18, 127], [169, 47, 102], [153, 121, 97], [63, 158, 101], [94, 13, 188]], ![[0, 1], [28, 139, 141], [175, 45, 127], [64, 173, 62], [177, 21, 74], [90, 28, 160], [183, 115, 112], [79, 179, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54, 164], []]
 b := ![[], [109, 43, 110], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 3
  hpos := by decide
  P := [14, 80, 20, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-82319, 39117, 66723, -114971, 63127]
  a := ![3, -4, 7, -8, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![28319, -4950, 56726, -114971, 63127]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 7189057 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19, -8, 4, -1, 2]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![-19, -8, 4, -1, 2]] 
 ![![193, 0, 0, 0, 0], ![0, 193, 0, 0, 0], ![98, 72, 1, 0, 0], ![85, 173, 0, 1, 0], ![30, 35, 0, 0, 1]] where
  M :=![![![-19, -8, 4, -1, 2], ![40, 9, -16, 6, -2], ![-20, 0, 9, -15, 6], ![40, 26, 8, 3, -14], ![-140, -60, 26, 15, 3]]]
  hmulB := by decide  
  f := ![![![93, -6, -20, 3, -12]], ![![-240, -71, -12, -28, 6]], ![![-42, -30, -15, -9, -4]], ![![-175, -67, -20, -24, 0]], ![![-30, -15, -6, -5, -1]]]
  g := ![![![-2, -1, 4, -1, 2], ![6, 1, -16, 6, -2], ![1, 9, 9, -15, 6], ![-3, -3, 8, 3, -14], ![-21, -24, 26, 15, 3]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P1 : CertificateIrreducibleZModOfList' 193 2 2 7 [21, 147, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [46, 192], [0, 1]]
 g := ![![[7, 46], [121], [177], [9], [69], [12], [46, 1]], ![[0, 147], [121], [177], [9], [69], [12], [92, 192]]]
 h' := ![![[46, 192], [185, 168], [88, 11], [36, 131], [178, 3], [135, 29], [192, 165], [0, 1]], ![[0, 1], [0, 25], [15, 182], [79, 62], [123, 190], [118, 164], [62, 28], [46, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [87]]
 b := ![[], [61, 140]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N1 : CertifiedPrimeIdeal' SI193N1 193 where
  n := 2
  hpos := by decide
  P := [21, 147, 1]
  hirr := P193P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![289, 97, 304, -25, 1056]
  a := ![1, 0, 2, -1, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-306, -282, 304, -25, 1056]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N1 B_one_repr
lemma NI193N1 : Nat.card (O ⧸ I193N1) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![-93, 6, 20, -3, 12]] ![![-19, -8, 4, -1, 2]]
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

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-35691, -3580, 4054, -2799, 3162]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![-35691, -3580, 4054, -2799, 3162]] 
 ![![197, 0, 0, 0, 0], ![0, 197, 0, 0, 0], ![0, 0, 197, 0, 0], ![0, 0, 0, 197, 0], ![36, 36, 169, 55, 1]] where
  M :=![![![-35691, -3580, 4054, -2799, 3162], ![63240, 6307, -7160, 4946, -5598], ![-55980, -5548, 6307, -4361, 4946], ![17840, 1686, -1968, 1361, -1562], ![-15620, -1436, 1686, -1187, 1361]]]
  hmulB := by decide  
  f := ![![![-7, -6, -2, 1, 0]], ![![0, -9, -12, -4, 2]], ![![20, 6, -9, -13, -4]], ![![-40, -14, 12, -5, -14]], ![![4, -2, -7, -13, -7]]]
  g := ![![![-759, -596, -2692, -897, 3162], ![1344, 1055, 4766, 1588, -5598], ![-1188, -932, -4211, -1403, 4946], ![376, 294, 1330, 443, -1562], ![-328, -256, -1159, -386, 1361]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 4 2 7 [106, 96, 67, 48, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [113, 145, 146, 171], [103, 124, 145, 96], [130, 124, 103, 127], [0, 1]]
 g := ![![[90, 163, 184, 23], [61, 98, 116], [170, 136, 91, 22], [139, 128, 70], [89, 109, 76], [70, 149, 1], []], ![[72, 134, 191, 150, 107, 156], [75, 104, 133], [54, 94, 152, 172, 95, 163], [54, 161, 92], [65, 73, 172], [68, 155, 43], [89, 46, 47, 60, 91, 154]], ![[184, 74, 72, 62, 102, 104], [61, 98, 116], [114, 187, 119, 141, 75, 39], [34, 114, 133], [147, 65, 174], [61, 82, 155], [4, 1, 36, 122, 169, 9]], ![[101, 40, 167, 133, 153, 34], [75, 104, 133], [32, 73, 141, 19, 128, 121], [139, 175, 24], [164, 86, 40], [15, 63, 173], [21, 55, 183, 151, 77, 174]]]
 h' := ![![[113, 145, 146, 171], [16, 11, 41, 107], [104, 45, 51, 71], [7, 117, 151, 131], [44, 90, 132, 55], [66, 141, 9, 154], [0, 0, 0, 1], [0, 1]], ![[103, 124, 145, 96], [160, 69, 0, 83], [69, 114, 161, 85], [11, 125, 188, 103], [66, 171, 152, 17], [88, 133, 120, 70], [91, 76, 12, 35], [113, 145, 146, 171]], ![[130, 124, 103, 127], [144, 159, 38, 126], [122, 152, 146, 126], [47, 51, 36, 39], [156, 2, 22, 85], [136, 196, 114, 119], [135, 148, 85, 130], [103, 124, 145, 96]], ![[0, 1], [151, 155, 118, 78], [157, 83, 36, 112], [176, 101, 19, 121], [174, 131, 88, 40], [192, 121, 151, 51], [194, 170, 100, 31], [130, 124, 103, 127]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [36, 143, 122], []]
 b := ![[], [], [181, 22, 108, 167], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 4
  hpos := by decide
  P := [106, 96, 67, 48, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5130, -9448, -11476, 8724, 1620]
  a := ![4, 1, -1, 2, -1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-270, -344, -1448, -408, 1620]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 1506138481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, -6, -2, 1, 0]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![-7, -6, -2, 1, 0]] 
 ![![197, 0, 0, 0, 0], ![87, 1, 0, 0, 0], ![57, 0, 1, 0, 0], ![38, 0, 0, 1, 0], ![120, 0, 0, 0, 1]] where
  M :=![![![-7, -6, -2, 1, 0], ![0, -9, -12, -4, 2], ![20, 6, -9, -13, -4], ![-40, -14, 12, -5, -14], ![-140, -98, -14, 19, -5]]]
  hmulB := by decide  
  f := ![![![-35691, -3580, 4054, -2799, 3162]], ![![-15441, -1549, 1754, -1211, 1368]], ![![-10611, -1064, 1205, -832, 940]], ![![-6794, -682, 772, -533, 602]], ![![-21820, -2188, 2478, -1711, 1933]]]
  g := ![![![3, -6, -2, 1, 0], ![7, -9, -12, -4, 2], ![5, 6, -9, -13, -4], ![12, -14, 12, -5, -14], ![46, -98, -14, 19, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![-35691, -3580, 4054, -2799, 3162]] ![![-7, -6, -2, 1, 0]]
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


lemma PB547I4_primes (p : ℕ) :
  p ∈ Set.range ![157, 163, 167, 173, 179, 181, 191, 193, 197] ↔ Nat.Prime p ∧ 151 < p ∧ p ≤ 197 := by
  rw [← List.mem_ofFn']
  convert primes_range 151 197 (by omega)

def PB547I4 : PrimesBelowBoundCertificateInterval O 151 197 547 where
  m := 9
  g := ![2, 3, 3, 2, 2, 3, 2, 2, 2]
  P := ![157, 163, 167, 173, 179, 181, 191, 193, 197]
  hP := PB547I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1, I163N2]
    · exact ![I167N0, I167N1, I167N2]
    · exact ![I173N0, I173N1]
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
    · exact ![4330747, 163, 163]
    · exact ![4657463, 167, 167]
    · exact ![5177717, 29929]
    · exact ![1026625681, 179]
    · exact ![5929741, 181, 181]
    · exact ![1330863361, 191]
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
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
      exact NI163N1
      exact NI163N2
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
      exact NI167N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
      exact NI197N1
  β := ![I157N1, I163N1, I163N2, I167N1, I167N2, I179N1, I181N1, I181N2, I191N1, I197N1]
  Il := ![[I157N1], [I163N1, I163N2], [I167N1, I167N2], [], [I179N1], [I181N1, I181N2], [I191N1], [], [I197N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
