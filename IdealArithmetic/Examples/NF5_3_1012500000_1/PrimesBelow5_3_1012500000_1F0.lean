
import IdealArithmetic.Examples.NF5_3_1012500000_1.RI5_3_1012500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14, 23, -8, 3, -2]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![14, 23, -8, 3, -2]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![14, 23, -8, 3, -2], ![-12, -16, 4, -21, 3], ![18, 33, 5, 33, -21], ![-30, -66, 14, 35, 16], ![24, 45, -76, -171, 62]]]
  hmulB := by decide  
  f := ![![![67, -160, -268, -108, -53]], ![![-159, -364, -322, -165, -54]], ![![-324, -969, -949, -465, -165]], ![![-3, 18, 26, 11, 5]], ![![-303, -843, -806, -399, -139]]]
  g := ![![![7, 23, -8, 3, -2], ![-6, -16, 4, -21, 3], ![9, 33, 5, 33, -21], ![-15, -66, 14, 35, 16], ![12, 45, -76, -171, 62]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-23, -14, 6, -1, 2]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![-23, -14, 6, -1, 2]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-23, -14, 6, -1, 2], ![12, 7, -3, 3, -1], ![-6, -3, -1, -9, 3], ![6, 8, -1, -1, -3], ![-6, -18, 14, 39, -7]]]
  hmulB := by decide  
  f := ![![![-148, -421, -405, -200, -70]], ![![-210, -599, -578, -285, -100]], ![![-600, -1710, -1648, -813, -285]], ![![-59, -168, -162, -80, -28]], ![![-587, -1673, -1613, -796, -279]]]
  g := ![![![-12, -14, 6, -1, 2], ![5, 7, -3, 3, -1], ![0, -3, -1, -9, 3], ![5, 8, -1, -1, -3], ![-19, -18, 14, 39, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 2, 0, -1, -1]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![1, 2, 0, -1, -1]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![1, 2, 0, -1, -1], ![-6, -14, 7, 21, -1], ![-6, -21, -10, -3, 21], ![24, 62, -17, -70, -11], ![0, 24, 64, 93, -82]]]
  hmulB := by decide  
  f := ![![![68, 99, -36, 13, -13]], ![![-5, -14, -3, -4, 0]], ![![73, 108, -52, 11, -17]], ![![-30, -49, 16, -7, 6]], ![![19, 21, -22, -1, -6]]]
  g := ![![![0, 2, 0, -1, -1], ![1, -14, 7, 21, -1], ![2, -21, -10, -3, 21], ![-5, 62, -17, -70, -11], ![-3, 24, 64, 93, -82]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![14, 23, -8, 3, -2]] ![![-23, -14, 6, -1, 2]]
  ![![32, 49, -8, 46, -14]] where
 M := ![![![32, 49, -8, 46, -14]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![32, 49, -8, 46, -14]] ![![-23, -14, 6, -1, 2]]
  ![![260, 539, -189, -405, -49]] where
 M := ![![![260, 539, -189, -405, -49]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![260, 539, -189, -405, -49]] ![![1, 2, 0, -1, -1]]
  ![![-11560, -29343, 9412, 35419, 3705]] where
 M := ![![![-11560, -29343, 9412, 35419, 3705]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![-11560, -29343, 9412, 35419, 3705]] ![![1, 2, 0, -1, -1]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![958082, 2474928, -664524, -2767644, -454864]]]
 hmul := by decide  
 g := ![![![![479041, 1237464, -332262, -1383822, -227432]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1, I2N1, I2N2, I2N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
    exact isPrimeI2N1
    exact isPrimeI2N2
    exact isPrimeI2N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1 ⊙ MulI2N2 ⊙ MulI2N3)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-195, -452, -404, -206, -68]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![-195, -452, -404, -206, -68]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-195, -452, -404, -206, -68], ![-408, -1215, -1186, -582, -206], ![-1236, -3498, -3367, -1662, -582], ![36, 88, 82, 41, 14], ![-1044, -2988, -2884, -1422, -499]]]
  hmulB := by decide  
  f := ![![![-9, -20, 16, 42, -8]], ![![-16, -43, 6, 38, 14]], ![![84, 194, -119, -330, 38]], ![![-4, 12, 62, 97, -74]], ![![-372, -884, 464, 1374, -87]]]
  g := ![![![-65, -452, -404, -206, -68], ![-136, -1215, -1186, -582, -206], ![-412, -3498, -3367, -1662, -582], ![12, 88, 82, 41, 14], ![-348, -2988, -2884, -1422, -499]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-59, -168, -162, -80, -28]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![-59, -168, -162, -80, -28]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-59, -168, -162, -80, -28], ![-168, -479, -462, -228, -80], ![-480, -1368, -1317, -648, -228], ![12, 34, 32, 15, 6], ![-408, -1164, -1130, -564, -195]]]
  hmulB := by decide  
  f := ![![![135, 312, -94, 48, -36]], ![![-72, -135, 42, -20, 16]], ![![96, 168, -53, 24, -20]], ![![-23, -14, 6, -1, 2]], ![![-24, -44, 14, -4, 5]]]
  g := ![![![7, -168, -162, -80, -28], ![20, -479, -462, -228, -80], ![56, -1368, -1317, -648, -228], ![-1, 34, 32, 15, 6], ![52, -1164, -1130, -564, -195]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![-195, -452, -404, -206, -68]] ![![-195, -452, -404, -206, -68]]
  ![![785361, 2235568, 2154340, 1062932, 372548]] where
 M := ![![![785361, 2235568, 2154340, 1062932, 372548]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![785361, 2235568, 2154340, 1062932, 372548]] ![![-59, -168, -162, -80, -28]]
  ![![-1595239323, -4547421024, -4384292094, -2162723796, -758294336]] where
 M := ![![![-1595239323, -4547421024, -4384292094, -2162723796, -758294336]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![-1595239323, -4547421024, -4384292094, -2162723796, -758294336]] ![![-59, -168, -162, -80, -28]]
  ![![3245977460745, 9253048459392, 8921115409420, 4400689564788, 1542970033140]] where
 M := ![![![3245977460745, 9253048459392, 8921115409420, 4400689564788, 1542970033140]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N3 : IdealMulLeCertificate' Table 
  ![![3245977460745, 9253048459392, 8921115409420, 4400689564788, 1542970033140]] ![![-59, -168, -162, -80, -28]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![-6604883706627075, -18828013978912656, -18152599802460918, -8954480786124276, -3139620578073552]]]
 hmul := by decide  
 g := ![![![![-2201627902209025, -6276004659637552, -6050866600820306, -2984826928708092, -1046540192691184]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N0, I3N1, I3N1, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N1
    exact isPrimeI3N1
    exact isPrimeI3N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1 ⊙ MulI3N2 ⊙ MulI3N3)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 11, -2, -5, -3]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5, 11, -2, -5, -3]] 
 ![![5, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![5, 11, -2, -5, -3], ![-18, -40, 22, 57, -5], ![-30, -93, -11, 51, 57], ![72, 184, -62, -233, -20], ![66, 231, 114, 39, -236]]]
  hmulB := by decide  
  f := ![![![107869, 57529, -25492, 4649, -9141]], ![![75326, 40174, -17800, 3247, -6383]], ![![91874, 49001, -21709, 3961, -7785]], ![![39886, 21272, -9426, 1719, -3380]], ![![40600, 21655, -9592, 1751, -3440]]]
  g := ![![![-3, 11, -2, -5, -3], ![-10, -40, 22, 57, -5], ![34, -93, -11, 51, 57], ![18, 184, -62, -233, -20], ![-184, 231, 114, 39, -236]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![5, 11, -2, -5, -3]] ![![5, 11, -2, -5, -3]]
  ![![-671, -1812, 222, 1548, 624]] where
 M := ![![![-671, -1812, 222, 1548, 624]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![-671, -1812, 222, 1548, 624]] ![![5, 11, -2, -5, -3]]
  ![![175241, 473429, -65804, -424955, -154497]] where
 M := ![![![175241, 473429, -65804, -424955, -154497]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![175241, 473429, -65804, -424955, -154497]] ![![5, 11, -2, -5, -3]]
  ![![-46464959, -124770264, 19523352, 115742376, 38316696]] where
 M := ![![![-46464959, -124770264, 19523352, 115742376, 38316696]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![-46464959, -124770264, 19523352, 115742376, 38316696]] ![![5, 11, -2, -5, -3]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![12290192405, 32811778235, -5674696730, -31357511765, -9481510515]]]
 hmul := by decide  
 g := ![![![![2458038481, 6562355647, -1134939346, -6271502353, -1896302103]]]]
 hle2 := by decide  

def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N0, I5N0, I5N0, I5N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0 ⊙ MulI5N1 ⊙ MulI5N2 ⊙ MulI5N3)
instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-95, -161, 45, -24, 18]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![-95, -161, 45, -24, 18]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![6, 0, 6, 1, 1]] where
  M :=![![![-95, -161, 45, -24, 18], ![108, 175, -74, 18, -24], ![-144, -252, 31, -66, 18], ![90, 147, -43, 43, -20], ![6, -21, -43, 36, 1]]]
  hmulB := by decide  
  f := ![![![-16709, -8911, 3949, -720, 1416]], ![![8496, 4531, -2008, 366, -720]], ![![-4320, -2304, 1021, -186, 366]], ![![2526, 1347, -597, 109, -214]], ![![-17382, -9270, 4108, -749, 1473]]]
  g := ![![![-29, -23, -9, -6, 18], ![36, 25, 10, 6, -24], ![-36, -36, -11, -12, 18], ![30, 21, 11, 9, -20], ![0, -3, -7, 5, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 4 2 2 [3, 0, 6, 0, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 4, 0, 5], [0, 6], [0, 3, 0, 2], [0, 1]]
 g := ![![[0, 1, 0, 1], []], ![[0, 5, 0, 0, 0, 3], [0, 3, 0, 5, 0, 6]], ![[0, 6, 0, 6], []], ![[0, 2, 0, 0, 0, 4], [0, 4, 0, 2, 0, 1]]]
 h' := ![![[0, 4, 0, 5], [0, 0, 0, 1], [0, 1]], ![[0, 6], [0, 5, 0, 3], [0, 4, 0, 5]], ![[0, 3, 0, 2], [0, 0, 0, 6], [0, 6]], ![[0, 1], [0, 2, 0, 4], [0, 3, 0, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [5], []]
 b := ![[], [], [0, 1, 0, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 4
  hpos := by decide
  P := [3, 0, 6, 0, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![426195801, 1026127774, -493321868, -1519558918, 56095379]
  a := ![0, -1, -4, -1, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![12803361, 146589682, -118556306, -225093471, 56095379]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 2401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-16709, -8911, 3949, -720, 1416]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![-16709, -8911, 3949, -720, 1416]] 
 ![![7, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![-16709, -8911, 3949, -720, 1416], ![8496, 4531, -2008, 366, -720], ![-4320, -2304, 1021, -186, 366], ![2526, 1347, -597, 109, -214], ![1974, 1053, -467, 84, -167]]]
  hmulB := by decide  
  f := ![![![-95, -161, 45, -24, 18]], ![![-66, -113, 28, -18, 12]], ![![-102, -174, 43, -30, 18]], ![![-55, -94, 26, -11, 10]], ![![-67, -118, 26, -12, 13]]]
  g := ![![![1369, -8911, 3949, -720, 1416], ![-696, 4531, -2008, 366, -720], ![354, -2304, 1021, -186, 366], ![-207, 1347, -597, 109, -214], ![-161, 1053, -467, 84, -167]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![-95, -161, 45, -24, 18]] ![![-16709, -8911, 3949, -720, 1416]]
  ![![7, 0, 0, 0, 0]] where
 M := ![![![7, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0)
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0, 0, 0]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]] where
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 5 2 3 [5, 1, 8, 7, 9, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 9, 7, 8, 7], [0, 4, 6, 4, 10], [1, 3, 0, 3, 9], [3, 5, 9, 7, 7], [0, 1]]
 g := ![![[7, 4, 4, 2, 4], [1], []], ![[4, 3, 1, 8, 4, 5, 9, 2], [1, 7, 3, 6, 9, 2, 7, 2], [9, 8, 1, 5]], ![[2, 4, 0, 0, 5, 9, 3, 6], [5, 0, 6, 7, 6, 6], [0, 7, 5, 1]], ![[6, 0, 7, 2, 4, 9, 5, 3], [9, 5, 0, 6, 6, 6, 10, 4], [7, 6, 7, 4]], ![[4, 8, 9, 7, 5, 10], [6, 8, 1, 3, 8, 1, 3, 2], [2, 4, 9, 5]]]
 h' := ![![[9, 9, 7, 8, 7], [6, 10, 3, 4, 2], [0, 0, 1], [0, 1]], ![[0, 4, 6, 4, 10], [10, 9, 0, 9, 4], [3, 3, 1, 7, 4], [9, 9, 7, 8, 7]], ![[1, 3, 0, 3, 9], [8, 6, 7, 6, 7], [0, 9, 6, 4], [0, 4, 6, 4, 10]], ![[3, 5, 9, 7, 7], [0, 9, 3, 8, 9], [10, 2, 0, 3, 3], [1, 3, 0, 3, 9]], ![[0, 1], [6, 10, 9, 6], [10, 8, 3, 8, 4], [3, 5, 9, 7, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 10, 6, 7], [], [], []]
 b := ![[], [4, 10, 2, 7, 10], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 5
  hpos := by decide
  P := [5, 1, 8, 7, 9, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8421331391, 18977747910, -25252498161, -56374174241, 5862540563]
  a := ![3, -64, 1, -1, 2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![765575581, 1725249810, -2295681651, -5124924931, 532958233]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 161051 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def PBC11 : ContainsPrimesAboveP 11 ![I11N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![11, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 11 (by decide) 𝕀

instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1139, -602, 268, -48, 96]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-1139, -602, 268, -48, 96]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![1, 7, 12, 6, 1]] where
  M :=![![![-1139, -602, 268, -48, 96], ![576, 301, -134, 24, -48], ![-288, -144, 67, -12, 24], ![168, 84, -38, 7, -14], ![132, 66, -28, 12, -11]]]
  hmulB := by decide  
  f := ![![![1, 2, 0, 0, 0]], ![![0, 1, 2, 0, 0]], ![![0, 0, 7, 12, 0]], ![![0, 0, -2, -5, 2]], ![![1, 3, 6, 6, 1]]]
  g := ![![![-95, -98, -68, -48, 96], ![48, 49, 34, 24, -48], ![-24, -24, -17, -12, 24], ![14, 14, 10, 7, -14], ![11, 11, 8, 6, -11]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 4 2 3 [10, 6, 0, 0, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 10, 7, 12], [10, 6, 3, 8], [1, 9, 3, 6], [0, 1]]
 g := ![![[5, 9, 3, 10], [0, 0, 1], []], ![[1, 2, 1, 8, 0, 10], [6, 10, 12], [10, 8, 0, 0, 8, 12]], ![[8, 3, 7, 10, 9, 6], [3, 12, 10], [10, 0, 12, 3, 4, 5]], ![[1, 11, 5, 12, 1, 5], [3, 0, 4], [6, 6, 6, 3, 12, 8]]]
 h' := ![![[2, 10, 7, 12], [0, 0, 3, 7], [0, 0, 0, 1], [0, 1]], ![[10, 6, 3, 8], [6, 8, 1, 4], [12, 6, 12, 8], [2, 10, 7, 12]], ![[1, 9, 3, 6], [5, 6, 7, 11], [3, 11, 1, 6], [10, 6, 3, 8]], ![[0, 1], [6, 12, 2, 4], [6, 9, 0, 11], [1, 9, 3, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [11, 1, 11], []]
 b := ![[], [], [6, 5, 1, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 4
  hpos := by decide
  P := [10, 6, 0, 0, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![30981617, 74907926, -34908124, -109105830, 3070942]
  a := ![1, -3, -2, -1, -3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2146975, 4108564, -5519956, -9810114, 3070942]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 28561 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -2, 0, 0, 0]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![-1, -2, 0, 0, 0]] 
 ![![13, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![10, 0, 0, 0, 1]] where
  M :=![![![-1, -2, 0, 0, 0], ![0, -1, -2, 0, 0], ![0, 0, -7, -12, 0], ![0, 0, 2, 5, -2], ![-12, -30, 8, 36, -1]]]
  hmulB := by decide  
  f := ![![![1139, 602, -268, 48, -96]], ![![569, 301, -134, 24, -48]], ![![285, 150, -67, 12, -24]], ![![688, 364, -162, 29, -58]], ![![866, 458, -204, 36, -73]]]
  g := ![![![1, -2, 0, 0, 0], ![1, -1, -2, 0, 0], ![9, 0, -7, -12, 0], ![-2, 0, 2, 5, -2], ![-8, -30, 8, 36, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-1139, -602, 268, -48, 96]] ![![-1, -2, 0, 0, 0]]
  ![![13, 0, 0, 0, 0]] where
 M := ![![![-13, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0)
instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10169, -5445, 2409, -442, 864]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![-10169, -5445, 2409, -442, 864]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![2, 10, 1, 0, 0], ![7, 7, 0, 1, 0], ![9, 2, 0, 0, 1]] where
  M :=![![![-10169, -5445, 2409, -442, 864], ![5184, 2791, -1232, 228, -442], ![-2652, -1446, 635, -120, 228], ![1554, 851, -373, 71, -134], ![1206, 651, -287, 54, -103]]]
  hmulB := by decide  
  f := ![![![11, 31, 27, 10, 6]], ![![36, 101, 78, 24, 10]], ![![26, 74, 65, 28, 8]], ![![19, 53, 42, 13, 8]], ![![21, 56, 26, -12, 9]]]
  g := ![![![-1157, -1657, 2409, -442, 864], ![590, 847, -1232, 228, -442], ![-302, -436, 635, -120, 228], ![177, 256, -373, 71, -134], ![137, 197, -287, 54, -103]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [13, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 16], [0, 1]]
 g := ![![[14, 4], [8], [8], [1]], ![[0, 13], [8], [8], [1]]]
 h' := ![![[5, 16], [7, 2], [14, 12], [4, 5], [0, 1]], ![[0, 1], [0, 15], [6, 5], [12, 12], [5, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [8, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 2
  hpos := by decide
  P := [13, 12, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2648, 6318, -2291, -8934, 1785]
  a := ![1, 19, 3, -1, 6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3159, 5188, -2291, -8934, 1785]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9947, -5306, 2351, -427, 843]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![-9947, -5306, 2351, -427, 843]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![2, 16, 1, 0, 0], ![5, 12, 0, 1, 0], ![10, 1, 0, 0, 1]] where
  M :=![![![-9947, -5306, 2351, -427, 843], ![5058, 2698, -1198, 213, -427], ![-2562, -1347, 599, -141, 213], ![1494, 779, -343, 101, -130], ![1140, 534, -261, 141, -76]]]
  hmulB := by decide  
  f := ![![![640829, 1071044, -340181, 155539, -128889]], ![![-773334, -1292506, 410518, -187701, 155539]], ![![-597556, -998721, 317207, -145037, 120185]], ![![-395893, -661673, 210156, -96090, 79625]], ![![317344, 530390, -168461, 77024, -63827]]]
  g := ![![![-1232, -2273, 2351, -427, 843], ![627, 1161, -1198, 213, -427], ![-305, -556, 599, -141, 213], ![175, 305, -343, 101, -130], ![101, 182, -261, 141, -76]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P1 : CertificateIrreducibleZModOfList' 17 2 2 4 [9, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 16], [0, 1]]
 g := ![![[7, 2], [1], [8], [1]], ![[0, 15], [1], [8], [1]]]
 h' := ![![[5, 16], [4, 6], [9, 1], [8, 5], [0, 1]], ![[0, 1], [0, 11], [14, 16], [16, 12], [5, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [15, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N1 : CertifiedPrimeIdeal' SI17N1 17 where
  n := 2
  hpos := by decide
  P := [9, 12, 1]
  hirr := P17P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1900, 3982, -3504, -8726, 2459]
  a := ![-1, 0, -2, 2, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1644, 9547, -3504, -8726, 2459]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N1 B_one_repr
lemma NI17N1 : Nat.card (O ⧸ I17N1) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N1

def I17N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2051, -1095, 485, -88, 174]] i)))

def SI17N2: IdealEqSpanCertificate' Table ![![-2051, -1095, 485, -88, 174]] 
 ![![17, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-2051, -1095, 485, -88, 174], ![1044, 559, -248, 42, -88], ![-528, -276, 125, -30, 42], ![306, 155, -69, 29, -26], ![234, 105, -59, 24, -7]]]
  hmulB := by decide  
  f := ![![![-13111, -37367, -36013, -17768, -6228]], ![![-8368, -23851, -22990, -11342, -3976]], ![![-9356, -26668, -25707, -12682, -4446]], ![![-2930, -8351, -8049, -3971, -1392]], ![![-6137, -17494, -16866, -8320, -2917]]]
  g := ![![![291, -1095, 485, -88, 174], ![-148, 559, -248, 42, -88], ![74, -276, 125, -30, 42], ![-44, 155, -69, 29, -26], ![-27, 105, -59, 24, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N2 : Nat.card (O ⧸ I17N2) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N2)

lemma isPrimeI17N2 : Ideal.IsPrime I17N2 := prime_ideal_of_norm_prime hp17.out _ NI17N2
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![-10169, -5445, 2409, -442, 864]] ![![-9947, -5306, 2351, -427, 843]]
  ![![67762987, 36138239, -16015116, 2919891, -5742539]] where
 M := ![![![67762987, 36138239, -16015116, 2919891, -5742539]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI17N1 : IdealMulLeCertificate' Table 
  ![![67762987, 36138239, -16015116, 2919891, -5742539]] ![![-2051, -1095, 485, -88, 174]]
  ![![17, 0, 0, 0, 0]] where
 M := ![![![-93247851053, -49729406638, 22038213245, -4018027435, 7902240441]]]
 hmul := by decide  
 g := ![![![![-5485167709, -2925259214, 1296365485, -236354555, 464837673]]]]
 hle2 := by decide  


def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N1, I17N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N1
    exact isPrimeI17N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 17 (by decide) (𝕀 ⊙ MulI17N0 ⊙ MulI17N1)
instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![91, 223, -87, -300, 4]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![91, 223, -87, -300, 4]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![5, 17, 14, 1, 0], ![13, 15, 7, 0, 1]] where
  M :=![![![91, 223, -87, -300, 4], ![24, 151, 246, 306, -300], ![-1800, -4476, 1783, 5958, 306], ![1206, 2703, -1943, -5093, 840], ![6858, 17439, -5439, -20820, -2267]]]
  hmulB := by decide  
  f := ![![![129661, 67877, -30315, 5364, -10858]], ![![-65148, -33209, 15000, -2538, 5364]], ![![32184, 15312, -7127, 1062, -2538]], ![![-1435, -1023, 406, -107, 148]], ![![48349, 25469, -11345, 2028, -4065]]]
  g := ![![![81, 277, 215, -300, 4], ![126, -29, -102, 306, -300], ![-1872, -5808, -4409, 5958, 306], ![829, 4036, 3341, -5093, 840], ![7391, 21336, 15890, -20820, -2267]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 3 2 4 [15, 14, 12, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 1, 1], [14, 17, 18], [0, 1]]
 g := ![![[3, 16, 4], [11, 0, 9], [7, 1], []], ![[14, 5, 5, 11], [12, 1, 0, 11], [2, 4], [9, 1]], ![[17, 3, 16, 13], [13, 0, 15, 3], [13, 1], [11, 1]]]
 h' := ![![[12, 1, 1], [6, 3, 17], [9, 1, 16], [0, 0, 1], [0, 1]], ![[14, 17, 18], [5, 9, 7], [13, 10, 7], [9, 16, 17], [12, 1, 1]], ![[0, 1], [5, 7, 14], [6, 8, 15], [12, 3, 1], [14, 17, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 16], []]
 b := ![[], [10, 11, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 3
  hpos := by decide
  P := [15, 14, 12, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![305823, 837520, -112492, -730980, -326984]
  a := ![0, 0, -6, -10, -4]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![432185, 956260, 653164, -730980, -326984]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 6859 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -3, 1, 4, 0]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![-1, -3, 1, 4, 0]] 
 ![![19, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![10, 0, 0, 0, 1]] where
  M :=![![![-1, -3, 1, 4, 0], ![0, -1, -4, -6, 4], ![24, 60, -23, -78, -6], ![-18, -41, 27, 73, -10], ![-90, -231, 65, 264, 37]]]
  hmulB := by decide  
  f := ![![![1433, 2215, -715, 316, -270]], ![![141, 212, -69, 30, -26]], ![![854, 1330, -429, 190, -162]], ![![609, 934, -302, 133, -114]], ![![728, 1123, -363, 160, -137]]]
  g := ![![![-2, -3, 1, 4, 0], ![3, -1, -4, -6, 4], ![44, 60, -23, -78, -6], ![-38, -41, 27, 73, -10], ![-147, -231, 65, 264, 37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1

def I19N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6023, -3280, 1336, -298, 494]] i)))

def SI19N2: IdealEqSpanCertificate' Table ![![-6023, -3280, 1336, -298, 494]] 
 ![![19, 0, 0, 0, 0], ![11, 1, 0, 0, 0], ![12, 0, 1, 0, 0], ![10, 0, 0, 1, 0], ![8, 0, 0, 0, 1]] where
  M :=![![![-6023, -3280, 1336, -298, 494], ![2964, 1387, -950, 18, -298], ![-1788, -1506, -289, -390, 18], ![912, 500, -198, 47, -74], ![504, -204, -728, -246, -157]]]
  hmulB := by decide  
  f := ![![![1675, 2808, -892, 374, -338]], ![![863, 1447, -458, 196, -176]], ![![1176, 1962, -625, 294, -234]], ![![802, 1352, -434, 139, -158]], ![![704, 1212, -372, 70, -161]]]
  g := ![![![687, -3280, 1336, -298, 494], ![69, 1387, -950, 18, -298], ![1158, -1506, -289, -390, 18], ![-110, 500, -198, 47, -74], ![800, -204, -728, -246, -157]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N2 : Nat.card (O ⧸ I19N2) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N2)

lemma isPrimeI19N2 : Ideal.IsPrime I19N2 := prime_ideal_of_norm_prime hp19.out _ NI19N2
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![91, 223, -87, -300, 4]] ![![-1, -3, 1, 4, 0]]
  ![![2861, 5660, -6640, -15032, 4562]] where
 M := ![![![2861, 5660, -6640, -15032, 4562]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI19N1 : IdealMulLeCertificate' Table 
  ![![2861, 5660, -6640, -15032, 4562]] ![![-6023, -3280, 1336, -298, 494]]
  ![![19, 0, 0, 0, 0]] where
 M := ![![![6821, 19532, 19456, 10146, 3268]]]
 hmul := by decide  
 g := ![![![![359, 1028, 1024, 534, 172]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N1, I19N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N1
    exact isPrimeI19N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0 ⊙ MulI19N1)
instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19213, -10246, 4540, -828, 1628]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![-19213, -10246, 4540, -828, 1628]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![19, 14, 1, 0, 0], ![19, 21, 0, 1, 0], ![22, 9, 0, 0, 1]] where
  M :=![![![-19213, -10246, 4540, -828, 1628], ![9768, 5207, -2310, 420, -828], ![-4968, -2652, 1169, -216, 420], ![2904, 1548, -686, 125, -246], ![2268, 1206, -540, 96, -193]]]
  hmulB := by decide  
  f := ![![![13, 26, -8, -12, -4]], ![![-24, -47, 30, 60, -12]], ![![-7, -16, 13, 36, -8]], ![![-7, -11, 16, 29, -14]], ![![14, 37, 2, -12, -21]]]
  g := ![![![-5459, -3090, 4540, -828, 1628], ![2778, 1573, -2310, 420, -828], ![-1405, -794, 1169, -216, 420], ![825, 467, -686, 125, -246], ![650, 369, -540, 96, -193]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [17, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 22], [0, 1]]
 g := ![![[22, 16], [10, 4], [11, 13], [1]], ![[18, 7], [9, 19], [2, 10], [1]]]
 h' := ![![[17, 22], [14, 19], [20, 2], [6, 17], [0, 1]], ![[0, 1], [15, 4], [8, 21], [19, 6], [17, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [16, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [17, 6, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1602, 2738, -2534, -6158, 1725]
  a := ![13, -1, -2, 1, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![5600, 6609, -2534, -6158, 1725]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-41645, -69603, 22107, -10108, 8376]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![-41645, -69603, 22107, -10108, 8376]] 
 ![![23, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![21, 0, 1, 0, 0], ![18, 0, 0, 1, 0], ![8, 0, 0, 0, 1]] where
  M :=![![![-41645, -69603, 22107, -10108, 8376], ![50256, 83995, -26678, 12198, -10108], ![-60648, -101364, 32195, -14718, 12198], ![42522, 71069, -22573, 10319, -8552], ![15606, 26085, -8285, 3780, -3139]]]
  hmulB := by decide  
  f := ![![![55049, 29371, -12993, 2380, -4662]], ![![10751, 5738, -2535, 466, -910]], ![![50883, 27153, -12004, 2202, -4308]], ![![42720, 22793, -10083, 1847, -3618]], ![![18866, 10069, -4447, 820, -1597]]]
  g := ![![![-1867, -69603, 22107, -10108, 8376], ![2253, 83995, -26678, 12198, -10108], ![-2721, -101364, 32195, -14718, 12198], ![1908, 71069, -22573, 10319, -8552], ![706, 26085, -8285, 3780, -3139]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1

def I23N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1085, -3095, -2988, -1473, -517]] i)))

def SI23N2: IdealEqSpanCertificate' Table ![![-1085, -3095, -2988, -1473, -517]] 
 ![![23, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  M :=![![![-1085, -3095, -2988, -1473, -517], ![-3102, -8840, -8518, -4203, -1473], ![-8838, -25197, -24299, -11985, -4203], ![216, 618, 600, 295, 104], ![-7566, -21567, -20792, -10257, -3596]]]
  hmulB := by decide  
  f := ![![![-703, -383, 170, -9, 59]], ![![-168, -92, 40, -3, 15]], ![![-308, -157, 71, -21, 25]], ![![-244, -140, 64, 13, 18]], ![![-291, -198, 80, 54, 31]]]
  g := ![![![2774, -3095, -2988, -1473, -517], ![7913, -8840, -8518, -4203, -1473], ![22567, -25197, -24299, -11985, -4203], ![-556, 618, 600, 295, 104], ![19312, -21567, -20792, -10257, -3596]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N2 : Nat.card (O ⧸ I23N2) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N2)

lemma isPrimeI23N2 : Ideal.IsPrime I23N2 := prime_ideal_of_norm_prime hp23.out _ NI23N2

def I23N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2665, 1419, -631, 114, -226]] i)))

def SI23N3: IdealEqSpanCertificate' Table ![![2665, 1419, -631, 114, -226]] 
 ![![23, 0, 0, 0, 0], ![21, 1, 0, 0, 0], ![19, 0, 1, 0, 0], ![16, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![2665, 1419, -631, 114, -226], ![-1356, -725, 316, -60, 114], ![684, 354, -173, 24, -60], ![-402, -213, 95, -17, 34], ![-318, -177, 65, -18, 25]]]
  hmulB := by decide  
  f := ![![![11, 33, -11, -54, -4]], ![![9, 28, -7, -42, -6]], ![![-5, -9, 0, -6, 4]], ![![22, 57, -25, -89, 0]], ![![49, 132, -24, -132, -37]]]
  g := ![![![-669, 1419, -631, 114, -226], ![349, -725, 316, -60, 114], ![-149, 354, -173, 24, -60], ![100, -213, 95, -17, 34], ![99, -177, 65, -18, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N3 : Nat.card (O ⧸ I23N3) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N3)

lemma isPrimeI23N3 : Ideal.IsPrime I23N3 := prime_ideal_of_norm_prime hp23.out _ NI23N3
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![-19213, -10246, 4540, -828, 1628]] ![![-41645, -69603, 22107, -10108, 8376]]
  ![![58841, 98357, -31239, 14284, -11836]] where
 M := ![![![58841, 98357, -31239, 14284, -11836]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI23N1 : IdealMulLeCertificate' Table 
  ![![58841, 98357, -31239, 14284, -11836]] ![![-1085, -3095, -2988, -1473, -517]]
  ![![-219097, -365168, 119139, -52217, 44651]] where
 M := ![![![-219097, -365168, 119139, -52217, 44651]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI23N2 : IdealMulLeCertificate' Table 
  ![![-219097, -365168, 119139, -52217, 44651]] ![![2665, 1419, -631, 114, -226]]
  ![![23, 0, 0, 0, 0]] where
 M := ![![![-442405, -757643, 187772, -123671, 79327]]]
 hmul := by decide  
 g := ![![![![-19235, -32941, 8164, -5377, 3449]]]]
 hle2 := by decide  


def PBC23 : ContainsPrimesAboveP 23 ![I23N0, I23N1, I23N2, I23N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N1
    exact isPrimeI23N2
    exact isPrimeI23N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 23 (by decide) (𝕀 ⊙ MulI23N0 ⊙ MulI23N1 ⊙ MulI23N2)


lemma PB1556I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB1556I0 : PrimesBelowBoundCertificateInterval O 1 23 1556 where
  m := 9
  g := ![5, 5, 5, 2, 1, 2, 3, 3, 4]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB1556I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N0, I3N1, I3N1, I3N1]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1]
    · exact ![I11N0]
    · exact ![I13N0, I13N1]
    · exact ![I17N0, I17N1, I17N2]
    · exact ![I19N0, I19N1, I19N2]
    · exact ![I23N0, I23N1, I23N2, I23N3]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC2
    · exact PBC3
    · exact PBC5
    · exact PBC7
    · exact PBC11
    · exact PBC13
    · exact PBC17
    · exact PBC19
    · exact PBC23
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2, 2, 2, 2, 2]
    · exact ![3, 3, 3, 3, 3]
    · exact ![5, 5, 5, 5, 5]
    · exact ![2401, 7]
    · exact ![161051]
    · exact ![28561, 13]
    · exact ![289, 289, 17]
    · exact ![6859, 19, 19]
    · exact ![529, 23, 23, 23]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N1
      exact NI2N1
      exact NI2N2
      exact NI2N2
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N0
      exact NI3N1
      exact NI3N1
      exact NI3N1
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N0
      exact NI5N0
      exact NI5N0
      exact NI5N0
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N1
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
      exact NI17N2
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
      exact NI19N2
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
      exact NI23N2
      exact NI23N3
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I5N0, I7N1, I13N1, I17N0, I17N1, I17N2, I19N1, I19N2, I23N0, I23N1, I23N2, I23N3]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N0, I3N1, I3N1, I3N1], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N1], [], [I13N1], [I17N0, I17N1, I17N2], [I19N1, I19N2], [I23N0, I23N1, I23N2, I23N3]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
