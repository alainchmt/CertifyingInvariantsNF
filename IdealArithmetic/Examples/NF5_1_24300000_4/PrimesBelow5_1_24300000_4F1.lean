
import IdealArithmetic.Examples.NF5_1_24300000_4.RI5_1_24300000_4
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![169, -69, 88, 56, -87]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![169, -69, 88, 56, -87]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![12, 1, 1, 0, 0], ![23, 6, 0, 1, 0], ![22, 9, 0, 0, 1]] where
  M :=![![![169, -69, 88, 56, -87], ![-348, 226, -243, 2, 112], ![448, -477, 450, -262, 4], ![182, 207, -113, 453, -318], ![-462, -11, -93, -432, 397]]]
  hmulB := by decide  
  f := ![![![-149, -121, -30, 14, 13]], ![![52, -152, -95, -34, 28]], ![![-56, -57, -19, 0, 4]], ![![-113, -128, -45, -1, 11]], ![![-108, -145, -56, -6, 13]]]
  g := ![![![-9, 10, 88, 56, -87], ![2, -19, -243, 2, 112], ![34, 21, 450, -262, 4], ![-65, 16, -113, 453, -318], ![64, -31, -93, -432, 397]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [24, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [13, 28], [0, 1]]
 g := ![![[20, 23], [23], [], [13, 1]], ![[0, 6], [23], [], [26, 28]]]
 h' := ![![[13, 28], [28, 9], [0, 20], [7], [0, 1]], ![[0, 1], [0, 20], [28, 9], [7], [13, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [26, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [24, 16, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2174, 2444, 1800, 2386, 1136]
  a := ![0, -8, -3, -4, -11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3424, -824, 1800, 2386, 1136]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![133, -182, -139, -76, 21]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![133, -182, -139, -76, 21]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![27, 8, 1, 0, 0], ![8, 11, 0, 1, 0], ![11, 4, 0, 0, 1]] where
  M :=![![![133, -182, -139, -76, 21], ![84, -61, -140, -236, -152], ![-608, -444, -365, -584, -472], ![-986, -984, -624, -719, -508], ![-1058, -1388, -930, -1014, -643]]]
  hmulB := by decide  
  f := ![![![2591, -474, 917, 1674, -1799]], ![![-7196, 3383, -4072, -1764, 3348]], ![![889, 158, 78, 1022, -873]], ![![-2134, 1413, -1510, 49, 666]], ![![-101, 134, -121, 96, -22]]]
  g := ![![![147, 58, -139, -76, 21], ![256, 147, -140, -236, -152], ![659, 372, -365, -584, -472], ![938, 481, -624, -719, -508], ![1353, 682, -930, -1014, -643]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P1 : CertificateIrreducibleZModOfList' 29 2 2 4 [16, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 28], [0, 1]]
 g := ![![[24, 20], [22], [1, 16], [22, 1]], ![[0, 9], [22], [5, 13], [15, 28]]]
 h' := ![![[22, 28], [20, 7], [13, 14], [25, 4], [0, 1]], ![[0, 1], [0, 22], [2, 15], [26, 25], [22, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [14, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N1 : CertifiedPrimeIdeal' SI29N1 29 where
  n := 2
  hpos := by decide
  P := [16, 7, 1]
  hirr := P29P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10616, 36401, -1129, 14006, 25310]
  a := ![3, -61, 2, -65, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-12779, -7237, -1129, 14006, 25310]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N1 B_one_repr
lemma NI29N1 : Nat.card (O ⧸ I29N1) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N1

def I29N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, -1, 1, 2, -2]] i)))

def SI29N2: IdealEqSpanCertificate' Table ![![3, -1, 1, 2, -2]] 
 ![![29, 0, 0, 0, 0], ![20, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![17, 0, 0, 1, 0], ![23, 0, 0, 0, 1]] where
  M :=![![![3, -1, 1, 2, -2], ![-8, 4, -5, -2, 4], ![16, -11, 12, -2, -4], ![-4, 9, -7, 9, -4], ![-4, -5, 3, -10, 7]]]
  hmulB := by decide  
  f := ![![![7, 31, 15, 2, -6]], ![![4, 22, 11, 2, -4]], ![![2, 7, 4, 2, 0]], ![![7, 20, 10, 3, -2]], ![![9, 28, 14, 4, -3]]]
  g := ![![![1, -1, 1, 2, -2], ![-4, 4, -5, -2, 4], ![10, -11, 12, -2, -4], ![-7, 9, -7, 9, -4], ![3, -5, 3, -10, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N2 : Nat.card (O ⧸ I29N2) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N2)

lemma isPrimeI29N2 : Ideal.IsPrime I29N2 := prime_ideal_of_norm_prime hp29.out _ NI29N2
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![169, -69, 88, 56, -87]] ![![133, -182, -139, -76, 21]]
  ![![7, 31, 15, 2, -6]] where
 M := ![![![7, 31, 15, 2, -6]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI29N1 : IdealMulLeCertificate' Table 
  ![![7, 31, 15, 2, -6]] ![![3, -1, 1, 2, -2]]
  ![![29, 0, 0, 0, 0]] where
 M := ![![![29, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N1, I29N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N1
    exact isPrimeI29N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0 ⊙ MulI29N1)
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 139, 100, 112, 69]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![89, 139, 100, 112, 69]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![7, 5, 30, 1, 0], ![7, 24, 17, 0, 1]] where
  M :=![![![89, 139, 100, 112, 69], ![276, 370, 277, 338, 224], ![896, 1115, 818, 1002, 676], ![1214, 1511, 1095, 1325, 890], ![1642, 2077, 1507, 1816, 1213]]]
  hmulB := by decide  
  f := ![![![-55, 13, -22, -30, 35]], ![![140, -72, 83, 26, -60]], ![![-240, 189, -192, 46, 52]], ![![-221, 170, -174, 37, 51]], ![![-33, 53, -47, 44, -14]]]
  g := ![![![-38, -67, -143, 112, 69], ![-118, -216, -441, 338, 224], ![-350, -649, -1314, 1002, 676], ![-461, -854, -1735, 1325, 890], ![-631, -1165, -2374, 1816, 1213]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 3 2 4 [25, 18, 12, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [24, 21, 5], [26, 9, 26], [0, 1]]
 g := ![![[4, 0, 14], [0, 10, 1], [27, 6, 20], [1]], ![[24, 6, 15, 16], [9, 15, 8, 20], [11, 30, 20, 7], [2, 26, 13, 1]], ![[27, 29, 20, 3], [9, 10, 14, 17], [3, 5, 3, 3], [22, 11, 5, 30]]]
 h' := ![![[24, 21, 5], [0, 16, 13], [7, 20, 30], [6, 13, 19], [0, 1]], ![[26, 9, 26], [15, 25, 11], [17, 29, 29], [10, 14, 19], [24, 21, 5]], ![[0, 1], [19, 21, 7], [21, 13, 3], [7, 4, 24], [26, 9, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21, 10], []]
 b := ![[], [4, 17, 29], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 3
  hpos := by decide
  P := [25, 18, 12, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-81354, -103526, -74603, -91863, -60158]
  a := ![1, -6, -1, -5, -4]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![31703, 58051, 119483, -91863, -60158]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 29791 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-55, 13, -22, -30, 35]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![-55, 13, -22, -30, 35]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![21, 2, 1, 0, 0], ![10, 9, 0, 1, 0], ![14, 12, 0, 0, 1]] where
  M :=![![![-55, 13, -22, -30, 35], ![140, -72, 83, 26, -60], ![-240, 189, -192, 46, 52], ![34, -131, 105, -153, 76], ![82, 67, -31, 168, -123]]]
  hmulB := by decide  
  f := ![![![89, 139, 100, 112, 69]], ![![276, 370, 277, 338, 224]], ![![107, 154, 112, 130, 83]], ![![148, 201, 148, 177, 116]], ![![200, 273, 201, 240, 157]]]
  g := ![![![7, -3, -22, -30, 35], ![-33, 8, 83, 26, -60], ![84, -15, -192, 46, 52], ![-55, 4, 105, -153, 76], ![25, 3, -31, 168, -123]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P1 : CertificateIrreducibleZModOfList' 31 2 2 4 [19, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 30], [0, 1]]
 g := ![![[1, 18], [24, 14], [21, 1], [12, 1]], ![[0, 13], [6, 17], [2, 30], [24, 30]]]
 h' := ![![[12, 30], [9, 7], [4, 13], [20, 1], [0, 1]], ![[0, 1], [0, 24], [5, 18], [1, 30], [12, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [2, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N1 : CertifiedPrimeIdeal' SI31N1 31 where
  n := 2
  hpos := by decide
  P := [19, 19, 1]
  hirr := P31P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8901, 10752, 8405, 9440, 6763]
  a := ![1, 26, 4, 18, 15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-11506, -5554, 8405, 9440, 6763]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N1 B_one_repr
lemma NI31N1 : Nat.card (O ⧸ I31N1) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![89, 139, 100, 112, 69]] ![![-55, 13, -22, -30, 35]]
  ![![31, 0, 0, 0, 0]] where
 M := ![![![31, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0)
instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6189, -3040, 3599, 1334, -2775]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![6189, -3040, 3599, 1334, -2775]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![5, 34, 5, 1, 0], ![12, 2, 29, 0, 1]] where
  M :=![![![6189, -3040, 3599, 1334, -2775], ![-11100, 8347, -8590, 1648, 2668], ![10672, -15374, 13683, -11844, 3296], ![12142, 3730, -96, 16155, -13178], ![-20806, 3338, -7018, -14098, 14821]]]
  hmulB := by decide  
  f := ![![![13543, 17136, 12499, 15140, 10133]], ![![40532, 51315, 37402, 45264, 30280]], ![![121120, 153478, 111875, 135364, 90528]], ![![59789, 75718, 55192, 66791, 44677]], ![![107466, 136166, 99259, 120106, 80327]]]
  g := ![![![887, -1158, 2092, 1334, -2775], ![-1388, -1433, -2546, 1648, 2668], ![820, 10290, -613, -11844, 3296], ![2419, -14032, 8143, 16155, -13178], ![-3464, 12244, -9901, -14098, 14821]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [4, 2, 21, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 33, 14], [6, 3, 23], [0, 1]]
 g := ![![[16, 5, 1], [29, 10], [23, 20, 25], [16, 1], []], ![[7, 8], [31, 26], [1, 20, 17, 14], [1, 9], [27, 11]], ![[5, 20, 9, 23], [14, 1], [15, 24, 16, 14], [16, 16], [18, 11]]]
 h' := ![![[10, 33, 14], [23, 24, 36], [19, 11, 26], [10, 1, 32], [0, 0, 1], [0, 1]], ![[6, 3, 23], [12, 8], [32, 27, 10], [23, 35, 36], [29, 7, 3], [10, 33, 14]], ![[0, 1], [18, 5, 1], [0, 36, 1], [11, 1, 6], [1, 30, 33], [6, 3, 23]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 18], []]
 b := ![[], [1, 3, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [4, 2, 21, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-730440, -425092, -635956, -504744, -297594]
  a := ![-1, -6, -4, 5, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![144984, 468416, 284270, -504744, -297594]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 50653 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-691, 383, -434, -88, 275]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-691, 383, -434, -88, 275]] 
 ![![37, 0, 0, 0, 0], ![11, 1, 0, 0, 0], ![27, 0, 1, 0, 0], ![31, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  M :=![![![-691, 383, -434, -88, 275], ![1100, -938, 933, -318, -176], ![-704, 1539, -1290, 1514, -636], ![-1822, -89, -333, -1767, 1602], ![2654, -691, 1091, 1428, -1679]]]
  hmulB := by decide  
  f := ![![![-6737, -8325, -6088, -7450, -5033]], ![![-2547, -3159, -2307, -2816, -1899]], ![![-6527, -8120, -5932, -7236, -4875]], ![![-7777, -9684, -7077, -8633, -5815]], ![![-4563, -5732, -4185, -5086, -3414]]]
  g := ![![![191, 383, -434, -88, 275], ![-63, -938, 933, -318, -176], ![-649, 1539, -1290, 1514, -636], ![1311, -89, -333, -1767, 1602], ![-1307, -691, 1091, 1428, -1679]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-76609, 2690, -18754, -65312, 62228]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![-76609, 2690, -18754, -65312, 62228]] 
 ![![37, 0, 0, 0, 0], ![16, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![26, 0, 0, 0, 1]] where
  M :=![![![-76609, 2690, -18754, -65312, 62228], ![248912, -98447, 127146, 86948, -130624], ![-522496, 332382, -359695, -6956, 173896], ![223336, -308402, 276514, -229273, 58356], ![-7744, 213690, -159418, 291396, -163961]]]
  hmulB := by decide  
  f := ![![![-845701, -1068874, -778350, -941616, -630068]], ![![-433824, -548587, -399530, -483316, -323360]], ![![-272163, -344756, -251277, -304036, -203348]], ![![-384749, -487112, -355016, -429609, -287384]], ![![-964698, -1220366, -889050, -1075684, -719665]]]
  g := ![![![-36615, 2690, -18754, -65312, 62228], ![119030, -98447, 127146, 86948, -130624], ![-249947, 332382, -359695, -6956, 173896], ![106955, -308402, 276514, -229273, 58356], ![-3852, 213690, -159418, 291396, -163961]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![6189, -3040, 3599, 1334, -2775]] ![![-691, 383, -434, -88, 275]]
  ![![-19949693, 12559567, -13636803, -448904, 6744344]] where
 M := ![![![-19949693, 12559567, -13636803, -448904, 6744344]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![-19949693, 12559567, -13636803, -448904, 6744344]] ![![-76609, 2690, -18754, -65312, 62228]]
  ![![37, 0, 0, 0, 0]] where
 M := ![![![11627243368749, -4243102460597, 5676827030941, 4558037613416, -6385401498708]]]
 hmul := by decide  
 g := ![![![![314249820777, -114678444881, 153427757593, 123190205768, -172578418884]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1, I37N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
    exact isPrimeI37N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0 ⊙ MulI37N1)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-33787, 7535, -12957, -19940, 22380]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![-33787, 7535, -12957, -19940, 22380]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![3, 11, 9, 1, 0], ![14, 10, 27, 0, 1]] where
  M :=![![![-33787, 7535, -12957, -19940, 22380], ![89520, -44304, 52295, 18846, -39880], ![-159520, 120781, -124064, 24830, 37692], ![30624, -88379, 71935, -95795, 44770], ![44780, 47919, -25567, 107282, -75855]]]
  hmulB := by decide  
  f := ![![![1221, 1387, 605, 292, 104]], ![![416, 2222, 1595, 1418, 584]], ![![2336, 4013, 3390, 4358, 2836]], ![![847, 1709, 1315, 1493, 886]], ![![2250, 3864, 2973, 3496, 2173]]]
  g := ![![![-7007, 75, -10677, -19940, 22380], ![14422, 3590, 23401, 18846, -39880], ![-18578, -12909, -33298, 24830, 37692], ![-7531, 12626, -6700, -95795, 44770], ![19144, -9113, 25780, 107282, -75855]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [38, 13, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 6, 28], [32, 34, 13], [0, 1]]
 g := ![![[15, 20, 40], [24, 20], [19, 23], [12, 36, 1], []], ![[24, 24, 37, 27], [21, 23], [38, 36], [39, 0, 22, 19], [24, 5]], ![[17, 34, 14, 26], [8, 37], [16, 4], [11, 33, 8, 17], [39, 5]]]
 h' := ![![[4, 6, 28], [31, 35, 9], [0, 15, 26], [36, 34, 8], [0, 0, 1], [0, 1]], ![[32, 34, 13], [20, 19, 15], [11, 12, 33], [15, 16, 35], [6, 38, 34], [4, 6, 28]], ![[0, 1], [22, 28, 17], [11, 14, 23], [2, 32, 39], [34, 3, 6], [32, 34, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39, 35], []]
 b := ![[], [9, 1, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [38, 13, 5, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![720030, -284602, 372664, 245498, -370422]
  a := ![0, -2, 4, -18, 14]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![126084, 17540, 199136, 245498, -370422]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 68921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1221, 1387, 605, 292, 104]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![1221, 1387, 605, 292, 104]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![11, 23, 1, 0, 0], ![17, 8, 0, 1, 0], ![38, 40, 0, 0, 1]] where
  M :=![![![1221, 1387, 605, 292, 104], ![416, 2222, 1595, 1418, 584], ![2336, 4013, 3390, 4358, 2836], ![5464, 5349, 4045, 5517, 4066], ![7924, 8435, 5943, 7402, 5225]]]
  hmulB := by decide  
  f := ![![![-33787, 7535, -12957, -19940, 22380]], ![![89520, -44304, 52295, 18846, -39880]], ![![37263, -19886, 22834, 5828, -15448]], ![![4205, -7676, 6586, -6927, 2590]], ![![57114, -35071, 38387, 2522, -20015]]]
  g := ![![![-350, -464, 605, 292, 104], ![-1547, -1687, 1595, 1418, 584], ![-5288, -5421, 3390, 4358, 2836], ![-7008, -7182, 4045, 5517, 4066], ![-9313, -9670, 5943, 7402, 5225]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P1 : CertificateIrreducibleZModOfList' 41 2 2 5 [37, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 40], [0, 1]]
 g := ![![[37, 10], [9], [18], [40, 10], [1]], ![[0, 31], [9], [18], [3, 31], [1]]]
 h' := ![![[25, 40], [31, 25], [6, 38], [37, 31], [4, 25], [0, 1]], ![[0, 1], [0, 16], [13, 3], [33, 10], [14, 16], [25, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [12, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N1 : CertifiedPrimeIdeal' SI41N1 41 where
  n := 2
  hpos := by decide
  P := [37, 16, 1]
  hirr := P41P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1644, 2048, 734, 2234, 234]
  a := ![13, -6, -3, 2, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1300, -1026, 734, 2234, 234]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N1 B_one_repr
lemma NI41N1 : Nat.card (O ⧸ I41N1) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![-33787, 7535, -12957, -19940, 22380]] ![![1221, 1387, 605, 292, 104]]
  ![![41, 0, 0, 0, 0]] where
 M := ![![![41, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1861, 2363, 1733, 2108, 1412]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![1861, 2363, 1733, 2108, 1412]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![29, 31, 35, 6, 1]] where
  M :=![![![1861, 2363, 1733, 2108, 1412], ![5648, 7114, 5187, 6290, 4216], ![16864, 21341, 15546, 18806, 12580], ![22336, 28341, 20657, 24981, 16698], ![30572, 38779, 28275, 34210, 22873]]]
  hmulB := by decide  
  f := ![![![-1, 21, -15, 28, -16]], ![![-64, -4, -11, -62, 56]], ![![224, -81, 108, 90, -124]], ![![-216, 151, -159, 15, 62]], ![![109, -37, 51, 48, -63]]]
  g := ![![![-909, -963, -1109, -148, 1412], ![-2712, -2874, -3311, -442, 4216], ![-8092, -8573, -9878, -1318, 12580], ![-10742, -11379, -13111, -1749, 16698], ![-14715, -15588, -17960, -2396, 22873]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 4 2 5 [30, 41, 27, 15, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 16, 36, 23], [15, 10, 39, 36], [0, 16, 11, 27], [0, 1]]
 g := ![![[1, 23, 1, 21], [40, 42, 33, 40], [30, 16, 31], [28, 1], []], ![[4, 22, 6, 13, 33, 35], [26, 11, 10, 36, 10, 13], [10, 38, 36], [21, 4, 31, 16, 37, 17], [19, 42, 13]], ![[7, 29, 36, 36, 22, 6], [13, 37, 37, 33, 39, 11], [2, 21, 1], [35, 37, 7, 13, 5, 13], [9, 9, 6]], ![[0, 22, 25, 10, 28, 42], [33, 41, 9, 8, 26, 7], [6, 33, 15], [26, 42, 8, 1, 11, 22], [21, 22, 41]]]
 h' := ![![[13, 16, 36, 23], [4, 22, 9, 8], [16, 18, 26, 13], [20, 26, 20, 26], [0, 0, 1], [0, 1]], ![[15, 10, 39, 36], [19, 37, 17, 40], [32, 41, 41, 25], [26, 0, 41, 6], [29, 11, 29, 13], [13, 16, 36, 23]], ![[0, 16, 11, 27], [10, 42, 42, 6], [27, 39, 8, 25], [42, 33, 25, 42], [41, 5, 5, 32], [15, 10, 39, 36]], ![[0, 1], [42, 28, 18, 32], [28, 31, 11, 23], [37, 27, 0, 12], [15, 27, 8, 41], [0, 16, 11, 27]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [26, 37, 41], []]
 b := ![[], [], [14, 30, 31, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 4
  hpos := by decide
  P := [30, 41, 27, 15, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![963626, 1551928, 1484886, 744860, 1785950]
  a := ![-1, 0, 2, -4, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1182068, -1251454, -1419148, -231880, 1785950]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 3418801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 21, -15, 28, -16]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-1, 21, -15, 28, -16]] 
 ![![43, 0, 0, 0, 0], ![31, 1, 0, 0, 0], ![28, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![18, 0, 0, 0, 1]] where
  M :=![![![-1, 21, -15, 28, -16], ![-64, -4, -11, -62, 56], ![224, -81, 108, 90, -124], ![-216, 151, -159, 15, 62], ![156, -147, 143, -66, -13]]]
  hmulB := by decide  
  f := ![![![1861, 2363, 1733, 2108, 1412]], ![![1473, 1869, 1370, 1666, 1116]], ![![1604, 2035, 1490, 1810, 1212]], ![![606, 769, 561, 679, 454]], ![![1490, 1891, 1383, 1678, 1123]]]
  g := ![![![0, 21, -15, 28, -16], ![-12, -4, -11, -62, 56], ![41, -81, 108, 90, -124], ![-37, 151, -159, 15, 62], ![25, -147, 143, -66, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![1861, 2363, 1733, 2108, 1412]] ![![-1, 21, -15, 28, -16]]
  ![![43, 0, 0, 0, 0]] where
 M := ![![![43, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1351533, 716756, -824862, -217682, 563900]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-1351533, 716756, -824862, -217682, 563900]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![8, 46, 2, 12, 1]] where
  M :=![![![-1351533, 716756, -824862, -217682, 563900], ![2255600, -1830177, 1844556, -521924, -435364], ![-1741456, 3142868, -2700905, 2818384, -1043848], ![-3215496, -418824, -394692, -3483791, 3036066], ![4944332, -1113868, 1904376, 2902336, -3266109]]]
  hmulB := by decide  
  f := ![![![3205, 3068, 2754, 4234, 3200]], ![![12800, 13393, 9468, 11908, 8468]], ![![33872, 42644, 30329, 35872, 23816]], ![![41232, 55248, 40404, 48191, 31638]], ![![26252, 31126, 22502, 27612, 18859]]]
  g := ![![![-124739, -536652, -41546, -148606, 563900], ![122096, 387161, 57772, 100052, -435364], ![140624, 1088508, -13047, 326480, -1043848], ![-585192, -2980380, -137592, -849289, 3036066], ![661132, 3172918, 179502, 895652, -3266109]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 4 2 5 [2, 23, 40, 27, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 40, 39, 8], [26, 36, 21, 41], [36, 17, 34, 45], [0, 1]]
 g := ![![[21, 4, 27, 3], [36, 16, 41, 9], [4, 22, 13, 21], [20, 1], []], ![[20, 43, 11, 26, 26, 4], [16, 42, 18, 28, 25, 14], [3, 42, 42, 45, 18, 12], [35, 5, 32, 10, 7, 37], [34, 24, 17]], ![[40, 31, 7, 20, 16, 5], [25, 31, 40, 46, 27, 44], [8, 30, 42, 0, 31, 10], [28, 28, 42, 36, 21, 15], [33, 45, 36]], ![[12, 0, 39, 30, 2, 39], [28, 6, 26, 33, 10, 39], [31, 28, 46, 20, 44, 45], [31, 13, 44, 29, 46, 19], [43, 38, 4]]]
 h' := ![![[5, 40, 39, 8], [22, 3, 19, 35], [39, 7, 31, 44], [7, 8, 23, 31], [0, 0, 1], [0, 1]], ![[26, 36, 21, 41], [28, 20, 31, 27], [24, 36, 20, 32], [10, 15, 32, 42], [4, 40, 44, 38], [5, 40, 39, 8]], ![[36, 17, 34, 45], [32, 27, 12, 30], [25, 37, 27, 20], [17, 2, 3, 22], [46, 36, 8, 31], [26, 36, 21, 41]], ![[0, 1], [28, 44, 32, 2], [21, 14, 16, 45], [46, 22, 36, 46], [35, 18, 41, 25], [36, 17, 34, 45]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [13, 7, 46], []]
 b := ![[], [], [37, 43, 0, 39], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 4
  hpos := by decide
  P := [2, 23, 40, 27, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![877181863, 1151029466, 823006459, 996050853, 690654301]
  a := ![3, 10, 7, -1, 21]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-98894735, -651469540, -11878769, -155144697, 690654301]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 4879681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3205, -3068, -2754, -4234, -3200]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-3205, -3068, -2754, -4234, -3200]] 
 ![![47, 0, 0, 0, 0], ![23, 1, 0, 0, 0], ![35, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![26, 0, 0, 0, 1]] where
  M :=![![![-3205, -3068, -2754, -4234, -3200], ![-12800, -13393, -9468, -11908, -8468], ![-33872, -42644, -30329, -35872, -23816], ![-41232, -55248, -40404, -48191, -31638], ![-56876, -74036, -54528, -66088, -43957]]]
  hmulB := by decide  
  f := ![![![1351533, -716756, 824862, 217682, -563900]], ![![613397, -311813, 364410, 117630, -266688]], ![![1043513, -600624, 671725, 102138, -397716]], ![![327219, -128340, 166350, 115807, -172578]], ![![642458, -372804, 415788, 58668, -242453]]]
  g := ![![![6065, -3068, -2754, -4234, -3200], ![20297, -13393, -9468, -11908, -8468], ![62777, -42644, -30329, -35872, -23816], ![82977, -55248, -40404, -48191, -31638], ![112598, -74036, -54528, -66088, -43957]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-1351533, 716756, -824862, -217682, 563900]] ![![-3205, -3068, -2754, -4234, -3200]]
  ![![47, 0, 0, 0, 0]] where
 M := ![![![-47, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 17, 4, 8, -13]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![29, 17, 4, 8, -13]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![10, 15, 16, 32, 1]] where
  M :=![![![29, 17, 4, 8, -13], ![-52, 28, -9, -18, 16], ![64, -63, 60, 14, -36], ![-46, 37, -63, 33, 6], ![38, -49, 29, -48, 25]]]
  hmulB := by decide  
  f := ![![![-1, -3, -2, -2, -1]], ![![-4, -6, -5, -6, -4]], ![![-16, -19, -14, -18, -12]], ![![-22, -27, -19, -23, -16]], ![![-20, -25, -18, -22, -15]]]
  g := ![![![3, 4, 4, 8, -13], ![-4, -4, -5, -10, 16], ![8, 9, 12, 22, -36], ![-2, -1, -3, -3, 6], ![-4, -8, -7, -16, 25]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 4 2 5 [31, 5, 23, 47, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 15, 51, 22], [27, 7, 13, 14], [26, 30, 42, 17], [0, 1]]
 g := ![![[34, 27, 25, 43], [24, 47, 42], [32, 20, 17, 38], [13, 6, 1], []], ![[33, 12, 42, 11, 51, 14], [31, 31, 1], [31, 40, 10, 49, 2, 50], [28, 37, 28], [14, 2, 47, 50, 34, 48]], ![[5, 31, 40, 0, 1, 51], [23, 0, 15], [15, 28, 8, 16, 15, 34], [43, 1, 40], [41, 8, 21, 0, 46, 41]], ![[37, 50, 44, 33, 20, 40], [3, 20, 10], [44, 16, 7, 19, 15, 42], [28, 30, 44], [5, 51, 32, 32, 13, 37]]]
 h' := ![![[6, 15, 51, 22], [11, 19, 12, 19], [15, 32, 20, 28], [21, 14, 11, 41], [0, 0, 0, 1], [0, 1]], ![[27, 7, 13, 14], [4, 24, 39, 16], [45, 48, 39, 1], [16, 43, 14, 6], [47, 4, 31, 9], [6, 15, 51, 22]], ![[26, 30, 42, 17], [16, 31, 3, 42], [26, 13, 20, 11], [9, 2, 15, 40], [21, 16, 26, 27], [27, 7, 13, 14]], ![[0, 1], [41, 32, 52, 29], [44, 13, 27, 13], [24, 47, 13, 19], [37, 33, 49, 16], [26, 30, 42, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [17, 45, 16], []]
 b := ![[], [], [8, 18, 2, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 4
  hpos := by decide
  P := [31, 5, 23, 47, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![18403679, 23632612, 17469752, 20343304, 14624694]
  a := ![1, 4, 2, -2, 9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2412137, -3693166, -4085384, -8446168, 14624694]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 7890481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -3, -2, -2, -1]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-1, -3, -2, -2, -1]] 
 ![![53, 0, 0, 0, 0], ![42, 1, 0, 0, 0], ![38, 0, 1, 0, 0], ![29, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![-1, -3, -2, -2, -1], ![-4, -6, -5, -6, -4], ![-16, -19, -14, -18, -12], ![-22, -27, -19, -23, -16], ![-30, -37, -27, -32, -21]]]
  hmulB := by decide  
  f := ![![![29, 17, 4, 8, -13]], ![![22, 14, 3, 6, -10]], ![![22, 11, 4, 6, -10]], ![![15, 10, 1, 5, -7]], ![![4, 1, 1, 0, -1]]]
  g := ![![![5, -3, -2, -2, -1], ![12, -6, -5, -6, -4], ![36, -19, -14, -18, -12], ![49, -27, -19, -23, -16], ![68, -37, -27, -32, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![29, 17, 4, 8, -13]] ![![-1, -3, -2, -2, -1]]
  ![![53, 0, 0, 0, 0]] where
 M := ![![![53, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3580943, 2659925, -2747084, 485626, 887119]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-3580943, 2659925, -2747084, 485626, 887119]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![23, 18, 56, 36, 1]] where
  M :=![![![-3580943, 2659925, -2747084, 485626, 887119], ![3548476, -4955282, 4434163, -3719930, 971252], ![3885008, 5233961, -3012778, 10810830, -7439860], ![-16653958, 4599241, -7039961, -8592673, 10325204], ![18876170, -8503053, 10407743, 5145208, -9078299]]]
  hmulB := by decide  
  f := ![![![552821, 700079, 510230, 617384, 412957]], ![![1651828, 2093392, 1525993, 1846374, 1234768]], ![![4939072, 6258963, 4562928, 5521522, 3692748]], ![![6559582, 8311439, 6059233, 7332489, 4904138]], ![![9562087, 12116570, 8833159, 10688976, 7148844]]]
  g := ![![![-406520, -225563, -888572, -533062, 887119], ![-318480, -380302, -846711, -655678, 971252], ![2966132, 2358499, 7010498, 4722810, -7439860], ![-4307350, -3072109, -9919515, -6445763, 10325204], ![3858933, 2625531, 8793093, 5626508, -9078299]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 4 2 5 [28, 48, 20, 29, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 57, 41, 18], [39, 18, 18, 30], [25, 42, 0, 11], [0, 1]]
 g := ![![[56, 49, 56, 9], [26, 3, 12, 20], [35, 36, 9], [28, 54, 30, 1], []], ![[51, 48, 58, 30, 55, 32], [29, 48, 48, 42, 20, 18], [26, 21, 15], [37, 19, 24, 4, 14, 18], [47, 49, 9, 5, 52, 50]], ![[36, 31, 29, 15, 19, 58], [53, 50, 24, 3, 48, 23], [35, 36, 9], [8, 18, 51, 43, 47, 31], [51, 57, 57, 41, 32, 37]], ![[29, 28, 17, 14, 58, 24], [47, 52, 6, 47, 5, 39], [26, 21, 15], [45, 37, 35, 21, 32, 6], [44, 41, 40, 36, 46, 33]]]
 h' := ![![[25, 57, 41, 18], [39, 19, 16, 56], [17, 16, 48, 16], [42, 35, 20, 3], [0, 0, 0, 1], [0, 1]], ![[39, 18, 18, 30], [21, 22, 15, 21], [8, 14, 50, 58], [38, 29, 16, 29], [31, 56, 58, 1], [25, 57, 41, 18]], ![[25, 42, 0, 11], [21, 33, 55, 23], [21, 9, 44, 39], [23, 24, 39, 56], [12, 33, 53, 48], [39, 18, 18, 30]], ![[0, 1], [7, 44, 32, 18], [1, 20, 35, 5], [27, 30, 43, 30], [56, 29, 7, 9], [25, 42, 0, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [50, 27, 49], []]
 b := ![[], [], [8, 23, 42, 20], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 4
  hpos := by decide
  P := [28, 48, 20, 29, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-76484, 121786, -44350, 40376, 67372]
  a := ![4, -1, -1, 1, -3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-27560, -18490, -64698, -40424, 67372]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 12117361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![552821, 700079, 510230, 617384, 412957]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![552821, 700079, 510230, 617384, 412957]] 
 ![![59, 0, 0, 0, 0], ![46, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![29, 0, 0, 1, 0], ![18, 0, 0, 0, 1]] where
  M :=![![![552821, 700079, 510230, 617384, 412957], ![1651828, 2093392, 1525993, 1846374, 1234768], ![4939072, 6258963, 4562928, 5521522, 3692748], ![6559582, 8311439, 6059233, 7332489, 4904138], ![8982362, 11381025, 8296861, 10040184, 6715105]]]
  hmulB := by decide  
  f := ![![![-3580943, 2659925, -2747084, 485626, 887119]], ![![-2731778, 1989852, -2066639, 315574, 708114]], ![![-419704, 449379, -423550, 249082, -5812]], ![![-2042395, 1385374, -1469583, 93059, 611045]], ![![-772556, 667383, -661691, 235364, 116777]]]
  g := ![![![-1035085, 700079, 510230, 617384, 412957], ![-3095302, 2093392, 1525993, 1846374, 1234768], ![-9255428, 6258963, 4562928, 5521522, 3692748], ![-12290799, 8311439, 6059233, 7332489, 4904138], ![-16829778, 11381025, 8296861, 10040184, 6715105]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-3580943, 2659925, -2747084, 485626, 887119]] ![![552821, 700079, 510230, 617384, 412957]]
  ![![59, 0, 0, 0, 0]] where
 M := ![![![59, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![34371, 71082, -44942, 130240, -85586]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![34371, 71082, -44942, 130240, -85586]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![11, 35, 56, 39, 1]] where
  M :=![![![34371, 71082, -44942, 130240, -85586], ![-342344, 34083, -100090, -261056, 260480], ![1041920, -443010, 555043, 320780, -522112], ![-873052, 680774, -693572, 163459, 190540], ![552252, -623354, 580972, -372504, 33219]]]
  hmulB := by decide  
  f := ![![![-38937, -49434, -36062, -43640, -29174]], ![![-116696, -147813, -107782, -130472, -87280]], ![![-349120, -442230, -322373, -390124, -260944]], ![![-463540, -587374, -428168, -518081, -346484]], ![![-701247, -888425, -647652, -783739, -524195]]]
  g := ![![![15997, 50272, 77834, 56854, -85586], ![-52584, -148897, -240770, -170816, 260480], ![111232, 292310, 488415, 339068, -522112], ![-48672, -98166, -186292, -119141, 190540], ![3063, -29279, -20972, -27345, 33219]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 4 2 5 [47, 11, 3, 29, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [26, 20, 21, 26], [32, 42, 40, 14], [35, 59, 0, 21], [0, 1]]
 g := ![![[28, 9, 58, 60], [55, 2, 36], [33, 21, 12, 48], [52, 45, 32, 1], []], ![[46, 18, 6, 17], [51, 47, 45], [16, 30, 32, 46, 11, 17], [1, 56, 33, 27, 15, 11], [47, 9, 45, 59, 22, 8]], ![[33, 4, 53, 40, 26, 22], [16, 8, 57], [5, 37, 30, 45, 3, 45], [54, 42, 47, 22, 50, 49], [16, 10, 48, 7, 3, 60]], ![[33, 36, 57, 39, 29, 32], [34, 16, 1], [34, 39, 16, 23, 29, 17], [20, 36, 39, 4, 51, 7], [23, 33, 40, 31, 14, 50]]]
 h' := ![![[26, 20, 21, 26], [43, 44, 54, 11], [35, 8, 45, 55], [57, 58, 41, 32], [0, 0, 0, 1], [0, 1]], ![[32, 42, 40, 14], [40, 23, 53], [34, 33, 32, 44], [54, 45, 29, 53], [56, 31, 2, 17], [26, 20, 21, 26]], ![[35, 59, 0, 21], [0, 32, 55, 18], [52, 15, 53, 22], [54, 38, 10, 56], [52, 34, 60, 20], [32, 42, 40, 14]], ![[0, 1], [50, 23, 21, 32], [60, 5, 53, 1], [4, 42, 42, 42], [9, 57, 60, 23], [35, 59, 0, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [59, 34, 52], []]
 b := ![[], [], [43, 31, 15, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 4
  hpos := by decide
  P := [47, 11, 3, 29, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![251218417427, 320993586984, 232184866720, 282556150084, 189006984388]
  a := ![7, -46, -24, -23, -71]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-29964891981, -103184440436, -169708299328, -116208462968, 189006984388]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 13845841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![38937, 49434, 36062, 43640, 29174]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![38937, 49434, 36062, 43640, 29174]] 
 ![![61, 0, 0, 0, 0], ![44, 1, 0, 0, 0], ![16, 0, 1, 0, 0], ![53, 0, 0, 1, 0], ![32, 0, 0, 0, 1]] where
  M :=![![![38937, 49434, 36062, 43640, 29174], ![116696, 147813, 107782, 130472, 87280], ![349120, 442230, 322373, 390124, 260944], ![463540, 587374, 428168, 518081, 346484], ![634620, 804230, 586280, 709416, 474441]]]
  hmulB := by decide  
  f := ![![![-34371, -71082, 44942, -130240, 85586]], ![![-19180, -51831, 34058, -89664, 57464]], ![![-26096, -11382, 2689, -39420, 31008]], ![![-15551, -72920, 50418, -115839, 71238]], ![![-27084, -27070, 14052, -62216, 44353]]]
  g := ![![![-97699, 49434, 36062, 43640, 29174], ![-292124, 147813, 107782, 130472, 87280], ![-873668, 442230, 322373, 390124, 260944], ![-1160285, 587374, 428168, 518081, 346484], ![-1588740, 804230, 586280, 709416, 474441]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![34371, 71082, -44942, 130240, -85586]] ![![38937, 49434, 36062, 43640, 29174]]
  ![![61, 0, 0, 0, 0]] where
 M := ![![![-61, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0)


lemma PB307I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB307I1 : PrimesBelowBoundCertificateInterval O 23 61 307 where
  m := 9
  g := ![3, 2, 3, 2, 2, 2, 2, 2, 2]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB307I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1, I29N2]
    · exact ![I31N0, I31N1]
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC29
    · exact PBC31
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
    · exact PBC53
    · exact PBC59
    · exact PBC61
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![841, 841, 29]
    · exact ![29791, 961]
    · exact ![50653, 37, 37]
    · exact ![68921, 1681]
    · exact ![3418801, 43]
    · exact ![4879681, 47]
    · exact ![7890481, 53]
    · exact ![12117361, 59]
    · exact ![13845841, 61]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
      exact NI29N2
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
      exact NI37N2
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
  β := ![I29N2, I37N1, I37N2, I43N1, I47N1, I53N1, I59N1, I61N1]
  Il := ![[I29N2], [], [I37N1, I37N2], [], [I43N1], [I47N1], [I53N1], [I59N1], [I61N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
