
import IdealArithmetic.Examples.NF5_3_112500000_1.RI5_3_112500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-30, -18, 4, 9, 0]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![-30, -18, 4, 9, 0]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-30, -18, 4, 9, 0], ![8, -25, -28, 6, 18], ![188, 102, -35, -54, 6], ![-39, 5, 30, 3, -17], ![-217, -92, 62, 53, -23]]]
  hmulB := by decide  
  f := ![![![596, 9, 28, 129, -81]], ![![-944, -16, -44, -207, 129]], ![![1504, 27, 69, 333, -207]], ![![-1563, -29, -72, -347, 215]], ![![1715, 32, 78, 382, -237]]]
  g := ![![![-15, -18, 4, 9, 0], ![-5, -25, -28, 6, 18], ![91, 102, -35, -54, 6], ![-11, 5, 30, 3, -17], ![-97, -92, 62, 53, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 2, 3, 14, -8]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![59, 2, 3, 14, -8]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![59, 2, 3, 14, -8], ![-186, -2, -6, -42, 28], ![330, 15, 20, 80, -42], ![-322, -4, -11, -73, 48], ![336, 21, 25, 84, -39]]]
  hmulB := by decide  
  f := ![![![-16, -5, 2, 2, 0]], ![![2, -8, -3, 4, 2]], ![![13, 11, -8, -8, 4]], ![![1, 2, 6, 1, -4]], ![![-43, -10, 13, 6, -5]]]
  g := ![![![25, 2, 3, 14, -8], ![-83, -2, -6, -42, 28], ![136, 15, 20, 80, -42], ![-143, -4, -11, -73, 48], ![133, 21, 25, 84, -39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-27, -1, -1, -7, 4]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![-27, -1, -1, -7, 4]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-27, -1, -1, -7, 4], ![94, 3, 4, 24, -14], ![-164, -6, -7, -40, 24], ![173, 6, 7, 42, -25], ![-167, -4, -7, -41, 24]]]
  hmulB := by decide  
  f := ![![![-5, -3, -2, -2, -1]], ![![-14, -7, -6, -6, -2]], ![![-30, -16, -15, -16, -6]], ![![-23, -11, -9, -10, -4]], ![![-66, -34, -27, -29, -12]]]
  g := ![![![-12, -1, -1, -7, 4], ![42, 3, 4, 24, -14], ![-74, -6, -7, -40, 24], ![78, 6, 7, 42, -25], ![-75, -4, -7, -41, 24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![-30, -18, 4, 9, 0]] ![![59, 2, 3, 14, -8]]
  ![![0, 0, -1, -1, 0]] where
 M := ![![![0, 0, -1, -1, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![0, 0, -1, -1, 0]] ![![59, 2, 3, 14, -8]]
  ![![-8, -11, -9, -7, -6]] where
 M := ![![![-8, -11, -9, -7, -6]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![-8, -11, -9, -7, -6]] ![![-27, -1, -1, -7, 4]]
  ![![449, 11, 20, 104, -63]] where
 M := ![![![449, 11, 20, 104, -63]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![449, 11, 20, 104, -63]] ![![-27, -1, -1, -7, 4]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![14144, 340, 624, 3272, -1990]]]
 hmul := by decide  
 g := ![![![![7072, 170, 312, 1636, -995]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-211, -108, -92, -98, -38]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![-211, -108, -92, -98, -38]] 
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 0, 0, 3, 0], ![1, 0, 0, 1, 1]] where
  M :=![![![-211, -108, -92, -98, -38], ![-1096, -559, -476, -508, -196], ![-2828, -1446, -1231, -1312, -508], ![-1612, -822, -700, -747, -288], ![-5220, -2668, -2272, -2422, -937]]]
  hmulB := by decide  
  f := ![![![-49, 0, -4, -6, 6]], ![![29, 1, 0, 2, -2]], ![![-63, 6, -3, -10, 6]], ![![132, -14, 12, 23, -16]], ![![-11, -10, 0, 5, 1]]]
  g := ![![![9, -108, -92, -20, -38], ![45, -559, -476, -104, -196], ![119, -1446, -1231, -268, -508], ![66, -822, -700, -153, -288], ![219, -2668, -2272, -495, -937]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P0 : CertificateIrreducibleZModOfList' 3 2 2 1 [2, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 2], [0, 1]]
 g := ![![[2, 1]], ![[1, 2]]]
 h' := ![![[2, 2], [0, 1]], ![[0, 1], [2, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [1, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 2
  hpos := by decide
  P := [2, 1, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![17681, 9556, 9684, 10912, 4963]
  a := ![-9, -7, -7, -10, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2174, 9556, 9684, 1983, 4963]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 9 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![87, 72, 6, -32, -12]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![87, 72, 6, -32, -12]] 
 ![![3, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![87, 72, 6, -32, -12], ![-276, -59, 132, 52, -64], ![-636, -466, 9, 216, 52], ![348, 128, -118, -81, 48], ![944, 566, -126, -284, -1]]]
  hmulB := by decide  
  f := ![![![589, 20, 26, 144, -84]], ![![-262, -3, -8, -60, 40]], ![![1323, 46, 63, 320, -184]], ![![-1156, -28, -46, -273, 168]], ![![1534, 58, 78, 372, -209]]]
  g := ![![![-13, 72, 6, -32, -12], ![-54, -59, 132, 52, -64], ![61, -466, 9, 216, 52], ![38, 128, -118, -81, 48], ![-20, 566, -126, -284, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![-211, -108, -92, -98, -38]] ![![-211, -108, -92, -98, -38]]
  ![![779401, 398132, 339008, 361488, 139752]] where
 M := ![![![779401, 398132, 339008, 361488, 139752]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![779401, 398132, 339008, 361488, 139752]] ![![87, 72, 6, -32, -12]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![38079, 19452, 16566, 17664, 6828]]]
 hmul := by decide  
 g := ![![![![12693, 6484, 5522, 5888, 2276]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N0, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 5, 4, 4, 2]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![7, 5, 4, 4, 2]] 
 ![![5, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![7, 5, 4, 4, 2], ![56, 25, 22, 24, 8], ![118, 65, 55, 58, 24], ![82, 37, 32, 35, 12], ![230, 121, 102, 108, 43]]]
  hmulB := by decide  
  f := ![![![-45, -3, -2, -8, 6]], ![![19, 0, 0, 4, -2]], ![![-56, 1, -3, -14, 8]], ![![24, -1, 2, 7, -4]], ![![-73, -6, -2, -12, 9]]]
  g := ![![![-4, 5, 4, 4, 2], ![-17, 25, 22, 24, 8], ![-49, 65, 55, 58, 24], ![-25, 37, 32, 35, 12], ![-88, 121, 102, 108, 43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![7, 5, 4, 4, 2]] ![![7, 5, 4, 4, 2]]
  ![![1589, 810, 690, 736, 284]] where
 M := ![![![1589, 810, 690, 736, 284]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![1589, 810, 690, 736, 284]] ![![7, 5, 4, 4, 2]]
  ![![263575, 134641, 114646, 122248, 47262]] where
 M := ![![![263575, 134641, 114646, 122248, 47262]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![263575, 134641, 114646, 122248, 47262]] ![![7, 5, 4, 4, 2]]
  ![![43807745, 22377768, 19054592, 20318128, 7855024]] where
 M := ![![![43807745, 22377768, 19054592, 20318128, 7855024]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![43807745, 22377768, 19054592, 20318128, 7855024]] ![![7, 5, 4, 4, 2]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![7280993095, 3719260045, 3166936980, 3376940820, 1305531410]]]
 hmul := by decide  
 g := ![![![![1456198619, 743852009, 633387396, 675388164, 261106282]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5041, -108, 298, 782, -584]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![5041, -108, 298, 782, -584]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![2, 1, 1, 3, 1]] where
  M :=![![![5041, -108, 298, 782, -584], ![-13420, 269, -788, -2112, 1564], ![17980, -334, 1045, 2876, -2112], ![-18010, 326, -1046, -2893, 2118], ![13070, -206, 746, 2154, -1557]]]
  hmulB := by decide  
  f := ![![![27, 36, 14, -14, -12]], ![![-260, -109, 76, 64, -28]], ![![-260, -262, -61, 108, 64]], ![![270, 138, -58, -75, 14]], ![![122, 71, -19, -37, 1]]]
  g := ![![![887, 68, 126, 362, -584], ![-2364, -185, -336, -972, 1564], ![3172, 254, 451, 1316, -2112], ![-3178, -256, -452, -1321, 2118], ![2312, 193, 329, 975, -1557]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 4 2 2 [3, 5, 1, 1, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 6, 0, 6], [0, 0, 3, 2], [1, 0, 4, 6], [0, 1]]
 g := ![![[3, 0, 6, 1], []], ![[0, 0, 3, 5, 2, 6], [2, 4, 1, 4, 1, 6]], ![[2, 6, 4, 4, 1, 2], [1, 3, 4, 4, 0, 1]], ![[3, 6, 0, 5, 6, 6], [6, 2, 0, 3, 6, 6]]]
 h' := ![![[5, 6, 0, 6], [0, 0, 0, 1], [0, 1]], ![[0, 0, 3, 2], [0, 1, 4, 6], [5, 6, 0, 6]], ![[1, 0, 4, 6], [4, 0, 0, 6], [0, 0, 3, 2]], ![[0, 1], [4, 6, 3, 1], [1, 0, 4, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [5, 6, 2], []]
 b := ![[], [], [1, 2, 1, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 4
  hpos := by decide
  P := [3, 5, 1, 1, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![16149232062151, 8268976634306, 7057820410854, 7515303412556, 2905826464488]
  a := ![-53, -53, -57, -58, -104]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1476797019025, 766164309974, 593141992338, -171739425844, 2905826464488]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 2401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![27, 36, 14, -14, -12]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![27, 36, 14, -14, -12]] 
 ![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![27, 36, 14, -14, -12], ![-260, -109, 76, 64, -28], ![-260, -262, -61, 108, 64], ![270, 138, -58, -75, 14], ![510, 382, -2, -178, -47]]]
  hmulB := by decide  
  f := ![![![5041, -108, 298, 782, -584]], ![![-1197, 23, -70, -190, 140]], ![![4729, -94, 277, 746, -552]], ![![1748, -46, 106, 257, -198]], ![![6188, -122, 362, 978, -723]]]
  g := ![![![15, 36, 14, -14, -12], ![-85, -109, 76, 64, -28], ![-121, -262, -61, 108, 64], ![96, 138, -58, -75, 14], ![212, 382, -2, -178, -47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![5041, -108, 298, 782, -584]] ![![27, 36, 14, -14, -12]]
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


def P11P0 : CertificateIrreducibleZModOfList' 11 5 2 3 [5, 6, 7, 5, 1, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 7, 3, 1, 10], [3, 8, 2, 2, 1], [6, 1, 8, 4, 2], [8, 5, 9, 4, 9], [0, 1]]
 g := ![![[8, 5, 3, 9, 1], [1], []], ![[0, 4, 8, 0, 10, 6], [0, 6, 9, 3, 0, 8, 7, 2], [7, 4, 8, 1]], ![[6, 10, 6, 8, 5, 4, 9, 9], [7, 2, 3, 9, 2, 7, 4, 4], [2, 0, 3, 1]], ![[5, 4, 3, 6, 7, 9, 5, 7], [6, 1, 10, 7, 6, 9, 7, 2], [8, 5, 1, 4]], ![[6, 2, 0, 9, 8, 8, 6, 9], [10, 4, 3, 2, 6, 2, 6, 1], [1, 2, 2, 4]]]
 h' := ![![[4, 7, 3, 1, 10], [6, 5, 4, 6, 10], [0, 0, 1], [0, 1]], ![[3, 8, 2, 2, 1], [3, 10, 0, 7], [3, 5, 4, 0, 3], [4, 7, 3, 1, 10]], ![[6, 1, 8, 4, 2], [1, 4, 8, 0, 8], [10, 3, 3, 0, 2], [3, 8, 2, 2, 1]], ![[8, 5, 9, 4, 9], [0, 10, 6, 9, 3], [7, 5, 6, 7, 10], [6, 1, 8, 4, 2]], ![[0, 1], [1, 4, 4, 0, 1], [4, 9, 8, 4, 7], [8, 5, 9, 4, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 9, 3, 4], [], [], []]
 b := ![[], [5, 4, 0, 0, 4], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 5
  hpos := by decide
  P := [5, 6, 7, 5, 1, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-120527841709, -61584649522, -52420518040, -55875233480, -21599086234]
  a := ![-4, -3, -4, -6, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-10957076519, -5598604502, -4765501640, -5079566680, -1963553294]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1752, -46, 106, 254, -197]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![1752, -46, 106, 254, -197]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![8, 10, 12, 3, 1]] where
  M :=![![![1752, -46, 106, 254, -197], ![-4516, 127, -274, -660, 508], ![5822, -165, 361, 854, -660], ![-5797, 154, -356, -843, 655], ![3965, -104, 234, 572, -442]]]
  hmulB := by decide  
  f := ![![![-14, -2, -2, -4, 1]], ![![20, -7, -6, 0, -8]], ![![-102, -23, -21, -34, 0]], ![![35, -12, -8, 3, -13]], ![![-90, -34, -30, -37, -9]]]
  g := ![![![256, 148, 190, 65, -197], ![-660, -381, -490, -168, 508], ![854, 495, 637, 218, -660], ![-849, -492, -632, -216, 655], ![577, 332, 426, 146, -442]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 4 2 3 [7, 1, 6, 3, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 0, 0, 5], [6, 8, 4, 2], [12, 4, 9, 6], [0, 1]]
 g := ![![[3, 5, 2, 12], [3, 10, 1], []], ![[4, 10, 5, 11, 1, 2], [1, 9, 9], [0, 2, 10, 11, 2, 8]], ![[3, 9, 10, 11, 8, 6], [9, 0, 3], [8, 10, 9, 7, 11, 8]], ![[11, 9, 1, 6], [], [0, 8, 7, 12, 12, 8]]]
 h' := ![![[5, 0, 0, 5], [5, 5, 4, 8], [0, 0, 0, 1], [0, 1]], ![[6, 8, 4, 2], [5, 11, 6, 9], [8, 12, 6, 3], [5, 0, 0, 5]], ![[12, 4, 9, 6], [5, 0, 4, 9], [4, 6, 7, 9], [6, 8, 4, 2]], ![[0, 1], [1, 10, 12], [12, 8], [12, 4, 9, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [7, 5, 10], []]
 b := ![[], [], [5, 11, 12, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 4
  hpos := by decide
  P := [7, 1, 6, 3, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1433311334328, 735352463515, 629819536110, 670831635779, 260161323983]
  a := ![28, 32, 24, 19, 64]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-49844558272, -143558521255, -191701257822, -8434795090, 260161323983]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 28561 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14, 2, 2, 4, -1]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![14, 2, 2, 4, -1]] 
 ![![13, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![14, 2, 2, 4, -1], ![-20, 7, 6, 0, 8], ![102, 23, 21, 34, 0], ![-35, 12, 8, -3, 13], ![139, 44, 38, 50, 6]]]
  hmulB := by decide  
  f := ![![![-1752, 46, -106, -254, 197]], ![![-596, 15, -36, -86, 67]], ![![-1526, 41, -93, -222, 172]], ![![-767, 20, -46, -111, 86]], ![![-305, 8, -18, -44, 34]]]
  g := ![![![-4, 2, 2, 4, -1], ![-9, 7, 6, 0, 8], ![-41, 23, 21, 34, 0], ![-12, 12, 8, -3, 13], ![-71, 44, 38, 50, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![1752, -46, 106, 254, -197]] ![![14, 2, 2, 4, -1]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19, 1, 0, -2, 2]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![-19, 1, 0, -2, 2]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![14, 2, 5, 1, 0], ![13, 11, 5, 0, 1]] where
  M :=![![![-19, 1, 0, -2, 2], ![48, -3, 6, 12, -4], ![-42, 9, -1, -2, 12], ![76, 7, 8, 11, -6], ![-12, 21, 14, 6, 7]]]
  hmulB := by decide  
  f := ![![![41, 1, 2, 10, -6]], ![![-140, -5, -6, -32, 20]], ![![234, 7, 9, 54, -32]], ![![72, 2, 3, 17, -10]], ![![23, 0, 1, 6, -3]]]
  g := ![![![-1, -1, 0, -2, 2], ![-4, 1, -2, 12, -4], ![-10, -7, -3, -2, 12], ![0, 3, -1, 11, -6], ![-11, -4, -3, 6, 7]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [3, 4, 11, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 7, 3], [12, 9, 14], [0, 1]]
 g := ![![[2, 6, 16], [13, 4], [6, 1], []], ![[0, 13, 2, 12], [15, 9], [8, 13], [11, 9]], ![[2, 13, 1, 5], [7, 1], [16, 15], [0, 9]]]
 h' := ![![[11, 7, 3], [13, 7, 13], [16, 7, 15], [0, 0, 1], [0, 1]], ![[12, 9, 14], [10, 6, 2], [2, 2, 3], [3, 15, 9], [11, 7, 3]], ![[0, 1], [14, 4, 2], [16, 8, 16], [8, 2, 7], [12, 9, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 15], []]
 b := ![[], [6, 0, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [3, 4, 11, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-24225121, -14875028, -12255590, -12583974, -6806386]
  a := ![-7, -18, -1, 12, -32]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![14143149, 5009598, 4982130, -12583974, -6806386]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 4913 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-122, -61, -52, -56, -21]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![-122, -61, -52, -56, -21]] 
 ![![17, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![-122, -61, -52, -56, -21], ![-608, -315, -268, -284, -112], ![-1612, -816, -695, -744, -284], ![-891, -463, -394, -417, -165], ![-2961, -1505, -1282, -1370, -526]]]
  hmulB := by decide  
  f := ![![![128, -29, 10, 34, -15]], ![![-20, 1, -4, -4, 4]], ![![44, 8, 1, 0, -4]], ![![9, -11, 4, 9, -3]], ![![47, -21, 8, 20, -8]]]
  g := ![![![20, -61, -52, -56, -21], ![104, -315, -268, -284, -112], ![268, -816, -695, -744, -284], ![153, -463, -394, -417, -165], ![495, -1505, -1282, -1370, -526]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1

def I17N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4, 4, 0, 0, -1]] i)))

def SI17N2: IdealEqSpanCertificate' Table ![![4, 4, 0, 0, -1]] 
 ![![17, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![16, 0, 1, 0, 0], ![14, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![4, 4, 0, 0, -1], ![-24, -5, 6, -4, 0], ![6, -17, 1, 22, -4], ![-23, 2, -6, -17, 9], ![91, 28, -4, 2, -8]]]
  hmulB := by decide  
  f := ![![![-2430, -1240, -1056, -1126, -435]], ![![-1596, -815, -694, -740, -286]], ![![-4198, -2143, -1825, -1946, -752]], ![![-3087, -1576, -1342, -1431, -553]], ![![-3955, -2020, -1720, -1834, -709]]]
  g := ![![![-1, 4, 0, 0, -1], ![-2, -5, 6, -4, 0], ![-12, -17, 1, 22, -4], ![16, 2, -6, -17, 9], ![-1, 28, -4, 2, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N2 : Nat.card (O ⧸ I17N2) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N2)

lemma isPrimeI17N2 : Ideal.IsPrime I17N2 := prime_ideal_of_norm_prime hp17.out _ NI17N2
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![-19, 1, 0, -2, 2]] ![![-122, -61, -52, -56, -21]]
  ![![-2430, -1240, -1056, -1126, -435]] where
 M := ![![![-2430, -1240, -1056, -1126, -435]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI17N1 : IdealMulLeCertificate' Table 
  ![![-2430, -1240, -1056, -1126, -435]] ![![4, 4, 0, 0, -1]]
  ![![17, 0, 0, 0, 0]] where
 M := ![![![17, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0, 0, 0]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0, 0, 0]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]] where
  M :=![![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 5 2 4 [18, 10, 13, 7, 17, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 10, 11, 12, 15], [17, 18, 18, 0, 8], [12, 6, 4, 16, 15], [7, 3, 5, 10], [0, 1]]
 g := ![![[4, 6, 8, 10, 17], [14, 5, 16, 2, 1], [], []], ![[13, 5, 12, 13, 9, 8, 3, 12], [1, 9, 10, 3, 1, 6, 1, 13], [0, 3, 1, 11], [18, 6, 12, 16]], ![[14, 7, 2, 11, 10, 3, 17, 2], [11, 8, 15, 15, 10, 3, 9, 2], [9, 3, 2, 11], [6, 1, 14, 7]], ![[5, 10, 0, 0, 10, 15, 13, 10], [1, 11, 17, 18, 13, 18, 5, 3], [9, 8, 16, 1], [4, 15, 18, 16]], ![[10, 18, 7, 18, 15, 5, 12], [16, 12, 18, 14, 2], [1, 11, 13, 16], [15, 5]]]
 h' := ![![[4, 10, 11, 12, 15], [14, 17, 12, 2, 13], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[17, 18, 18, 0, 8], [18, 0, 16, 7, 15], [16, 14, 2, 14, 7], [15, 1, 1, 8, 7], [4, 10, 11, 12, 15]], ![[12, 6, 4, 16, 15], [18, 16, 8, 15, 9], [14, 10, 18, 16, 9], [10, 2, 7, 4, 7], [17, 18, 18, 0, 8]], ![[7, 3, 5, 10], [15, 15, 12, 2, 11], [6, 11, 13, 10, 2], [15, 5, 5, 7, 1], [12, 6, 4, 16, 15]], ![[0, 1], [17, 9, 9, 12, 9], [12, 3, 5, 17], [7, 11, 5, 0, 4], [7, 3, 5, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 15, 16, 10], [], [], []]
 b := ![[], [6, 4, 4, 16, 12], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 5
  hpos := by decide
  P := [18, 10, 13, 7, 17, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1335073325470, -90668378556, -18178463104, -248417612496, 159366649752]
  a := ![-12, 18, -14, -54, 18]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-70267017130, -4772019924, -956761216, -13074611184, 8387718408]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 2476099 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def PBC19 : ContainsPrimesAboveP 19 ![I19N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![19, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 19 (by decide) 𝕀

instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-193, 1, -10, -36, 24]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![-193, 1, -10, -36, 24]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![14, 1, 13, 10, 1]] where
  M :=![![![-193, 1, -10, -36, 24], ![556, -3, 30, 108, -72], ![-834, -7, -45, -162, 108], ![852, 5, 42, 165, -110], ![-704, -1, -36, -148, 91]]]
  hmulB := by decide  
  f := ![![![-3, -1, 0, 0, 0]], ![![0, -3, -2, 0, 0]], ![![-2, 1, -5, -6, 0]], ![![0, -1, 0, -1, -2]], ![![-4, -1, -3, -4, -1]]]
  g := ![![![-23, -1, -14, -12, 24], ![68, 3, 42, 36, -72], ![-102, -5, -63, -54, 108], ![104, 5, 64, 55, -110], ![-86, -4, -53, -46, 91]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 4 2 4 [8, 16, 12, 3, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 15, 15, 14], [20, 15, 21, 7], [20, 15, 10, 2], [0, 1]]
 g := ![![[14, 14, 17, 4], [10, 10, 14, 9], [20, 1], []], ![[13, 9, 5, 11, 4, 22], [11, 6, 22, 2, 5, 21], [12, 16, 4, 22, 18, 20], [16, 16, 12]], ![[20, 2, 1, 13, 13, 7], [6, 12, 20, 3, 2, 11], [4, 8, 6, 4, 2, 5], [13, 9, 3]], ![[5, 1, 22, 19, 4, 4], [20, 15, 12, 4, 9, 4], [7, 4, 18, 6, 15, 12], [5, 5, 4]]]
 h' := ![![[3, 15, 15, 14], [12, 14, 10, 21], [1, 17, 20, 20], [0, 0, 1], [0, 1]], ![[20, 15, 21, 7], [16, 5, 18, 8], [21, 7, 18, 6], [19, 5, 1, 10], [3, 15, 15, 14]], ![[20, 15, 10, 2], [20, 12, 4, 22], [10, 17, 16, 15], [20, 21, 5, 2], [20, 15, 21, 7]], ![[0, 1], [18, 15, 14, 18], [5, 5, 15, 5], [15, 20, 16, 11], [20, 15, 10, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [18, 20, 16], []]
 b := ![[], [], [17, 14, 7, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 4
  hpos := by decide
  P := [8, 16, 12, 3, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![645238116511, 330518508419, 281597681198, 299160064742, 115199775729]
  a := ![34, 13, 25, 47, 42]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-42067771465, 9361684030, -52869539273, -37079899676, 115199775729]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 279841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 1, 0, 0, 0]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![3, 1, 0, 0, 0]] 
 ![![23, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![18, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![3, 1, 0, 0, 0], ![0, 3, 2, 0, 0], ![2, -1, 5, 6, 0], ![0, 1, 0, 1, 2], ![24, 9, 2, 4, 3]]]
  hmulB := by decide  
  f := ![![![193, -1, 10, 36, -24]], ![![1, 0, 0, 0, 0]], ![![95, 0, 5, 18, -12]], ![![114, -1, 6, 21, -14]], ![![39, 0, 2, 8, -5]]]
  g := ![![![0, 1, 0, 0, 0], ![-1, 3, 2, 0, 0], ![-6, -1, 5, 6, 0], ![-1, 1, 0, 1, 2], ![-4, 9, 2, 4, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![-193, 1, -10, -36, 24]] ![![3, 1, 0, 0, 0]]
  ![![23, 0, 0, 0, 0]] where
 M := ![![![-23, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC23 : ContainsPrimesAboveP 23 ![I23N0, I23N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 23 (by decide) (𝕀 ⊙ MulI23N0)


lemma PB519I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB519I0 : PrimesBelowBoundCertificateInterval O 1 23 519 where
  m := 9
  g := ![5, 3, 5, 2, 1, 2, 3, 1, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB519I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N0, I3N1]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1]
    · exact ![I11N0]
    · exact ![I13N0, I13N1]
    · exact ![I17N0, I17N1, I17N2]
    · exact ![I19N0]
    · exact ![I23N0, I23N1]
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
    · exact ![9, 9, 3]
    · exact ![5, 5, 5, 5, 5]
    · exact ![2401, 7]
    · exact ![161051]
    · exact ![28561, 13]
    · exact ![4913, 17, 17]
    · exact ![2476099]
    · exact ![279841, 23]
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
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I5N0, I7N1, I13N1, I17N1, I17N2, I23N1]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N0, I3N1], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N1], [], [I13N1], [I17N1, I17N2], [], [I23N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
