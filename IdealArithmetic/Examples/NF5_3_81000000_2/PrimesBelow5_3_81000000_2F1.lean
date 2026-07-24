
import IdealArithmetic.Examples.NF5_3_81000000_2.RI5_3_81000000_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1105, 1351, 965, 56, -144]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![1105, 1351, 965, 56, -144]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![15, 4, 13, 1, 0], ![4, 25, 5, 0, 1]] where
  M :=![![![1105, 1351, 965, 56, -144], ![-864, -1055, -753, -43, 112], ![672, 816, 582, 31, -86], ![-516, -618, -443, -20, 62], ![-150, -201, -145, -20, 23]]]
  hmulB := by decide  
  f := ![![![17, 55, 43, 2, -6]], ![![-36, -73, -33, 1, 4]], ![![24, 24, -12, -5, 2]], ![![15, 31, 14, -1, -2]], ![![-26, -54, -26, 0, 3]]]
  g := ![![![29, 163, 33, 56, -144], ![-23, -127, -26, -43, 112], ![19, 98, 21, 31, -86], ![-16, -72, -17, -20, 62], ![2, -24, 0, -20, 23]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [25, 3, 13, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 15, 7], [7, 13, 22], [0, 1]]
 g := ![![[24], [23, 9], [4, 27, 24], [1]], ![[14, 17, 18, 25], [28, 23], [23, 13, 17, 23], [3, 14, 8, 24]], ![[1, 19, 21, 4], [23, 28], [3, 9], [23, 2, 19, 5]]]
 h' := ![![[9, 15, 7], [0, 13], [16, 25, 26], [4, 26, 16], [0, 1]], ![[7, 13, 22], [1, 21, 4], [18, 6, 20], [16, 9, 13], [9, 15, 7]], ![[0, 1], [4, 24, 25], [12, 27, 12], [0, 23], [7, 13, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25, 1], []]
 b := ![[], [8, 28, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 3
  hpos := by decide
  P := [25, 3, 13, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5601089, -15228012, -19584269, -10718064, -4559451]
  a := ![0, -1, -3, -1, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![5979575, 4883811, 4915442, -10718064, -4559451]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 24389 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -3, -1, 0, 0]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![-1, -3, -1, 0, 0]] 
 ![![29, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![24, 0, 0, 1, 0], ![13, 0, 0, 0, 1]] where
  M :=![![![-1, -3, -1, 0, 0], ![0, -1, -3, -1, 0], ![0, 0, -2, -3, -2], ![-12, -30, -33, -16, -6], ![-18, -51, -67, -36, -15]]]
  hmulB := by decide  
  f := ![![![79, 93, 57, 6, -10]], ![![17, 20, 12, 1, -2]], ![![27, 33, 21, 3, -4]], ![![60, 66, 39, 2, -6]], ![![41, 54, 34, 6, -7]]]
  g := ![![![1, -3, -1, 0, 0], ![2, -1, -3, -1, 0], ![4, 0, -2, -3, -2], ![33, -30, -33, -16, -6], ![69, -51, -67, -36, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1

def I29N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, 2, 12, 2, -2]] i)))

def SI29N2: IdealEqSpanCertificate' Table ![![-5, 2, 12, 2, -2]] 
 ![![29, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![8, 0, 0, 0, 1]] where
  M :=![![![-5, 2, 12, 2, -2], ![-12, -35, -26, -2, 4], ![24, 48, 23, 2, -4], ![-24, -36, -10, -5, 4], ![0, -6, -2, 8, -3]]]
  hmulB := by decide  
  f := ![![![815, 998, 712, 42, -106]], ![![231, 283, 202, 12, -30]], ![![186, 228, 163, 10, -24]], ![![100, 124, 90, 7, -12]], ![![224, 278, 202, 16, -27]]]
  g := ![![![-3, 2, 12, 2, -2], ![15, -35, -26, -2, 4], ![-18, 48, 23, 2, -4], ![12, -36, -10, -5, 4], ![2, -6, -2, 8, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N2 : Nat.card (O ⧸ I29N2) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N2)

lemma isPrimeI29N2 : Ideal.IsPrime I29N2 := prime_ideal_of_norm_prime hp29.out _ NI29N2
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![1105, 1351, 965, 56, -144]] ![![-1, -3, -1, 0, 0]]
  ![![815, 998, 712, 42, -106]] where
 M := ![![![815, 998, 712, 42, -106]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI29N1 : IdealMulLeCertificate' Table 
  ![![815, 998, 712, 42, -106]] ![![-5, 2, 12, 2, -2]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4039, -4938, -3527, -207, 528]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![-4039, -4938, -3527, -207, 528]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![22, 22, 7, 10, 1]] where
  M :=![![![-4039, -4938, -3527, -207, 528], ![3168, 3881, 2775, 169, -414], ![-2484, -3042, -2160, -123, 338], ![2028, 2586, 1905, 206, -246], ![504, 690, 631, 153, 37]]]
  hmulB := by decide  
  f := ![![![-25, 66, 133, 15, -20]], ![![-120, -325, -219, -7, 30]], ![![180, 330, 118, -9, -14]], ![![-84, -30, 111, 20, -18]], ![![-94, -130, -5, 10, -1]]]
  g := ![![![-505, -534, -233, -177, 528], ![396, 419, 183, 139, -414], ![-320, -338, -146, -113, 338], ![240, 258, 117, 86, -246], ![-10, -4, 12, -7, 37]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 4 2 4 [14, 0, 30, 15, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 11, 16, 21], [20, 21, 11, 20], [8, 29, 4, 21], [0, 1]]
 g := ![![[23, 22, 26, 8], [29, 21, 17, 14], [5, 9, 16, 1], []], ![[8, 24, 15, 9, 14, 27], [2, 17, 14, 1, 13, 6], [2, 23, 24, 0, 5, 6], [17, 29, 30, 25, 22, 23]], ![[5, 29, 14, 17, 12, 16], [16, 23, 13, 8, 18, 14], [5, 26, 21, 12, 23, 8], [20, 30, 14, 18, 26, 2]], ![[0, 11, 10, 17, 14, 26], [2, 13, 23, 0, 13, 11], [26, 16, 25, 30, 25, 24], [1, 7, 20, 6, 18, 23]]]
 h' := ![![[19, 11, 16, 21], [28, 18, 9, 15], [23, 29, 29, 13], [0, 0, 0, 1], [0, 1]], ![[20, 21, 11, 20], [12, 2, 17, 22], [21, 30, 2, 24], [18, 6, 14, 7], [19, 11, 16, 21]], ![[8, 29, 4, 21], [21, 3, 17, 21], [12, 4, 3, 17], [1, 11, 21, 9], [20, 21, 11, 20]], ![[0, 1], [0, 8, 19, 4], [9, 30, 28, 8], [2, 14, 27, 14], [8, 29, 4, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [5, 23, 18], []]
 b := ![[], [], [26, 23, 17, 27], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 4
  hpos := by decide
  P := [14, 0, 30, 15, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-313343884, -658672104, -403202924, -168816210, 209006978]
  a := ![3, -64, 2, -1, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-158435400, -169575020, -60201670, -72867290, 209006978]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 923521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25, -66, -133, -15, 20]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![25, -66, -133, -15, 20]] 
 ![![31, 0, 0, 0, 0], ![11, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![29, 0, 0, 1, 0], ![25, 0, 0, 0, 1]] where
  M :=![![![25, -66, -133, -15, 20], ![120, 325, 219, 7, -30], ![-180, -330, -118, 9, 14], ![84, 30, -111, -20, 18], ![144, 342, 199, 3, -27]]]
  hmulB := by decide  
  f := ![![![4039, 4938, 3527, 207, -528]], ![![1331, 1627, 1162, 68, -174]], ![![471, 576, 411, 24, -62]], ![![3713, 4536, 3238, 187, -486]], ![![3241, 3960, 2824, 162, -427]]]
  g := ![![![35, -66, -133, -15, 20], ![-115, 325, 219, 7, -30], ![103, -330, -118, 9, 14], ![7, 30, -111, -20, 18], ![-117, 342, 199, 3, -27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![-4039, -4938, -3527, -207, 528]] ![![25, -66, -133, -15, 20]]
  ![![31, 0, 0, 0, 0]] where
 M := ![![![-31, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-163, -187, -133, -8, 20]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![-163, -187, -133, -8, 20]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![32, 16, 10, 1, 0], ![25, 10, 14, 0, 1]] where
  M :=![![![-163, -187, -133, -8, 20], ![120, 137, 105, 7, -16], ![-96, -120, -96, -7, 14], ![84, 114, 83, 2, -14], ![6, -3, 1, -4, -5]]]
  hmulB := by decide  
  f := ![![![5, 13, 9, 2, -2]], ![![-12, -25, -15, -5, 4]], ![![24, 48, 30, 13, -10]], ![![4, 10, 7, 2, -2]], ![![11, 24, 16, 6, -5]]]
  g := ![![![-11, -7, -9, -8, 20], ![8, 5, 7, 7, -16], ![-6, -4, -6, -7, 14], ![10, 6, 7, 2, -14], ![7, 3, 3, -4, -5]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [4, 35, 7, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 34, 22], [21, 2, 15], [0, 1]]
 g := ![![[7, 16, 36], [21, 4], [17, 11, 11], [30, 1], []], ![[3, 10, 8, 17], [29, 16], [7, 19, 32, 14], [1, 4], [32, 3]], ![[26, 12, 8, 29], [12, 4], [11, 3, 5, 29], [36, 9], [2, 3]]]
 h' := ![![[9, 34, 22], [26, 27, 31], [6, 34, 35], [28, 19, 14], [0, 0, 1], [0, 1]], ![[21, 2, 15], [33, 5, 27], [36, 13, 4], [22, 26, 2], [27, 35, 2], [9, 34, 22]], ![[0, 1], [30, 5, 16], [2, 27, 35], [14, 29, 21], [26, 2, 34], [21, 2, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28, 15], []]
 b := ![[], [0, 16, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [4, 35, 7, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-519109, -1407402, -1800889, -984370, -413654]
  a := ![1, -3, -1, -1, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1116813, 499434, 373891, -984370, -413654]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 50653 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 31, 22, 3, -4]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![23, 31, 22, 3, -4]] 
 ![![37, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![26, 0, 0, 1, 0], ![27, 0, 0, 0, 1]] where
  M :=![![![23, 31, 22, 3, -4], ![-24, -37, -26, -6, 6], ![36, 66, 47, 16, -12], ![-72, -144, -98, -37, 32], ![78, 171, 126, 55, -31]]]
  hmulB := by decide  
  f := ![![![-457, -793, -234, 29, 26]], ![![-144, -259, -86, 8, 10]], ![![-40, -58, -5, 4, 0]], ![![-338, -590, -178, 21, 20]], ![![-333, -588, -184, 20, 21]]]
  g := ![![![-11, 31, 22, 3, -4], ![14, -37, -26, -6, 6], ![-28, 66, 47, 16, -12], ![58, -144, -98, -37, 32], ![-83, 171, 126, 55, -31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 72, 19, -3, -2]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![43, 72, 19, -3, -2]] 
 ![![37, 0, 0, 0, 0], ![15, 1, 0, 0, 0], ![34, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![34, 0, 0, 0, 1]] where
  M :=![![![43, 72, 19, -3, -2], ![-12, 13, 39, 5, -6], ![-36, -102, -72, -3, 10], ![60, 114, 45, -2, -6], ![0, 36, 47, 3, -7]]]
  hmulB := by decide  
  f := ![![![-1913, -2340, -1671, -99, 250]], ![![-735, -899, -642, -38, 96]], ![![-1790, -2190, -1564, -93, 234]], ![![-388, -474, -339, -20, 50]], ![![-1754, -2148, -1535, -93, 229]]]
  g := ![![![-43, 72, 19, -3, -2], ![-37, 13, 39, 5, -6], ![98, -102, -72, -3, 10], ![-80, 114, 45, -2, -6], ![-52, 36, 47, 3, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![-163, -187, -133, -8, 20]] ![![23, 31, 22, 3, -4]]
  ![![-1913, -2340, -1671, -99, 250]] where
 M := ![![![-1913, -2340, -1671, -99, 250]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![-1913, -2340, -1671, -99, 250]] ![![43, 72, 19, -3, -2]]
  ![![37, 0, 0, 0, 0]] where
 M := ![![![37, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0, 0, 0]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![0, 0, 0, 0, 41]] where
  M :=![![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![0, 0, 0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 5 2 5 [34, 13, 32, 29, 2, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 18, 25, 2, 37], [4, 13, 9, 16, 36], [38, 26, 2, 37, 28], [0, 24, 5, 27, 22], [0, 1]]
 g := ![![[23, 38, 34, 29, 16], [3, 27, 16, 32], [39, 22, 26, 4], [1], []], ![[15, 12, 10, 9, 16, 13, 20, 4], [39, 4, 1, 32], [28, 19, 8, 31], [39, 5, 18, 2, 7, 0, 25, 18], [37, 10, 34, 16]], ![[23, 23, 34, 15, 2, 4, 28, 33], [29, 12, 20, 4], [17, 16, 21, 16], [31, 6, 35, 3, 4, 37, 8, 39], [27, 25, 36, 25]], ![[40, 37, 7, 14, 19, 26, 31, 6], [0, 28, 33, 16], [11, 15, 18, 20], [11, 10, 40, 25, 21, 7, 11, 7], [30, 0, 12, 5]], ![[0, 4, 14, 15, 33, 16, 38, 13], [12, 30, 38, 8], [38, 22, 30, 39], [16, 4, 6, 38, 11, 29, 4, 38], [34, 3, 15, 33]]]
 h' := ![![[38, 18, 25, 2, 37], [16, 10, 12, 18, 37], [35, 39, 9, 3, 27], [7, 28, 9, 12, 39], [0, 0, 1], [0, 1]], ![[4, 13, 9, 16, 36], [26, 32, 37, 38, 32], [9, 17, 10, 5, 27], [10, 37, 11, 29, 21], [22, 14, 0, 26, 4], [38, 18, 25, 2, 37]], ![[38, 26, 2, 37, 28], [0, 28, 34, 29, 10], [17, 1, 1, 34, 39], [12, 8, 26, 19, 37], [0, 10, 1, 3, 5], [4, 13, 9, 16, 36]], ![[0, 24, 5, 27, 22], [5, 19, 32, 11, 38], [28, 21, 39, 38, 37], [22, 6, 32, 32, 15], [14, 28, 34, 39, 21], [38, 26, 2, 37, 28]], ![[0, 1], [39, 34, 8, 27, 6], [18, 4, 23, 2, 34], [30, 3, 4, 31, 11], [33, 30, 5, 14, 11], [0, 24, 5, 27, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36, 32, 13, 10], [], [], []]
 b := ![[], [25, 18, 10, 30, 23], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 5
  hpos := by decide
  P := [34, 13, 32, 29, 2, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![38502543840699, 104337689410089, 133453237132594, 72921494568947, 30599812939811]
  a := ![1, 19, 4, -1, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![939086435139, 2544821692929, 3254957003234, 1778573038267, 746336900971]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 115856201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def PBC41 : ContainsPrimesAboveP 41 ![I41N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![41, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 41 (by decide) 𝕀

instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 44, 13, -1, -2]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![31, 44, 13, -1, -2]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![6, 21, 15, 22, 1]] where
  M :=![![![31, 44, 13, -1, -2], ![-12, 1, 13, -1, -2], ![-12, -42, -30, -1, -2], ![-12, -42, -73, -44, -2], ![0, 0, -43, -43, -43]]]
  hmulB := by decide  
  f := ![![![13, 16, 13, 1, -2]], ![![-12, -17, -13, -1, 2]], ![![12, 18, 12, 1, -2]], ![![-12, -18, -11, -2, 2]], ![![-6, -9, -6, -1, 1]]]
  g := ![![![1, 2, 1, 1, -2], ![0, 1, 1, 1, -2], ![0, 0, 0, 1, -2], ![0, 0, -1, 0, -2], ![6, 21, 14, 21, -43]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 4 2 5 [13, 6, 5, 7, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 26, 6, 7], [31, 29, 11, 15], [34, 30, 26, 21], [0, 1]]
 g := ![![[32, 34, 40, 16], [34, 26, 36, 36], [21, 8, 1], [36, 1], []], ![[32, 38, 27, 41, 30, 12], [12, 18, 39, 21, 3, 20], [2, 24, 25], [9, 25, 26, 19, 20, 19], [33, 42, 6]], ![[42, 13, 40, 33, 23, 35], [40, 21, 42, 9, 42, 9], [42, 30, 9], [39, 14, 30, 28, 1, 6], [24, 2, 10]], ![[3, 29, 10, 10, 3, 4], [6, 11, 18, 34, 15, 15], [24, 4, 1], [2, 4, 18, 25, 36, 38], [22, 26, 11]]]
 h' := ![![[14, 26, 6, 7], [31, 31, 19, 4], [10, 17, 19, 37], [5, 29, 29, 1], [0, 0, 1], [0, 1]], ![[31, 29, 11, 15], [11, 9, 9, 33], [31, 39, 3, 40], [33, 27, 36, 38], [25, 27, 5, 31], [14, 26, 6, 7]], ![[34, 30, 26, 21], [40, 11, 5, 17], [5, 35, 23, 32], [32, 22, 37, 3], [4, 37, 14, 40], [31, 29, 11, 15]], ![[0, 1], [15, 35, 10, 32], [2, 38, 41, 20], [20, 8, 27, 1], [10, 22, 23, 15], [34, 30, 26, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [23, 22, 13], []]
 b := ![[], [], [32, 24, 34, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 4
  hpos := by decide
  P := [13, 6, 5, 7, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![38615433318, 104861318004, 134590624465, 73616343251, 31161446149]
  a := ![-1, 0, -4, 2, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3450075432, -12779745375, -7740257390, -14231057489, 31161446149]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 3418801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 16, 13, 1, -2]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![13, 16, 13, 1, -2]] 
 ![![43, 0, 0, 0, 0], ![42, 1, 0, 0, 0], ![42, 0, 1, 0, 0], ![42, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![13, 16, 13, 1, -2], ![-12, -17, -13, -1, 2], ![12, 18, 12, 1, -2], ![-12, -18, -11, -2, 2], ![0, 0, -1, 1, -1]]]
  hmulB := by decide  
  f := ![![![31, 44, 13, -1, -2]], ![![30, 43, 13, -1, -2]], ![![30, 42, 12, -1, -2]], ![![30, 42, 11, -2, -2]], ![![0, 0, -1, -1, -1]]]
  g := ![![![-29, 16, 13, 1, -2], ![30, -17, -13, -1, 2], ![-30, 18, 12, 1, -2], ![30, -18, -11, -2, 2], ![0, 0, -1, 1, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![31, 44, 13, -1, -2]] ![![13, 16, 13, 1, -2]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![769, 2491, 1994, 103, -280]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![769, 2491, 1994, 103, -280]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![32, 0, 10, 28, 1]] where
  M :=![![![769, 2491, 1994, 103, -280], ![-1680, -3431, -1606, 34, 206], ![1236, 1410, -307, -164, 68], ![408, 2256, 2266, 169, -328], ![-1602, -2961, -1094, 67, 135]]]
  hmulB := by decide  
  f := ![![![11, 25, 30, 15, 6]], ![![36, 101, 130, 72, 30]], ![![180, 486, 623, 340, 144]], ![![864, 2340, 2986, 1631, 680]], ![![602, 1627, 2076, 1133, 473]]]
  g := ![![![207, 53, 102, 169, -280], ![-176, -73, -78, -122, 206], ![-20, 30, -21, -44, 68], ![232, 48, 118, 199, -328], ![-126, -63, -52, -79, 135]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 4 2 5 [33, 32, 35, 25, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 44, 5, 22], [35, 11, 5, 34], [12, 38, 37, 38], [0, 1]]
 g := ![![[15, 6, 9, 9], [33, 45, 26, 24], [37, 34, 5, 18], [22, 1], []], ![[43, 20, 1, 3, 43, 43], [2, 29, 35, 26, 12, 5], [18, 1, 41, 38, 34, 44], [1, 38, 35, 13, 19, 10], [21, 11, 14]], ![[25, 1, 40, 19, 31, 25], [22, 42, 6, 0, 24, 9], [40, 33, 12, 21, 9, 2], [24, 6, 36, 46, 5, 2], [4, 16, 28]], ![[40, 21, 41, 28, 17, 10], [8, 26, 28, 13, 20, 23], [39, 36, 31, 41, 36, 19], [22, 23, 43, 46, 7, 13], [30, 35, 34]]]
 h' := ![![[22, 44, 5, 22], [39, 45, 8, 44], [1, 15, 18, 20], [26, 15, 44, 26], [0, 0, 1], [0, 1]], ![[35, 11, 5, 34], [7, 41, 38, 9], [22, 26, 18, 34], [34, 10, 36, 7], [26, 8, 43, 3], [22, 44, 5, 22]], ![[12, 38, 37, 38], [41, 33, 1, 36], [9, 3, 13, 31], [18, 28, 17, 41], [12, 20, 23, 41], [35, 11, 5, 34]], ![[0, 1], [43, 22, 0, 5], [10, 3, 45, 9], [26, 41, 44, 20], [0, 19, 27, 3], [12, 38, 37, 38]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [9, 30, 10], []]
 b := ![[], [], [9, 20, 21, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 4
  hpos := by decide
  P := [33, 32, 35, 25, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1125954519, -2332257312, -1438756664, -543925988, 663575836]
  a := ![0, 0, 4, -10, 6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-475752793, -49622496, -171798192, -406894668, 663575836]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 4879681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11, -25, -30, -15, -6]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-11, -25, -30, -15, -6]] 
 ![![47, 0, 0, 0, 0], ![38, 1, 0, 0, 0], ![13, 0, 1, 0, 0], ![23, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![-11, -25, -30, -15, -6], ![-36, -101, -130, -72, -30], ![-180, -486, -623, -340, -144], ![-864, -2340, -2986, -1631, -680], ![-1950, -5289, -6774, -3703, -1559]]]
  hmulB := by decide  
  f := ![![![-769, -2491, -1994, -103, 280]], ![![-586, -1941, -1578, -84, 222]], ![![-239, -719, -545, -25, 76]], ![![-385, -1267, -1024, -54, 144]], ![![-15, -96, -104, -8, 15]]]
  g := ![![![36, -25, -30, -15, -6], ![154, -101, -130, -72, -30], ![737, -486, -623, -340, -144], ![3541, -2340, -2986, -1631, -680], ![8020, -5289, -6774, -3703, -1559]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![769, 2491, 1994, 103, -280]] ![![-11, -25, -30, -15, -6]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0, 0, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0, 0, 0]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![0, 0, 0, 0, 53]] where
  M :=![![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![0, 0, 0, 0, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 5 2 5 [25, 39, 40, 37, 23, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [28, 10, 37, 34, 51], [52, 50, 35, 37, 18], [41, 42, 21, 23, 31], [15, 3, 13, 12, 6], [0, 1]]
 g := ![![[1, 16, 26, 39, 6], [32, 36, 36, 37], [44, 50, 47, 22, 13], [30, 1], []], ![[10, 25, 10, 44, 37, 25, 45, 22], [21, 19, 34, 25], [1, 50, 35, 27, 36, 32, 8, 8], [17, 37, 23, 47], [26, 1, 12, 30, 23, 10, 9, 45]], ![[41, 15, 38, 26, 50, 19, 19, 34], [24, 46, 36, 49], [44, 33, 7, 12, 42, 48, 31, 14], [37, 44, 19, 40], [18, 46, 43, 6, 8, 14, 37, 2]], ![[40, 18, 14, 49, 52, 22, 35, 31], [26, 34, 29, 36], [15, 46, 26, 39, 50, 40, 51, 31], [18, 48, 23, 28], [4, 40, 26, 42, 48, 20, 50, 5]], ![[24, 19, 41, 16, 43, 24, 37, 24], [48, 38, 26, 7], [34, 15, 40, 7, 4, 34, 29, 36], [6, 44, 34, 42], [26, 12, 28, 22, 28, 6, 38, 4]]]
 h' := ![![[28, 10, 37, 34, 51], [5, 45, 41, 27, 18], [13, 13, 31, 26, 14], [45, 24, 33, 16, 15], [0, 0, 0, 1], [0, 1]], ![[52, 50, 35, 37, 18], [22, 48, 3, 4, 25], [21, 37, 14, 8, 48], [15, 36, 8, 42, 46], [49, 9, 23, 34, 10], [28, 10, 37, 34, 51]], ![[41, 42, 21, 23, 31], [43, 31, 22, 33, 7], [22, 18, 28, 49, 7], [16, 7, 35, 18, 28], [26, 47, 40, 38, 27], [52, 50, 35, 37, 18]], ![[15, 3, 13, 12, 6], [32, 1, 6, 4, 1], [29, 2, 25, 14, 6], [14, 34, 16, 6, 52], [27, 28, 14, 13, 44], [41, 42, 21, 23, 31]], ![[0, 1], [26, 34, 34, 38, 2], [22, 36, 8, 9, 31], [16, 5, 14, 24, 18], [22, 22, 29, 20, 25], [15, 3, 13, 12, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 37, 46, 30], [], [], []]
 b := ![[], [38, 22, 46, 40, 15], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 5
  hpos := by decide
  P := [25, 39, 40, 37, 23, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-26666039141841, -72267266283141, -92444722267499, -50515383974868, -21204085172372]
  a := ![13, -1, -3, 1, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-503132813997, -1363533326097, -1744240042783, -953120452356, -400077078724]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 418195493 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def PBC53 : ContainsPrimesAboveP 53 ![I53N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![53, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 53 (by decide) 𝕀

instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-733, -896, -642, -38, 96]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-733, -896, -642, -38, 96]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![22, 28, 27, 1, 0], ![57, 46, 4, 0, 1]] where
  M :=![![![-733, -896, -642, -38, 96], ![576, 707, 506, 30, -76], ![-456, -564, -403, -26, 60], ![360, 444, 310, 17, -52], ![72, 72, 42, -14, -13]]]
  hmulB := by decide  
  f := ![![![-23, -32, -2, 2, 0]], ![![0, -23, -30, -2, 4]], ![![24, 60, 35, -2, -4]], ![![2, 4, 1, -1, 0]], ![![-21, -46, -24, 0, 3]]]
  g := ![![![-91, -72, 0, -38, 96], ![72, 57, 0, 30, -76], ![-56, -44, 1, -26, 60], ![50, 40, 1, 17, -52], ![19, 18, 8, -14, -13]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [44, 48, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [31, 9, 36], [28, 49, 23], [0, 1]]
 g := ![![[6, 21, 15], [19, 45, 1], [6, 45], [3], [1]], ![[54, 16, 25, 12], [0, 1, 14, 28], [56, 15], [37, 53, 15, 20], [24, 41, 5, 46]], ![[24, 27, 34, 24], [2, 23, 21, 38], [14, 25], [0, 23, 3, 39], [37, 31, 1, 13]]]
 h' := ![![[31, 9, 36], [49, 21, 30], [50, 7, 58], [45, 22, 35], [15, 11], [0, 1]], ![[28, 49, 23], [52, 5, 43], [29, 18, 26], [30, 3, 29], [2, 40, 42], [31, 9, 36]], ![[0, 1], [57, 33, 45], [49, 34, 34], [4, 34, 54], [28, 8, 17], [28, 49, 23]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40, 52], []]
 b := ![[], [27, 40, 51], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [44, 48, 0, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![501493, 1408758, 1909437, 1060083, 506937]
  a := ![-1, -3, 2, -1, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-876538, -874452, -487128, 1060083, 506937]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 205379 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 32, 2, -2, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![23, 32, 2, -2, 0]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![37, 32, 1, 0, 0], ![55, 16, 0, 1, 0], ![10, 21, 0, 0, 1]] where
  M :=![![![23, 32, 2, -2, 0], ![0, 23, 30, 2, -4], ![-24, -60, -35, 2, 4], ![24, 36, 2, -7, 4], ![24, 72, 62, 14, -9]]]
  hmulB := by decide  
  f := ![![![733, 896, 642, 38, -96]], ![![-576, -707, -506, -30, 76]], ![![155, 188, 135, 8, -20]], ![![521, 636, 456, 27, -68]], ![![-82, -101, -72, -4, 11]]]
  g := ![![![1, 0, 2, -2, 0], ![-20, -15, 30, 2, -4], ![19, 16, -35, 2, 4], ![5, 0, 2, -7, 4], ![-50, -33, 62, 14, -9]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P1 : CertificateIrreducibleZModOfList' 59 2 2 5 [50, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [54, 58], [0, 1]]
 g := ![![[6, 15], [9, 3], [3], [10, 35], [54, 1]], ![[49, 44], [53, 56], [3], [12, 24], [49, 58]]]
 h' := ![![[54, 58], [22, 30], [44, 11], [31, 48], [14, 34], [0, 1]], ![[0, 1], [49, 29], [48, 48], [27, 11], [21, 25], [54, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57]]
 b := ![[], [27, 58]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N1 : CertifiedPrimeIdeal' SI59N1 59 where
  n := 2
  hpos := by decide
  P := [50, 5, 1]
  hirr := P59P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-892, 276, 6957, 4783, 5884]
  a := ![3, 0, 7, -4, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9834, -7160, 6957, 4783, 5884]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N1 B_one_repr
lemma NI59N1 : Nat.card (O ⧸ I59N1) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-733, -896, -642, -38, 96]] ![![23, 32, 2, -2, 0]]
  ![![59, 0, 0, 0, 0]] where
 M := ![![![-59, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0, 0, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0, 0, 0]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![0, 0, 0, 0, 61]] where
  M :=![![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![0, 0, 0, 0, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 5 2 5 [46, 37, 22, 19, 17, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [24, 10, 38, 38, 49], [27, 24, 3, 52, 49], [7, 17, 34, 12, 28], [47, 9, 47, 20, 57], [0, 1]]
 g := ![![[26, 25, 16, 46, 12], [42, 18, 43, 48], [3, 3, 27, 12, 56], [26, 44, 1], []], ![[7, 10, 45, 49, 50, 46, 25, 13], [28, 15, 21, 3], [20, 27, 32, 46, 31, 23, 43, 58], [18, 28, 20, 6, 33, 32, 11, 41], [59, 56, 4, 42, 35, 27, 42, 41]], ![[30, 8, 58, 15, 6, 16, 53, 41], [55, 35, 45, 52], [57, 32, 11, 44, 46, 25, 19, 16], [7, 42, 16, 33, 2, 28, 22, 57], [57, 10, 14, 52, 25, 28, 51, 41]], ![[18, 27, 19, 0, 19, 19, 8, 32], [54, 44, 31, 13], [59, 40, 9, 29, 0, 15, 18, 44], [22, 59, 12, 25, 11, 7, 25, 55], [27, 38, 27, 52, 42, 8, 56, 53]], ![[34, 53, 26, 24, 26, 10, 26, 1], [38, 25, 45, 39], [34, 48, 17, 28, 48, 59, 30, 14], [14, 45, 15, 40, 40, 25, 13, 5], [21, 14, 49, 0, 30, 29, 35, 58]]]
 h' := ![![[24, 10, 38, 38, 49], [32, 25, 18, 57, 45], [45, 22, 6, 22, 32], [24, 3, 11, 26, 42], [0, 0, 0, 1], [0, 1]], ![[27, 24, 3, 52, 49], [45, 42, 40, 35, 59], [33, 12, 4, 26, 53], [37, 11, 8, 4, 31], [8, 16, 14, 14, 12], [24, 10, 38, 38, 49]], ![[7, 17, 34, 12, 28], [12, 11, 20, 16, 49], [23, 45, 32, 15, 33], [31, 55, 27, 7, 43], [42, 21, 14, 6, 38], [27, 24, 3, 52, 49]], ![[47, 9, 47, 20, 57], [53, 28, 56, 4, 55], [55, 59, 59, 9, 14], [48, 50, 31, 48, 43], [16, 57, 17, 44, 51], [7, 17, 34, 12, 28]], ![[0, 1], [18, 16, 49, 10, 36], [34, 45, 21, 50, 51], [41, 3, 45, 37, 24], [11, 28, 16, 57, 21], [47, 9, 47, 20, 57]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51, 24, 59, 54], [], [], []]
 b := ![[], [37, 14, 24, 55, 35], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 5
  hpos := by decide
  P := [46, 37, 22, 19, 17, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4635004086184, 12562978254163, 16074326720007, 8784214751110, 3689347331190]
  a := ![1, 1, 2, -1, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![75983673544, 205950463183, 263513552787, 144003520510, 60481103790]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 844596301 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def PBC61 : ContainsPrimesAboveP 61 ![I61N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![61, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 61 (by decide) 𝕀



lemma PB441I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB441I1 : PrimesBelowBoundCertificateInterval O 23 61 441 where
  m := 9
  g := ![3, 2, 3, 1, 2, 2, 1, 2, 1]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB441I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1, I29N2]
    · exact ![I31N0, I31N1]
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0]
    · exact ![I59N0, I59N1]
    · exact ![I61N0]
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
    · exact ![24389, 29, 29]
    · exact ![923521, 31]
    · exact ![50653, 37, 37]
    · exact ![115856201]
    · exact ![3418801, 43]
    · exact ![4879681, 47]
    · exact ![418195493]
    · exact ![205379, 3481]
    · exact ![844596301]
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
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
  β := ![I29N1, I29N2, I31N1, I37N1, I37N2, I43N1, I47N1]
  Il := ![[I29N1, I29N2], [I31N1], [I37N1, I37N2], [], [I43N1], [I47N1], [], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
