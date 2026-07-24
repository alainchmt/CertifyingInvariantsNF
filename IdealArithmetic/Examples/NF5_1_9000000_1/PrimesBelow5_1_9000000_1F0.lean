
import IdealArithmetic.Examples.NF5_1_9000000_1.RI5_1_9000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![26, 10, 8, 5, 9]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![26, 10, 8, 5, 9]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![26, 10, 8, 5, 9], ![36, 17, 10, 8, 12], ![24, 13, 9, 6, 12], ![6, -4, 2, -1, 0], ![-6, 1, -2, 0, -1]]]
  hmulB := by decide  
  f := ![![![7, -3, -2, -1, 3]], ![![6, -3, -2, -6, -6]], ![![-12, 5, 3, -2, -12]], ![![-27, 13, 8, 16, 9]], ![![9, -4, -2, 1, 8]]]
  g := ![![![13, 10, 8, 5, 9], ![18, 17, 10, 8, 12], ![12, 13, 9, 6, 12], ![3, -4, 2, -1, 0], ![-3, 1, -2, 0, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, 4, 2, -7, -18]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![-7, 4, 2, -7, -18]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-7, 4, 2, -7, -18], ![-72, 35, 22, 26, -6], ![-12, 10, 9, 54, 84], ![204, -91, -55, -34, 81], ![6, -5, -5, -36, -58]]]
  hmulB := by decide  
  f := ![![![-80, 69, -17, 20, 21]], ![![42, -60, 49, -18, 39]], ![![78, -31, -42, -8, -93]], ![![-247, 214, -56, 62, 60]], ![![114, -100, 28, -29, -25]]]
  g := ![![![0, 4, 2, -7, -18], ![-49, 35, 22, 26, -6], ![-33, 10, 9, 54, 84], ![119, -91, -55, -34, 81], ![21, -5, -5, -36, -58]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1491, 689, 465, 328, 568]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![1491, 689, 465, 328, 568]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![1491, 689, 465, 328, 568], ![2272, 908, 722, 450, 832], ![1664, 699, 458, 340, 518], ![-100, 170, -2, 55, 86], ![-112, -168, -49, -66, -107]]]
  hmulB := by decide  
  f := ![![![1838, -827, -506, -414, 544]], ![![1088, -564, -413, -1464, -1786]], ![![-2653, 1139, 647, -298, -2334]], ![![-5756, 2764, 1850, 4147, 3226]], ![![3435, -1511, -893, -208, 1995]]]
  g := ![![![229, 689, 465, 328, 568], ![359, 908, 722, 450, 832], ![344, 699, 458, 340, 518], ![-92, 170, -2, 55, 86], ![22, -168, -49, -66, -107]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![26, 10, 8, 5, 9]] ![![-7, 4, 2, -7, -18]]
  ![![76, 34, 24, 16, 27]] where
 M := ![![![76, 34, 24, 16, 27]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![76, 34, 24, 16, 27]] ![![-7, 4, 2, -7, -18]]
  ![![158, 143, 101, 132, 174]] where
 M := ![![![158, 143, 101, 132, 174]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![158, 143, 101, 132, 174]] ![![1491, 689, 465, 328, 568]]
  ![![695850, 302513, 214184, 146290, 253772]] where
 M := ![![![695850, 302513, 214184, 146290, 253772]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![695850, 302513, 214184, 146290, 253772]] ![![1491, 689, 465, 328, 568]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![2038172598, 886072674, 627353500, 428489208, 743308264]]]
 hmul := by decide  
 g := ![![![![1019086299, 443036337, 313676750, 214244604, 371654132]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 7, 2, 1]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![37, 0, 7, 2, 1]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![37, 0, 7, 2, 1], ![4, 45, -4, 16, 10], ![20, 1, 29, 2, 38], ![74, -53, 1, -15, -37], ![-44, 29, -2, 8, 19]]]
  hmulB := by decide  
  f := ![![![55, -22, -11, 32, 93]], ![![124, -57, -36, -48, 2]], ![![4, -7, -9, -86, -146]], ![![-354, 159, 97, 75, -113]], ![![21, -5, 1, 68, 132]]]
  g := ![![![12, 0, 7, 2, 1], ![-2, 45, -4, 16, 10], ![-6, 1, 29, 2, 38], ![37, -53, 1, -15, -37], ![-21, 29, -2, 8, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![143, 62, 44, 30, 52]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![143, 62, 44, 30, 52]] 
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![143, 62, 44, 30, 52], ![208, 91, 64, 44, 76], ![152, 66, 47, 32, 56], ![8, 2, 2, 1, 2], ![-20, -8, -6, -4, -7]]]
  hmulB := by decide  
  f := ![![![-3, 2, 0, 2, 0]], ![![-1, 1, 0, 2, 4]], ![![7, -4, -1, -2, 0]], ![![-2, 2, -2, -3, -10]], ![![-5, 2, 2, 2, 1]]]
  g := ![![![-25, 62, 44, 30, 52], ![-37, 91, 64, 44, 76], ![-27, 66, 47, 32, 56], ![0, 2, 2, 1, 2], ![3, -8, -6, -4, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1

def I3N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-21, 8, 12, 2, 26]] i)))

def SI3N2: IdealEqSpanCertificate' Table ![![-21, 8, 12, 2, 26]] 
 ![![3, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-21, 8, 12, 2, 26], ![104, -83, 12, -24, -40], ![-80, 94, -59, 28, -32], ![-116, 48, 60, 13, 136], ![68, -30, -32, -8, -75]]]
  hmulB := by decide  
  f := ![![![1705, 740, 524, 358, 622]], ![![1966, 853, 604, 412, 716]], ![![1171, 510, 361, 246, 426]], ![![591, 260, 184, 127, 218]], ![![-76, -34, -24, -16, -27]]]
  g := ![![![-17, 8, 12, 2, 26], ![94, -83, 12, -24, -40], ![-79, 94, -59, 28, -32], ![-95, 48, 60, 13, 136], ![56, -30, -32, -8, -75]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N2 : Nat.card (O ⧸ I3N2) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N2)

lemma isPrimeI3N2 : Ideal.IsPrime I3N2 := prime_ideal_of_norm_prime hp3.out _ NI3N2
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 7, 2, 1]] ![![143, 62, 44, 30, 52]]
  ![![6351, 2752, 1955, 1332, 2313]] where
 M := ![![![6351, 2752, 1955, 1332, 2313]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N1 : IdealMulLeCertificate' Table 
  ![![6351, 2752, 1955, 1332, 2313]] ![![143, 62, 44, 30, 52]]
  ![![1742165, 757384, 536243, 366258, 635357]] where
 M := ![![![1742165, 757384, 536243, 366258, 635357]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![1742165, 757384, 536243, 366258, 635357]] ![![-21, 8, 12, 2, 26]]
  ![![1379, 964, 307, 416, 467]] where
 M := ![![![1379, 964, 307, 416, 467]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N3 : IdealMulLeCertificate' Table 
  ![![1379, 964, 307, 416, 467]] ![![-21, 8, 12, 2, 26]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![30237, -34164, 20019, -10110, 9021]]]
 hmul := by decide  
 g := ![![![![10079, -11388, 6673, -3370, 3007]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N1, I3N1, I3N2, I3N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N1
    exact isPrimeI3N1
    exact isPrimeI3N2
    exact isPrimeI3N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1 ⊙ MulI3N2 ⊙ MulI3N3)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, 4, -1, 2, -1]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![-5, 4, -1, 2, -1]] 
 ![![5, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![-5, 4, -1, 2, -1], ![-4, 1, 4, 4, 14], ![28, -17, -3, -6, -2], ![-2, 9, -13, -9, -23], ![-4, -3, 8, 0, 1]]]
  hmulB := by decide  
  f := ![![![9951, 4326, 3063, 2092, 3629]], ![![10864, 4723, 3344, 2284, 3962]], ![![6098, 2651, 1877, 1282, 2224]], ![![8054, 3501, 2479, 1693, 2937]], ![![3710, 1613, 1142, 780, 1353]]]
  g := ![![![-5, 4, -1, 2, -1], ![-12, 1, 4, 4, 14], ![26, -17, -3, -6, -2], ![14, 9, -13, -9, -23], ![-2, -3, 8, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![-5, 4, -1, 2, -1]] ![![-5, 4, -1, 2, -1]]
  ![![-19, 22, -10, -6, 16]] where
 M := ![![![-19, 22, -10, -6, 16]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![-19, 22, -10, -6, 16]] ![![-5, 4, -1, 2, -1]]
  ![![-325, 14, 343, 164, 501]] where
 M := ![![![-325, 14, 343, 164, 501]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![-325, 14, 343, 164, 501]] ![![-5, 4, -1, 2, -1]]
  ![![8841, -7144, 1228, -4128, -3436]] where
 M := ![![![8841, -7144, 1228, -4128, -3436]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![8841, -7144, 1228, -4128, -3436]] ![![-5, 4, -1, 2, -1]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![40755, -19500, -14925, 18890, -19805]]]
 hmul := by decide  
 g := ![![![![8151, -3900, -2985, 3778, -3961]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, -21, 12, -6, 4]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![23, -21, 12, -6, 4]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![1, 1, 1, 0, 0], ![6, 0, 0, 1, 0], ![3, 4, 0, 0, 1]] where
  M :=![![![23, -21, 12, -6, 4], ![16, 11, -30, 4, -44], ![-88, 63, 7, 18, 56], ![104, -112, 60, -33, 20], ![-56, 61, -34, 18, -13]]]
  hmulB := by decide  
  f := ![![![33, -15, -10, -22, -16]], ![![-64, 27, 14, -32, -100]], ![![-33, 15, 9, 4, -16]], ![![34, -14, -8, 3, 28]], ![![-3, 0, -2, -36, -65]]]
  g := ![![![5, -7, 12, -6, 4], ![22, 31, -30, 4, -44], ![-53, -24, 7, 18, 56], ![26, -36, 60, -33, 20], ![-13, 21, -34, 18, -13]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [4, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 6], [0, 1]]
 g := ![![[2, 2], [6, 1]], ![[0, 5], [5, 6]]]
 h' := ![![[6, 6], [4, 4], [0, 1]], ![[0, 1], [0, 3], [6, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [1, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 2
  hpos := by decide
  P := [4, 1, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-720, 253, 403, 524, 491]
  a := ![0, -7, 2, -8, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-820, -302, 403, 524, 491]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1597, -684, -387, 206, 1451]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![1597, -684, -387, 206, 1451]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![4, 2, 1, 0, 0], ![6, 2, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![1597, -684, -387, 206, 1451], ![5804, -2731, -1780, -3264, -1666], ![-3332, 1247, 533, -3378, -8126], ![-19154, 8777, 5515, 6913, -1175], ![2556, -981, -446, 2192, 5543]]]
  hmulB := by decide  
  f := ![![![-9333, -4130, -2885, -1988, -3449]], ![![-13796, -5847, -4284, -2848, -5030]], ![![-10712, -4651, -3301, -2250, -3910]], ![![-11960, -5273, -3711, -2541, -4433]], ![![-7842, -3441, -2420, -1660, -2881]]]
  g := ![![![-971, -46, -387, 206, 1451], ![6072, 1051, -1780, -3264, -1666], ![9080, 991, 533, -3378, -8126], ![-10806, -2297, 5515, 6913, -1175], ![-6010, -639, -446, 2192, 5543]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P1 : CertificateIrreducibleZModOfList' 7 2 2 2 [2, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 6], [0, 1]]
 g := ![![[6, 4], [2, 1]], ![[0, 3], [4, 6]]]
 h' := ![![[2, 6], [3, 2], [0, 1]], ![[0, 1], [0, 5], [2, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [3, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N1 : CertifiedPrimeIdeal' SI7N1 7 where
  n := 2
  hpos := by decide
  P := [2, 5, 1]
  hirr := P7P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-33686, 13185, 18666, 17106, 6726]
  a := ![3, -62, -1, -63, -119]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-35906, -8337, 18666, 17106, 6726]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N1 B_one_repr
lemma NI7N1 : Nat.card (O ⧸ I7N1) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N1

def I7N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2179, 947, 671, 458, 795]] i)))

def SI7N2: IdealEqSpanCertificate' Table ![![2179, 947, 671, 458, 795]] 
 ![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![2179, 947, 671, 458, 795], ![3180, 1381, 978, 668, 1158], ![2316, 1010, 713, 488, 846], ![102, 43, 33, 21, 39], ![-296, -128, -92, -62, -109]]]
  hmulB := by decide  
  f := ![![![-11, 3, -1, -36, -69]], ![![-41, 18, 11, 4, -21]], ![![-27, 13, 8, 16, 9]], ![![89, -40, -26, -29, 12]], ![![8, -6, -6, -42, -67]]]
  g := ![![![-893, 947, 671, 458, 795], ![-1301, 1381, 978, 668, 1158], ![-951, 1010, 713, 488, 846], ![-43, 43, 33, 21, 39], ![122, -128, -92, -62, -109]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N2 : Nat.card (O ⧸ I7N2) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N2)

lemma isPrimeI7N2 : Ideal.IsPrime I7N2 := prime_ideal_of_norm_prime hp7.out _ NI7N2
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![23, -21, 12, -6, 4]] ![![1597, -684, -387, 206, 1451]]
  ![![11, -3, 1, 36, 69]] where
 M := ![![![11, -3, 1, 36, 69]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI7N1 : IdealMulLeCertificate' Table 
  ![![11, -3, 1, 36, 69]] ![![2179, 947, 671, 458, 795]]
  ![![7, 0, 0, 0, 0]] where
 M := ![![![-7, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N1, I7N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N1
    exact isPrimeI7N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0 ⊙ MulI7N1)
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


def P11P0 : CertificateIrreducibleZModOfList' 11 5 2 3 [10, 4, 3, 4, 5, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 9, 0, 10, 2], [0, 7, 6, 10, 2], [10, 7, 3, 9, 3], [0, 9, 2, 4, 4], [0, 1]]
 g := ![![[7, 3, 8, 3, 3], [1], []], ![[4, 10, 4, 4, 9, 4, 3, 7], [10, 3, 5, 8, 2, 0, 2, 2], [2, 6, 9, 4]], ![[10, 8, 5, 8, 7, 0, 2, 6], [2, 4, 10, 7, 3, 5, 1, 2], [5, 8, 9, 4]], ![[0, 9, 10, 7, 8, 10, 0, 1], [1, 10, 1, 3, 8, 7, 4, 4], [9, 7, 9, 9]], ![[0, 0, 1, 10, 9, 5, 4, 1], [4, 0, 3, 10, 5, 1, 9, 5], [6, 10, 7, 5]]]
 h' := ![![[7, 9, 0, 10, 2], [1, 7, 8, 7, 6], [0, 0, 1], [0, 1]], ![[0, 7, 6, 10, 2], [1, 5, 3, 3, 3], [7, 3, 5, 5, 10], [7, 9, 0, 10, 2]], ![[10, 7, 3, 9, 3], [2, 6, 2, 1, 6], [5, 10, 0, 8, 10], [0, 7, 6, 10, 2]], ![[0, 9, 2, 4, 4], [0, 4, 6, 2, 2], [10, 1, 8, 6, 4], [10, 7, 3, 9, 3]], ![[0, 1], [4, 0, 3, 9, 5], [6, 8, 8, 3, 9], [0, 9, 2, 4, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 3, 9], [], [], []]
 b := ![[], [6, 0, 4, 1], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 5
  hpos := by decide
  P := [10, 4, 3, 4, 5, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-46051467, 19273991, 9919668, -15919057, -59814777]
  a := ![1, -6, 1, -7, -12]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4186497, 1752181, 901788, -1447187, -5437707]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0, 0, 0]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]] where
  M :=![![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 5 2 3 [12, 12, 2, 7, 4, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 2, 8, 10, 4], [9, 10, 8, 6, 3], [10, 11, 8, 12, 2], [0, 2, 2, 11, 4], [0, 1]]
 g := ![![[3, 9, 7, 1, 3], [9, 1], []], ![[5, 11, 7, 11, 5, 1, 7, 12], [8, 9, 4, 10], [7, 7, 7, 2, 9, 6, 3, 12]], ![[10, 1, 4, 0, 4, 4, 0, 3], [0, 11, 11, 12], [12, 2, 12, 4, 1, 5, 2, 1]], ![[4, 0, 8, 5, 7, 4, 7, 7], [7, 0, 5, 9], [1, 5, 3, 12, 11, 1, 8, 8]], ![[0, 6, 9, 9, 2, 1, 1, 4], [1, 3, 6, 1], [6, 0, 10, 3, 5, 12, 12, 12]]]
 h' := ![![[3, 2, 8, 10, 4], [9, 10, 9, 0, 9], [0, 0, 0, 1], [0, 1]], ![[9, 10, 8, 6, 3], [7, 0, 8, 11, 9], [8, 3, 5, 5, 7], [3, 2, 8, 10, 4]], ![[10, 11, 8, 12, 2], [0, 11, 9, 1, 1], [0, 0, 6, 11, 8], [9, 10, 8, 6, 3]], ![[0, 2, 2, 11, 4], [7, 7, 7, 10, 6], [0, 4, 4, 4, 10], [10, 11, 8, 12, 2]], ![[0, 1], [11, 11, 6, 4, 1], [6, 6, 11, 5, 1], [0, 2, 2, 11, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 12, 11, 10], [], [], []]
 b := ![[], [2, 5, 6, 0, 4], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 5
  hpos := by decide
  P := [12, 12, 2, 7, 4, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![71121365302, -34673450266, -20511192182, -39613474550, -23201770566]
  a := ![1, 25, -3, 24, 59]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![5470874254, -2667188482, -1577784014, -3047190350, -1784751582]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 371293 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def PBC13 : ContainsPrimesAboveP 13 ![I13N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![13, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 13 (by decide) 𝕀

instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0, 0]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0, 0, 0]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]] where
  M :=![![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 5 2 4 [16, 1, 14, 6, 4, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 7, 5, 14, 9], [4, 6, 3, 4, 2], [4, 2, 0, 12, 14], [7, 1, 9, 4, 9], [0, 1]]
 g := ![![[15, 6, 3, 1, 16], [4, 10, 13, 1], [], []], ![[8, 13, 15, 16, 12, 13, 3, 9], [15, 9, 9, 9], [5, 6, 8, 16], [11, 3, 13, 13]], ![[13, 7, 3, 10, 14, 7, 15, 13], [10, 8, 16, 4], [12, 12, 4, 8], [10, 4, 0, 4]], ![[11, 12, 15, 3, 4, 2, 1, 11], [11, 4, 6, 8], [7, 14, 12, 4], [3, 12, 11, 9]], ![[12, 5, 10, 12, 8, 15, 8, 1], [12, 12, 16, 1], [9, 0, 14, 1], [14, 3, 3, 13]]]
 h' := ![![[15, 7, 5, 14, 9], [4, 6, 15, 11, 13], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[4, 6, 3, 4, 2], [11, 3, 12, 9, 16], [9, 9, 5, 16, 3], [15, 15, 4, 8, 13], [15, 7, 5, 14, 9]], ![[4, 2, 0, 12, 14], [6, 7, 9, 4, 10], [8, 8, 8, 8, 2], [9, 8, 1, 7, 5], [4, 6, 3, 4, 2]], ![[7, 1, 9, 4, 9], [13, 1, 1, 15, 6], [11, 5, 12, 3, 12], [2, 8, 12, 10, 15], [4, 2, 0, 12, 14]], ![[0, 1], [12, 0, 14, 12, 6], [0, 12, 9, 7, 16], [12, 3, 16, 9, 1], [7, 1, 9, 4, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 7, 12, 16], [], [], []]
 b := ![[], [8, 12, 11, 13, 2], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 5
  hpos := by decide
  P := [16, 1, 14, 6, 4, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2549295758, -1187393152, -606683420, -629286858, 1047571008]
  a := ![-1, -7, 5, -5, -27]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![149958574, -69846656, -35687260, -37016874, 61621824]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 1419857 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def PBC17 : ContainsPrimesAboveP 17 ![I17N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![17, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 17 (by decide) 𝕀

instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![85, -33, -21, -36, -9]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![85, -33, -21, -36, -9]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![10, 2, 1, 0, 0], ![18, 11, 0, 1, 0], ![5, 12, 0, 0, 1]] where
  M :=![![![85, -33, -21, -36, -9], ![-36, 19, 6, -96, -198], ![-396, 186, 115, 108, -90], ![-162, 93, 75, 361, 513], ![276, -126, -78, -78, 55]]]
  hmulB := by decide  
  f := ![![![79, 51, -177, 18, -261]], ![![-1044, 721, 66, 204, 630]], ![![-2, 38, -59, 12, -72]], ![![-504, 476, -177, 139, 45]], ![![-655, 465, 21, 132, 370]]]
  g := ![![![52, 27, -21, -36, -9], ![138, 181, 6, -96, -198], ![-160, -8, 115, 108, -90], ![-525, -536, 75, 361, 513], ![115, 12, -78, -78, 55]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [5, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 18], [0, 1]]
 g := ![![[3, 4], [6, 6], [16], [1]], ![[0, 15], [11, 13], [16], [1]]]
 h' := ![![[4, 18], [8, 17], [2, 5], [14, 4], [0, 1]], ![[0, 1], [0, 2], [3, 14], [11, 15], [4, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [18, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [5, 15, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6725, -3408, -2186, -3382, -5094]
  a := ![0, -4, -2, -14, 18]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![6049, 5226, -2186, -3382, -5094]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17947, 7805, 5524, 3774, 6546]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![17947, 7805, 5524, 3774, 6546]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![13, 13, 1, 0, 0], ![2, 9, 0, 1, 0], ![9, 1, 0, 0, 1]] where
  M :=![![![17947, 7805, 5524, 3774, 6546], ![26184, 11381, 8062, 5504, 9552], ![19104, 8299, 5877, 4014, 6960], ![828, 374, 254, 179, 306], ![-2432, -1065, -748, -514, -889]]]
  hmulB := by decide  
  f := ![![![-215, 103, 70, 158, 126]], ![![504, -207, -110, 204, 696]], ![![271, -105, -49, 216, 558]], ![![194, -81, -44, 59, 234]], ![![-125, 61, 42, 108, 101]]]
  g := ![![![-6333, -5501, 5524, 3774, 6546], ![-9242, -8027, 8062, 5504, 9552], ![-6735, -5852, 5877, 4014, 6960], ![-294, -255, 254, 179, 306], ![859, 746, -748, -514, -889]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P1 : CertificateIrreducibleZModOfList' 19 2 2 4 [18, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 18], [0, 1]]
 g := ![![[6, 1], [], [17], [1]], ![[12, 18], [], [17], [1]]]
 h' := ![![[6, 18], [0, 1], [18], [1, 6], [0, 1]], ![[0, 1], [6, 18], [18], [18, 13], [6, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [3, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N1 : CertifiedPrimeIdeal' SI19N1 19 where
  n := 2
  hpos := by decide
  P := [18, 13, 1]
  hirr := P19P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1160, -977, 517, 350, 419]
  a := ![13, -7, 4, -6, -23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-528, -593, 517, 350, 419]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N1 B_one_repr
lemma NI19N1 : Nat.card (O ⧸ I19N1) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N1

def I19N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![39947, 17325, 12319, 8384, 14587]] i)))

def SI19N2: IdealEqSpanCertificate' Table ![![39947, 17325, 12319, 8384, 14587]] 
 ![![19, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![10, 0, 0, 1, 0], ![8, 0, 0, 0, 1]] where
  M :=![![![39947, 17325, 12319, 8384, 14587], ![58348, 25273, 17882, 12232, 21130], ![42260, 18652, 13041, 8984, 15566], ![1958, 649, 727, 343, 821], ![-5468, -2272, -1754, -1114, -2059]]]
  hmulB := by decide  
  f := ![![![-8391, 5309, 4647, 26994, 40931]], ![![5084, -1583, -326, 10388, 21450]], ![![5782, -2458, -1373, 1048, 5776]], ![![-23024, 10747, 6929, 11529, 4155]], ![![-8984, 4926, 3820, 16490, 22359]]]
  g := ![![![-19637, 17325, 12319, 8384, 14587], ![-28552, 25273, 17882, 12232, 21130], ![-21030, 18652, 13041, 8984, 15566], ![-926, 649, 727, 343, 821], ![2676, -2272, -1754, -1114, -2059]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N2 : Nat.card (O ⧸ I19N2) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N2)

lemma isPrimeI19N2 : Ideal.IsPrime I19N2 := prime_ideal_of_norm_prime hp19.out _ NI19N2
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![85, -33, -21, -36, -9]] ![![17947, 7805, 5524, 3774, 6546]]
  ![![252319, 109694, 77665, 53046, 92019]] where
 M := ![![![252319, 109694, 77665, 53046, 92019]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI19N1 : IdealMulLeCertificate' Table 
  ![![252319, 109694, 77665, 53046, 92019]] ![![39947, 17325, 12319, 8384, 14587]]
  ![![19, 0, 0, 0, 0]] where
 M := ![![![19362639681, 8417690403, 5959858250, 4070647476, 7061428508]]]
 hmul := by decide  
 g := ![![![![1019086299, 443036337, 313676750, 214244604, 371654132]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0, 0]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0, 0, 0]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]] where
  M :=![![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 5 2 4 [13, 6, 16, 19, 18, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 7, 20, 4, 14], [10, 10, 18, 22, 10], [9, 10, 10, 6, 22], [22, 18, 21, 14], [0, 1]]
 g := ![![[1, 8, 4, 19, 12], [11, 21, 22, 4, 2], [1], []], ![[1, 20, 19, 3, 13, 5, 17, 10], [19, 12, 8, 14, 9, 2, 17, 20], [0, 13, 17, 2, 16, 0, 16, 20], [15, 12, 11, 12]], ![[9, 16, 5, 2, 11, 19, 12, 11], [18, 14, 7, 21, 19, 14, 7, 5], [9, 0, 22, 3, 17, 5, 21, 15], [5, 10, 20, 8]], ![[9, 10, 7, 20, 3, 9, 19, 21], [11, 1, 22, 7, 22, 8, 18, 19], [18, 15, 5, 9, 11, 4, 7, 5], [4, 8, 16, 1]], ![[15, 0, 10, 0, 0, 0, 21], [13, 6, 9, 11, 2, 0, 19], [7, 12, 21, 9, 17, 22, 14], [4, 12]]]
 h' := ![![[10, 7, 20, 4, 14], [18, 14, 5, 22, 9], [10, 17, 7, 4, 5], [0, 0, 1], [0, 1]], ![[10, 10, 18, 22, 10], [0, 22, 8, 2, 2], [21, 21, 6, 0, 13], [20, 9, 17, 6, 13], [10, 7, 20, 4, 14]], ![[9, 10, 10, 6, 22], [10, 12, 5, 18, 13], [12, 15, 3, 10, 14], [12, 17, 14, 22, 17], [10, 10, 18, 22, 10]], ![[22, 18, 21, 14], [8, 19, 21, 19, 5], [21, 15, 22, 15, 21], [6, 6, 6, 18, 15], [9, 10, 10, 6, 22]], ![[0, 1], [14, 2, 7, 8, 17], [22, 1, 8, 17, 16], [18, 14, 8, 0, 1], [22, 18, 21, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 21, 22, 2], [], [], []]
 b := ![[], [10, 4, 19, 2, 13], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 5
  hpos := by decide
  P := [13, 6, 16, 19, 18, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1345293, -641700, -499652, -1318958, -1374756]
  a := ![-1, -1, -1, -2, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![58491, -27900, -21724, -57346, -59772]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 6436343 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def PBC23 : ContainsPrimesAboveP 23 ![I23N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![23, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 23 (by decide) 𝕀



lemma PB187I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB187I0 : PrimesBelowBoundCertificateInterval O 1 23 187 where
  m := 9
  g := ![5, 5, 5, 3, 1, 1, 1, 3, 1]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB187I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N1, I3N1, I3N2, I3N2]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1, I7N2]
    · exact ![I11N0]
    · exact ![I13N0]
    · exact ![I17N0]
    · exact ![I19N0, I19N1, I19N2]
    · exact ![I23N0]
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
    · exact ![49, 49, 7]
    · exact ![161051]
    · exact ![371293]
    · exact ![1419857]
    · exact ![361, 361, 19]
    · exact ![6436343]
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
      exact NI3N1
      exact NI3N1
      exact NI3N2
      exact NI3N2
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
      exact NI7N2
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
      exact NI19N2
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I3N2, I5N0, I7N0, I7N1, I7N2, I19N2]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N1, I3N1, I3N2, I3N2], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N0, I7N1, I7N2], [], [], [], [I19N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
