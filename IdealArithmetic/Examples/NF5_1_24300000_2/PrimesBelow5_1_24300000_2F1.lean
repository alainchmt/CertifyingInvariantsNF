
import IdealArithmetic.Examples.NF5_1_24300000_2.RI5_1_24300000_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-637, 544, -906, 688, -1052]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![-637, 544, -906, 688, -1052]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![11, 27, 1, 0, 0], ![11, 4, 0, 1, 0], ![1, 24, 0, 0, 1]] where
  M :=![![![-637, 544, -906, 688, -1052], ![-2144, 1249, 868, -1448, 3076], ![7960, -8876, 1429, 108, -5612], ![-9990, 9736, -7570, 4905, -4020], ![-3870, 3332, 1158, -1992, 5449]]]
  hmulB := by decide  
  f := ![![![124023, -82440, 19862, -7480, 85420]], ![![319240, -34435, -11980, -38216, 40540]], ![![345905, -56849, -6045, -39324, 63636]], ![![71195, -29764, 5168, -6167, 31320]], ![![257165, -31724, -8236, -30360, 36677]]]
  g := ![![![97, 1638, -906, 688, -1052], ![40, -3111, 868, -1448, 3076], ![-115, 2993, 1429, 108, -5612], ![805, 10034, -7570, 4905, -4020], ![-5, -5198, 1158, -1992, 5449]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [4, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 28], [0, 1]]
 g := ![![[27, 22], [6], [20, 4], [8, 1]], ![[0, 7], [6], [23, 25], [16, 28]]]
 h' := ![![[8, 28], [25, 15], [7, 8], [26, 2], [0, 1]], ![[0, 1], [0, 14], [13, 21], [13, 27], [8, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [5, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [4, 21, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1978, -505, 709, 170, -238]
  a := ![-13, -7, -11, 0, -26]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-257, -504, 709, 170, -238]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![496, -695, 209, 9, 710]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![496, -695, 209, 9, 710]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![20, 13, 1, 0, 0], ![15, 13, 0, 1, 0], ![11, 11, 0, 0, 1]] where
  M :=![![![496, -695, 209, 9, 710], ![2867, -706, 33, -301, 764], ![2153, 1071, -544, -397, -1042], ![-4113, 2001, -399, 326, -2094], ![-3362, 442, 98, 394, -507]]]
  hmulB := by decide  
  f := ![![![-108, 65, 109, -133, 272]], ![![689, -676, 71, 79, -526]], ![![170, -193, 71, -36, -50]], ![![268, -296, 139, -80, -26]], ![![265, -275, 78, -20, -121]]]
  g := ![![![-401, -391, 209, 9, 710], ![-58, -194, 33, -301, 764], ![1050, 854, -544, -397, -1042], ![759, 896, -399, 326, -2094], ![-195, -13, 98, 394, -507]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P1 : CertificateIrreducibleZModOfList' 29 2 2 4 [3, 28, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 28], [0, 1]]
 g := ![![[19, 7], [24], [16, 4], [1, 1]], ![[26, 22], [24], [20, 25], [2, 28]]]
 h' := ![![[1, 28], [28, 23], [10, 13], [26, 27], [0, 1]], ![[0, 1], [22, 6], [23, 16], [24, 2], [1, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [21, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N1 : CertifiedPrimeIdeal' SI29N1 29 where
  n := 2
  hpos := by decide
  P := [3, 28, 1]
  hirr := P29P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4564, 51876, -21345, 22693, 1085]
  a := ![19, -56, 15, -67, 35]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2414, 773, -21345, 22693, 1085]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N1 B_one_repr
lemma NI29N1 : Nat.card (O ⧸ I29N1) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N1

def I29N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-58, -13, 9, 9, 12]] i)))

def SI29N2: IdealEqSpanCertificate' Table ![![-58, -13, 9, 9, 12]] 
 ![![29, 0, 0, 0, 0], ![18, 1, 0, 0, 0], ![24, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![18, 0, 0, 0, 1]] where
  M :=![![![-58, -13, 9, 9, 12], ![75, -64, 17, -3, 66], ![255, -43, -4, -29, 48], ![15, 95, -35, -12, -96], ![-136, 74, -16, 10, -77]]]
  hmulB := by decide  
  f := ![![![-158, -29, -75, -5, -90]], ![![-111, -20, -51, -5, -60]], ![![-153, -35, -72, -7, -90]], ![![-67, -8, -32, -1, -36]], ![![-100, -16, -46, -4, -53]]]
  g := ![![![-11, -13, 9, 9, 12], ![-12, -64, 17, -3, 66], ![16, -43, -4, -29, 48], ![33, 95, -35, -12, -96], ![8, 74, -16, 10, -77]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N2 : Nat.card (O ⧸ I29N2) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N2)

lemma isPrimeI29N2 : Ideal.IsPrime I29N2 := prime_ideal_of_norm_prime hp29.out _ NI29N2
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![-637, 544, -906, 688, -1052]] ![![496, -695, 209, 9, 710]]
  ![![158, 29, 75, 5, 90]] where
 M := ![![![158, 29, 75, 5, 90]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI29N1 : IdealMulLeCertificate' Table 
  ![![158, 29, 75, 5, 90]] ![![-58, -13, 9, 9, 12]]
  ![![29, 0, 0, 0, 0]] where
 M := ![![![-29, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-112, 20, -44, -3, -24]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![-112, 20, -44, -3, -24]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![22, 25, 7, 1, 0], ![20, 18, 10, 0, 1]] where
  M :=![![![-112, 20, -44, -3, -24], ![-105, -111, -10, -61, -42], ![-351, -92, -275, 83, -408], ![-639, 192, -162, -82, 66], ![87, -98, 104, -81, 95]]]
  hmulB := by decide  
  f := ![![![542, -20, -34, -69, 30]], ![![-87, 379, -128, -29, -384]], ![![-1623, 524, -63, 157, -558]], ![![-79, 397, -135, -32, -402]], ![![-209, 360, -112, -11, -367]]]
  g := ![![![14, 17, 7, -3, -24], ![67, 70, 27, -61, -42], ![193, 167, 104, 83, -408], ![-5, 34, -8, -82, 66], ![-1, 7, -9, -81, 95]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 3 2 4 [2, 15, 22, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [23, 20, 19], [17, 10, 12], [0, 1]]
 g := ![![[4, 22, 14], [0, 17, 4], [5, 25, 19], [1]], ![[6, 5, 19, 7], [15, 11, 21, 28], [10, 13, 25, 20], [14, 13, 1, 8]], ![[17, 7, 15, 21], [25, 0, 22, 27], [5, 30], [27, 6, 1, 23]]]
 h' := ![![[23, 20, 19], [0, 4, 18], [21, 3, 2], [29, 16, 9], [0, 1]], ![[17, 10, 12], [16, 14, 8], [23, 1, 15], [18, 8, 22], [23, 20, 19]], ![[0, 1], [8, 13, 5], [24, 27, 14], [23, 7], [17, 10, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28, 27], []]
 b := ![[], [3, 16, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 3
  hpos := by decide
  P := [2, 15, 22, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7900, 3220, -3364, 272, -2238]
  a := ![-2, -4, -2, -3, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![996, 1184, 552, 272, -2238]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 29791 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-542, 20, 34, 69, -30]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![-542, 20, 34, 69, -30]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![23, 17, 1, 0, 0], ![6, 7, 0, 1, 0], ![29, 13, 0, 0, 1]] where
  M :=![![![-542, 20, 34, 69, -30], ![87, -379, 128, 29, 384], ![1623, -524, 63, -157, 558], ![837, 396, -204, -152, -384], ![-477, 502, -142, 9, -515]]]
  hmulB := by decide  
  f := ![![![112, -20, 44, 3, 24]], ![![105, 111, 10, 61, 42]], ![![152, 49, 47, 33, 54]], ![![66, 15, 16, 17, 12]], ![![146, 31, 42, 31, 37]]]
  g := ![![![-28, -21, 34, 69, -30], ![-457, -250, 128, 29, 384], ![-486, -250, 63, -157, 558], ![567, 320, -204, -152, -384], ![570, 308, -142, 9, -515]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P1 : CertificateIrreducibleZModOfList' 31 2 2 4 [25, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [20, 30], [0, 1]]
 g := ![![[24, 5], [20, 9], [1, 9], [20, 1]], ![[0, 26], [14, 22], [26, 22], [9, 30]]]
 h' := ![![[20, 30], [27, 25], [6, 28], [27, 3], [0, 1]], ![[0, 1], [0, 6], [8, 3], [25, 28], [20, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [29, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N1 : CertifiedPrimeIdeal' SI31N1 31 where
  n := 2
  hpos := by decide
  P := [25, 11, 1]
  hirr := P31P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![13746, 3005, 7679, -341, 9066]
  a := ![23, 27, 19, 12, 45]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-13669, -7839, 7679, -341, 9066]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N1 B_one_repr
lemma NI31N1 : Nat.card (O ⧸ I31N1) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![-112, 20, -44, -3, -24]] ![![-542, 20, 34, 69, -30]]
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

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-853, -108, -384, -36, -420]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![-853, -108, -384, -36, -420]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![22, 28, 15, 1, 0], ![36, 19, 25, 0, 1]] where
  M :=![![![-853, -108, -384, -36, -420], ![-1788, -433, -600, -312, -636], ![-3480, -1428, -1693, -252, -2508], ![-4500, 12, -1920, -157, -1692], ![-72, 72, 204, -204, 431]]]
  hmulB := by decide  
  f := ![![![4847, -900, -48, -540, 996]], ![![2364, 2267, -984, -552, -2244]], ![![-10632, 5316, -1081, 828, -5556]], ![![62, 3308, -1179, -361, -3336]], ![![-1248, 3785, -1249, -240, -3841]]]
  g := ![![![407, 240, 288, -36, -420], ![756, 551, 540, -312, -636], ![2496, 1440, 1751, -252, -2508], ![1618, 988, 1155, -157, -1692], ![-300, -65, -203, -204, 431]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [26, 29, 30, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [36, 23, 25], [8, 13, 12], [0, 1]]
 g := ![![[10, 36, 28], [11, 33], [30, 4, 30], [7, 1], []], ![[3, 8, 24, 36], [15, 12], [34, 17, 2, 28], [7, 21], [12, 33]], ![[0, 27, 0, 34], [11, 28], [29, 33, 7, 25], [23, 11], [25, 33]]]
 h' := ![![[36, 23, 25], [19, 25, 19], [34, 34, 12], [3, 30, 20], [0, 0, 1], [0, 1]], ![[8, 13, 12], [5, 23, 21], [5, 3, 7], [6, 33, 11], [22, 6, 13], [36, 23, 25]], ![[0, 1], [0, 26, 34], [8, 0, 18], [30, 11, 6], [6, 31, 23], [8, 13, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 11], []]
 b := ![[], [3, 32, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [26, 29, 30, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1531309, -1593087, -870201, 1101813, -3008014]
  a := ![-33, -9, -27, 15, -65]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2312971, 667795, 1562242, 1101813, -3008014]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 50653 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![38, 82, -218, 237, -354]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![38, 82, -218, 237, -354]] 
 ![![37, 0, 0, 0, 0], ![19, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![16, 0, 0, 1, 0], ![8, 0, 0, 0, 1]] where
  M :=![![![38, 82, -218, 237, -354], ![-705, 765, 202, -319, 1068], ![3315, -2958, 1195, -345, -846], ![-1857, 2546, -2348, 1950, -1992], ![-1669, 1530, 28, -401, 1567]]]
  hmulB := by decide  
  f := ![![![-177820, -5178, 15320, 23885, 1992]], ![![-89161, -6513, 9072, 12394, 4950]], ![![-27159, -5628, 4057, 4164, 5184]], ![![-71041, 2378, 4542, 9068, -3690]], ![![-44457, 3754, 2038, 5433, -4595]]]
  g := ![![![-14, 82, -218, 237, -354], ![-554, 765, 202, -319, 1068], ![1650, -2958, 1195, -345, -846], ![-1199, 2546, -2348, 1950, -1992], ![-1003, 1530, 28, -401, 1567]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![56, 151, 53, 9, 160]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![56, 151, 53, 9, 160]] 
 ![![37, 0, 0, 0, 0], ![25, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![30, 0, 0, 1, 0], ![23, 0, 0, 0, 1]] where
  M :=![![![56, 151, 53, 9, 160], ![667, -202, 329, -63, 214], ![667, 505, -114, 507, -164], ![99, 795, 513, -254, 1332], ![416, -462, 312, -214, 129]]]
  hmulB := by decide  
  f := ![![![-82956, -2793, 7281, 11183, 1310]], ![![-55003, -3701, 5484, 7612, 2734]], ![![-1405, -2331, 934, 433, 2326]], ![![-64581, -75, 4923, 8482, -1098]], ![![-54428, 551, 3931, 7083, -1545]]]
  g := ![![![-213, 151, 53, 9, 160], ![37, -202, 329, -63, 214], ![-620, 505, -114, 507, -164], ![-1212, 795, 513, -254, 1332], ![383, -462, 312, -214, 129]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![-853, -108, -384, -36, -420]] ![![38, 82, -218, 237, -354]]
  ![![-461402, 249050, -221974, 62991, -74946]] where
 M := ![![![-461402, 249050, -221974, 62991, -74946]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![-461402, 249050, -221974, 62991, -74946]] ![![56, 151, 53, 9, 160]]
  ![![37, 0, 0, 0, 0]] where
 M := ![![![-32720247, -147373775, 91719411, -132344856, 90112094]]]
 hmul := by decide  
 g := ![![![![-884331, -3983075, 2478903, -3576888, 2435462]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2148854, -285063, -61727, -251555, 326626]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![2148854, -285063, -61727, -251555, 326626]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![12, 17, 35, 1, 0], ![6, 38, 38, 0, 1]] where
  M :=![![![2148854, -285063, -61727, -251555, 326626], ![551839, 1182320, -461547, -198525, -1182704], ![-5326391, 2257175, -397434, 458135, -2373854], ![-4336425, -850151, 630569, 659688, 778830], ![735390, -1715910, 553370, 86538, 1744387]]]
  hmulB := by decide  
  f := ![![![1986, 2933, -615, 2087, -152]], ![![5653, 3762, 6955, -3165, 12370]], ![![39985, -15297, 9802, 4705, -6620]], ![![36839, -9860, 10834, 3616, -454]], ![![42406, -10122, 15550, 1584, 5651]]]
  g := ![![![78238, -205376, -89490, -251555, 326626], ![244643, 1207317, 1254380, -198525, -1182704], ![83393, 2065252, 1799373, 458135, -2373854], ![-412821, -1016107, -1269611, 659688, 778830], ![-262668, -1694482, -1677126, 86538, 1744387]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [17, 38, 23, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 14, 22], [15, 26, 19], [0, 1]]
 g := ![![[36, 20, 9], [3, 39], [4, 33], [40, 18, 1], []], ![[8, 38, 13, 29], [5, 9], [24, 18], [9, 8, 16, 30], [21, 33]], ![[18, 38, 4, 26], [5, 23], [36, 21], [35, 12, 5, 34], [24, 33]]]
 h' := ![![[3, 14, 22], [0, 31, 3], [16, 15, 30], [17, 19, 19], [0, 0, 1], [0, 1]], ![[15, 26, 19], [33, 12, 22], [35, 8, 3], [22, 26, 10], [21, 37, 26], [3, 14, 22]], ![[0, 1], [39, 39, 16], [40, 18, 8], [23, 37, 12], [22, 4, 14], [15, 26, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31, 35], []]
 b := ![[], [16, 23, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [17, 38, 23, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1103901, -1203432, 1067488, -821284, 813872]
  a := ![14, -4, 12, -22, 28]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![148197, -443140, -27188, -821284, 813872]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 68921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1540682, -9734, 120266, 203199, -18180]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-1540682, -9734, 120266, 203199, -18180]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![29, 12, 1, 0, 0], ![31, 25, 0, 1, 0], ![5, 17, 0, 0, 1]] where
  M :=![![![-1540682, -9734, 120266, 203199, -18180], ![536877, -1180857, 378484, 55513, 1201014], ![4970595, -1431154, 131183, -499559, 1534092], ![2050407, 1357446, -637332, -413840, -1332138], ![-1729281, 1515554, -406892, 65247, -1560329]]]
  hmulB := by decide  
  f := ![![![15092, -2546, 572, 5403, -6186]], ![![-8535, 33439, 2074, 1927, 26232]], ![![10877, 6596, 2561, 3800, 4224]], ![![7276, 18967, 852, 6618, 9702]], ![![-2968, 14799, 524, 1567, 10603]]]
  g := ![![![-274065, -151801, 120266, 203199, -18180], ![-443052, -671408, 378484, 55513, 1201014], ![219077, -404779, 131183, -499559, 1534092], ![976165, 1024336, -637332, -413840, -1332138], ![386575, 763236, -406892, 65247, -1560329]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P1 : CertificateIrreducibleZModOfList' 41 2 2 5 [4, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 40], [0, 1]]
 g := ![![[33, 31], [4], [21], [40, 40], [1]], ![[0, 10], [4], [21], [8, 1], [1]]]
 h' := ![![[32, 40], [16, 20], [14, 2], [4, 29], [37, 32], [0, 1]], ![[0, 1], [0, 21], [37, 39], [30, 12], [36, 9], [32, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [15, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N1 : CertifiedPrimeIdeal' SI41N1 41 where
  n := 2
  hpos := by decide
  P := [4, 9, 1]
  hirr := P41P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11261, 2743, 6221, 175, 6930]
  a := ![29, 19, 20, 10, 45]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5103, -4734, 6221, 175, 6930]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N1 B_one_repr
lemma NI41N1 : Nat.card (O ⧸ I41N1) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![2148854, -285063, -61727, -251555, 326626]] ![![-1540682, -9734, 120266, 203199, -18180]]
  ![![41, 0, 0, 0, 0]] where
 M := ![![![-4851182633035, 557589549387, 169867302499, 577071447842, -650663761850]]]
 hmul := by decide  
 g := ![![![![-118321527635, 13599745107, 4143104939, 14074913362, -15869847850]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-67, 49, -7, 6, -44]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![-67, 49, -7, 6, -44]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![38, 37, 31, 1, 0], ![37, 1, 21, 0, 1]] where
  M :=![![![-67, 49, -7, 6, -44], ![-158, 20, 17, 24, -8], ![40, -101, 60, 18, 136], ![378, -87, 27, -29, 126], ![179, 12, -18, -25, -9]]]
  hmulB := by decide  
  f := ![![![21, -21, 9, -4, -4]], ![![-28, 34, -33, 26, -28]], ![![-34, 21, 58, -64, 128]], ![![-26, 22, 22, -27, 62]], ![![0, -6, 34, -33, 57]]]
  g := ![![![31, -3, 17, 6, -44], ![-18, -20, -13, 24, -8], ![-132, -21, -78, 18, 136], ![-74, 20, -40, -29, 126], ![34, 22, 22, -25, -9]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [10, 28, 27, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 36], [2, 6], [0, 1]]
 g := ![![[33, 13, 25], [16, 25, 6], [36, 21], [13, 16, 1], []], ![[41, 40, 21], [37, 25, 36], [29, 25], [3, 36, 6], []], ![[30, 33, 40], [4, 36, 1], [35, 40], [6, 34, 36], []]]
 h' := ![![[14, 36], [12, 0, 38], [28, 2, 36], [42, 35, 8], [0, 0, 1], [0, 1]], ![[2, 6], [21, 34, 13], [17, 25, 1], [36, 36, 5], [24, 19, 6], [14, 36]], ![[0, 1], [35, 9, 35], [4, 16, 6], [15, 15, 30], [4, 24, 36], [2, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18], []]
 b := ![[], [21, 19, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [10, 28, 27, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![23289, -21495, 11553, -6723, 1162]
  a := ![3, -3, 3, -6, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![5483, 5258, 4548, -6723, 1162]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 79507 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![21, -21, 9, -4, -4]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![21, -21, 9, -4, -4]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![30, 24, 1, 0, 0], ![27, 7, 0, 1, 0], ![3, 20, 0, 0, 1]] where
  M :=![![![21, -21, 9, -4, -4], ![-28, 34, -33, 26, -28], ![-34, 21, 58, -64, 128], ![174, -165, 27, 13, -114], ![-35, 44, -56, 47, -61]]]
  hmulB := by decide  
  f := ![![![-67, 49, -7, 6, -44]], ![![-158, 20, 17, 24, -8]], ![![-134, 43, 6, 18, -32]], ![![-59, 32, -1, 7, -26]], ![![-74, 13, 7, 11, -7]]]
  g := ![![![-3, -3, 9, -4, -4], ![8, 28, -33, 26, -28], ![-10, -81, 58, -64, 128], ![-15, 32, 27, 13, -114], ![13, 53, -56, 47, -61]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P1 : CertificateIrreducibleZModOfList' 43 2 2 5 [15, 42, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 42], [0, 1]]
 g := ![![[20, 23], [16, 1], [38], [14, 1], [1]], ![[0, 20], [17, 42], [38], [15, 42], [1]]]
 h' := ![![[1, 42], [18, 25], [14, 42], [5, 9], [28, 1], [0, 1]], ![[0, 1], [0, 18], [13, 1], [14, 34], [29, 42], [1, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [8, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N1 : CertifiedPrimeIdeal' SI43N1 43 where
  n := 2
  hpos := by decide
  P := [15, 42, 1]
  hirr := P43P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5026, -120, 2159, 495, 1803]
  a := ![19, 9, 16, -1, 35]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1826, -2127, 2159, 495, 1803]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N1 B_one_repr
lemma NI43N1 : Nat.card (O ⧸ I43N1) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![-67, 49, -7, 6, -44]] ![![21, -21, 9, -4, -4]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1052, -124, 124, 151, 104]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-1052, -124, 124, 151, 104]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![6, 18, 7, 1, 0], ![11, 26, 43, 0, 1]] where
  M :=![![![-1052, -124, 124, 151, 104], ![869, -985, 282, -7, 1010], ![4019, -876, 11, -439, 968], ![843, 1320, -534, -250, -1338], ![-1835, 1194, -288, 117, -1239]]]
  hmulB := by decide  
  f := ![![![38622, 9180, 15906, 3969, 18866]], ![![87371, 20765, 35984, 8977, 42680]], ![![197651, 46972, 81399, 20311, 96542]], ![![71656, 17030, 29511, 7363, 35002]], ![![238160, 56600, 98083, 24473, 116331]]]
  g := ![![![-66, -118, -115, 151, 104], ![-217, -577, -917, -7, 1010], ![-85, -386, -820, -439, 968], ![363, 864, 1250, -250, -1338], ![236, 666, 1110, 117, -1239]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [32, 20, 22, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 45, 17], [25, 1, 30], [0, 1]]
 g := ![![[0, 31, 18], [18, 25, 7], [18, 40, 12], [41, 25, 1], []], ![[33, 5, 21, 21], [9, 19, 31, 36], [32, 26, 16, 3], [11, 34, 41, 17], [13, 7]], ![[7, 15, 31, 20], [11, 1, 5, 46], [36, 36, 0, 30], [25, 23, 8, 26], [0, 7]]]
 h' := ![![[0, 45, 17], [35, 18, 21], [35, 21, 30], [4, 25, 23], [0, 0, 1], [0, 1]], ![[25, 1, 30], [41, 46, 45], [10, 8, 11], [24, 4, 25], [7, 33, 1], [0, 45, 17]], ![[0, 1], [27, 30, 28], [40, 18, 6], [11, 18, 46], [14, 14, 45], [25, 1, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25, 33], []]
 b := ![[], [33, 42, 34], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [32, 20, 22, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-217771, 389723, 137485, -124116, 540035]
  a := ![21, 7, 17, -8, 41]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-115180, -242917, -472664, -124116, 540035]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 103823 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-38622, -9180, -15906, -3969, -18866]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-38622, -9180, -15906, -3969, -18866]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![20, 33, 1, 0, 0], ![46, 30, 0, 1, 0], ![19, 17, 0, 0, 1]] where
  M :=![![![-38622, -9180, -15906, -3969, -18866], ![-87371, -20765, -35984, -8977, -42680], ![-197651, -46972, -81399, -20311, -96542], ![-179865, -42756, -74076, -18484, -87864], ![1961, 466, 806, 203, 955]]]
  hmulB := by decide  
  f := ![![![1052, 124, -124, -151, -104]], ![![-869, 985, -282, 7, -1010]], ![![-248, 763, -251, -50, -774]], ![![457, 722, -290, -138, -718]], ![![150, 381, -146, -61, -381]]]
  g := ![![![17458, 20330, -15906, -3969, -18866], ![39493, 45991, -35984, -8977, -42680], ![89339, 104037, -81399, -20311, -96542], ![81305, 94680, -74076, -18484, -87864], ![-886, -1031, 806, 203, 955]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P1 : CertificateIrreducibleZModOfList' 47 2 2 5 [13, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [45, 46], [0, 1]]
 g := ![![[11, 25], [3, 9], [16, 42], [44, 4], [1]], ![[8, 22], [32, 38], [26, 5], [36, 43], [1]]]
 h' := ![![[45, 46], [8, 42], [27, 3], [39, 29], [34, 45], [0, 1]], ![[0, 1], [18, 5], [21, 44], [28, 18], [38, 2], [45, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [2, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N1 : CertifiedPrimeIdeal' SI47N1 47 where
  n := 2
  hpos := by decide
  P := [13, 2, 1]
  hirr := P47P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2593, -202, 1209, 110, 762]
  a := ![15, 8, 11, 1, 26]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-875, -1199, 1209, 110, 762]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N1 B_one_repr
lemma NI47N1 : Nat.card (O ⧸ I47N1) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-1052, -124, 124, 151, 104]] ![![-38622, -9180, -15906, -3969, -18866]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179305, 42614, 73848, 18422, 87590]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![179305, 42614, 73848, 18422, 87590]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![22, 25, 52, 43, 1]] where
  M :=![![![179305, 42614, 73848, 18422, 87590], ![405626, 96395, 167048, 41684, 198122], ![917540, 218114, 377885, 94290, 448226], ![835074, 198434, 343936, 85785, 407922], ![-9084, -2180, -3750, -930, -4465]]]
  hmulB := by decide  
  f := ![![![405, -30, -20, -50, 38]], ![![2, 259, -92, -28, -262]], ![![-1132, 406, -59, 106, -430]], ![![-702, -242, 140, 117, 234]], ![![-1506, 305, 6, 165, -333]]]
  g := ![![![-32975, -40512, -84544, -70716, 87590], ![-74586, -91635, -191232, -159954, 198122], ![-168744, -207312, -432639, -361876, 448226], ![-153570, -188672, -393736, -329337, 407922], ![1682, 2065, 4310, 3605, -4465]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 4 2 5 [47, 40, 42, 11, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [44, 35, 43, 41], [43, 51, 51, 33], [8, 19, 12, 32], [0, 1]]
 g := ![![[25, 39, 40, 37], [27, 42, 43], [7, 45, 47, 52], [26, 42, 1], []], ![[31, 2, 6, 1, 18, 33], [42, 12, 10], [44, 50, 10, 45, 17, 45], [13, 25, 29], [44, 21, 50, 14, 7, 21]], ![[15, 33, 45, 8, 12, 18], [15, 38, 4], [31, 24, 10, 2, 16, 8], [43, 43, 10], [20, 40, 34, 41, 5, 3]], ![[51, 12, 7, 35, 7, 26], [27, 30, 16], [23, 27, 5, 51, 33, 34], [9, 19, 36], [22, 9, 9, 51, 34, 14]]]
 h' := ![![[44, 35, 43, 41], [18, 42, 20, 39], [42, 52, 1, 19], [50, 7, 43, 30], [0, 0, 0, 1], [0, 1]], ![[43, 51, 51, 33], [40, 35, 27, 39], [0, 41, 32, 40], [10, 22, 44, 6], [12, 34, 2, 33], [44, 35, 43, 41]], ![[8, 19, 12, 32], [27, 40, 38, 11], [34, 31, 6, 51], [10, 9, 42, 25], [21, 6, 12, 13], [43, 51, 51, 33]], ![[0, 1], [9, 42, 21, 17], [18, 35, 14, 49], [12, 15, 30, 45], [8, 13, 39, 6], [8, 19, 12, 32]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [29, 16, 6], []]
 b := ![[], [], [9, 3, 47, 48], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 4
  hpos := by decide
  P := [47, 40, 42, 11, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-247992254, 318981964, -127683232, 77959669, 49656844]
  a := ![9, -7, 1, -25, 11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-25291374, -17404512, -51129040, -38816691, 49656844]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 7890481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![405, -30, -20, -50, 38]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![405, -30, -20, -50, 38]] 
 ![![53, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![17, 0, 1, 0, 0], ![52, 0, 0, 1, 0], ![30, 0, 0, 0, 1]] where
  M :=![![![405, -30, -20, -50, 38], ![2, 259, -92, -28, -262], ![-1132, 406, -59, 106, -430], ![-702, -242, 140, 117, 234], ![272, -356, 106, 2, 363]]]
  hmulB := by decide  
  f := ![![![179305, 42614, 73848, 18422, 87590]], ![![27952, 6643, 11512, 2872, 13654]], ![![74825, 17784, 30817, 7688, 36552]], ![![191678, 45554, 78944, 19693, 93634]], ![![101322, 24080, 41730, 10410, 49495]]]
  g := ![![![45, -30, -20, -50, 38], ![176, 259, -92, -28, -262], ![91, 406, -59, 106, -430], ![-278, -242, 140, 117, 234], ![-196, -356, 106, 2, 363]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![179305, 42614, 73848, 18422, 87590]] ![![405, -30, -20, -50, 38]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-32217, -7626, -13298, -3276, -15772]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-32217, -7626, -13298, -3276, -15772]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![25, 7, 54, 42, 1]] where
  M :=![![![-32217, -7626, -13298, -3276, -15772], ![-72916, -17247, -29950, -7548, -35428], ![-164356, -39558, -67771, -16924, -80716], ![-150360, -35186, -62086, -15177, -73416], ![1454, 544, 724, 78, 1047]]]
  hmulB := by decide  
  f := ![![![-971, -418, 222, 172, 404]], ![![2132, -1385, 330, -132, 1436]], ![![5348, -542, -213, -644, 644]], ![![-744, 2294, -758, -147, -2328]], ![![4149, 821, -606, -632, -753]]]
  g := ![![![6137, 1742, 14210, 11172, -15772], ![13776, 3911, 31918, 25092, -35428], ![31416, 8906, 72727, 57172, -80716], ![28560, 8114, 66142, 52005, -73416], ![-419, -115, -946, -744, 1047]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 4 2 5 [42, 40, 17, 2, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 47, 8, 16], [3, 13, 14, 56], [44, 57, 37, 46], [0, 1]]
 g := ![![[11, 27, 1, 20], [29, 31, 20, 57], [15, 4, 53], [20, 46, 57, 1], []], ![[37, 36, 45, 12, 54, 1], [22, 41, 12, 43, 17, 45], [58, 51, 49], [9, 24, 7, 3, 48, 20], [12, 15, 37, 5, 17, 25]], ![[21, 30, 58, 17, 55, 47], [38, 35, 1, 33, 35, 50], [3, 26, 35], [27, 51, 52, 58, 20, 13], [28, 30, 48, 11, 19, 32]], ![[5, 30, 11, 30, 40, 46], [17, 27, 5, 46, 40, 27], [58, 43, 41], [22, 54, 16, 3, 57, 41], [48, 30, 36, 4, 25, 45]]]
 h' := ![![[10, 47, 8, 16], [21, 44, 19, 43], [38, 31, 26, 23], [45, 41, 28, 42], [0, 0, 0, 1], [0, 1]], ![[3, 13, 14, 56], [16, 0, 18, 15], [34, 48, 43, 6], [13, 1, 2, 52], [24, 10, 55, 4], [10, 47, 8, 16]], ![[44, 57, 37, 46], [17, 41, 7, 2], [20, 7, 12, 11], [38, 37, 50, 34], [31, 36, 36, 25], [3, 13, 14, 56]], ![[0, 1], [24, 33, 15, 58], [36, 32, 37, 19], [17, 39, 38, 49], [37, 13, 27, 29], [44, 57, 37, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [10, 49, 52], []]
 b := ![[], [], [57, 54, 27, 37], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 4
  hpos := by decide
  P := [42, 40, 17, 2, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5604382, 1699768, 2485652, 624088, 3185272]
  a := ![-8, -4, -8, -3, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1254702, -349104, -2873204, -2256904, 3185272]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 12117361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![971, 418, -222, -172, -404]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![971, 418, -222, -172, -404]] 
 ![![59, 0, 0, 0, 0], ![42, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![30, 0, 0, 1, 0], ![52, 0, 0, 0, 1]] where
  M :=![![![971, 418, -222, -172, -404], ![-2132, 1385, -330, 132, -1436], ![-5348, 542, 213, 644, -644], ![744, -2294, 758, 147, 2328], ![3402, -1504, 276, -286, 1579]]]
  hmulB := by decide  
  f := ![![![32217, 7626, 13298, 3276, 15772]], ![![24170, 5721, 9974, 2460, 11828]], ![![6062, 1446, 2501, 620, 2972]], ![![18930, 4474, 7814, 1923, 9264]], ![![28370, 6712, 11708, 2886, 13883]]]
  g := ![![![185, 418, -222, -172, -404], ![210, 1385, -330, 132, -1436], ![-258, 542, 213, 644, -644], ![-558, -2294, 758, 147, 2328], ![-146, -1504, 276, -286, 1579]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-32217, -7626, -13298, -3276, -15772]] ![![971, 418, -222, -172, -404]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2890, -731, 1219, -49, 644]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![2890, -731, 1219, -49, 644]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![15, 44, 27, 1, 0], ![51, 15, 3, 0, 1]] where
  M :=![![![2890, -731, 1219, -49, 644], ![2429, 2772, -185, 1843, 350], ![6929, 3387, 6808, -2563, 11408], ![17757, -7207, 4927, 1464, -2160], ![-1908, 2318, -3100, 2574, -3439]]]
  hmulB := by decide  
  f := ![![![-62010, 19309, -2153, 6077, -20606]], ![![-64193, -16874, 10857, 10223, 15856]], ![![94093, -74825, 19428, -4365, 77194]], ![![-16954, -40775, 15760, 6574, 40826]], ![![-62330, 8884, 1572, 7231, -10095]]]
  g := ![![![-479, -135, 10, -49, 644], ![-706, -1370, -836, 1843, 350], ![-8794, -901, 685, -2563, 11408], ![1737, -643, -461, 1464, -2160], ![2211, -973, -1021, 2574, -3439]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [22, 47, 12, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [34, 57, 48], [15, 3, 13], [0, 1]]
 g := ![![[4, 24, 1], [60, 14], [22, 34, 20], [58, 10, 22], [1]], ![[51, 39, 32, 60], [30, 15], [23, 13, 35, 3], [14, 51, 2, 57], [53, 44, 58, 60]], ![[9, 6, 8, 47], [23, 16], [59, 44, 29, 41], [55, 3, 10, 47], [19, 49, 45, 1]]]
 h' := ![![[34, 57, 48], [38, 18, 1], [4, 12, 40], [5, 39, 52], [39, 14, 49], [0, 1]], ![[15, 3, 13], [31, 51, 13], [52, 53, 25], [9, 18, 15], [13, 54, 26], [34, 57, 48]], ![[0, 1], [1, 53, 47], [43, 57, 57], [59, 4, 55], [29, 54, 47], [15, 3, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42, 3], []]
 b := ![[], [50, 55, 19], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [22, 47, 12, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1444382, 140940, 532974, 125794, 520126]
  a := ![19, 14, 15, 9, 35]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-442114, -216326, -72522, 125794, 520126]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 226981 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-62010, 19309, -2153, 6077, -20606]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![-62010, 19309, -2153, 6077, -20606]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![23, 7, 1, 0, 0], ![11, 18, 0, 1, 0], ![7, 2, 0, 0, 1]] where
  M :=![![![-62010, 19309, -2153, 6077, -20606], ![-64193, -16874, 10857, 10223, 15856], ![94093, -74825, 19428, -4365, 77194], ![179937, -14179, -8609, -22098, 17574], ![40996, 34750, -15444, -9086, -34311]]]
  hmulB := by decide  
  f := ![![![2890, -731, 1219, -49, 644]], ![![2429, 2772, -185, 1843, 350]], ![![1482, 98, 550, 151, 470]], ![![1529, 568, 246, 559, 184]], ![![380, 45, 83, 97, 29]]]
  g := ![![![1064, -554, -2153, 6077, -20606], ![-8809, -5059, 10857, 10223, 15856], ![-13854, -4699, 19428, -4365, 77194], ![8164, 6700, -8609, -22098, 17574], ![12071, 6148, -15444, -9086, -34311]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P1 : CertificateIrreducibleZModOfList' 61 2 2 5 [4, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [44, 60], [0, 1]]
 g := ![![[50, 46], [45], [26, 56], [57, 34], [44, 1]], ![[0, 15], [45], [50, 5], [28, 27], [27, 60]]]
 h' := ![![[44, 60], [22, 30], [18, 17], [16, 42], [7, 41], [0, 1]], ![[0, 1], [0, 31], [34, 44], [34, 19], [42, 20], [44, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [52, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N1 : CertifiedPrimeIdeal' SI61N1 61 where
  n := 2
  hpos := by decide
  P := [4, 17, 1]
  hirr := P61P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11700, -5855, -4441, 8930, -16392]
  a := ![-41, -9, -36, 21, -85]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2137, -1684, -4441, 8930, -16392]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N1 B_one_repr
lemma NI61N1 : Nat.card (O ⧸ I61N1) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![2890, -731, 1219, -49, 644]] ![![-62010, 19309, -2153, 6077, -20606]]
  ![![61, 0, 0, 0, 0]] where
 M := ![![![61, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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
    · exact ![79507, 1849]
    · exact ![103823, 2209]
    · exact ![7890481, 53]
    · exact ![12117361, 59]
    · exact ![226981, 3721]
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
  β := ![I29N2, I37N1, I37N2, I53N1, I59N1]
  Il := ![[I29N2], [], [I37N1, I37N2], [], [], [], [I53N1], [I59N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
