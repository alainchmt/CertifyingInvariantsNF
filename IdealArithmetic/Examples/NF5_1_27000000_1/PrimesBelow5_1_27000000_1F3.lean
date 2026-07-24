
import IdealArithmetic.Examples.NF5_1_27000000_1.RI5_1_27000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-489, 298, -112, 96, -118]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![-489, 298, -112, 96, -118]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![0, 0, 107, 0, 0], ![76, 78, 42, 1, 0], ![56, 70, 46, 0, 1]] where
  M :=![![![-489, 298, -112, 96, -118], ![944, -495, 168, -84, 192], ![-1240, 640, -303, 60, -180], ![248, -264, 316, -111, -36], ![-28, 274, -166, 328, -117]]]
  hmulB := by decide  
  f := ![![![309, 346, 156, 72, -6]], ![![48, 667, 536, 252, 144]], ![![-600, 40, 291, 140, 180]], ![![12, 742, 614, 289, 172]], ![![-76, 632, 560, 264, 171]]]
  g := ![![![-11, 10, 12, 96, -118], ![-32, -69, -48, -84, 192], ![40, 80, 51, 60, -180], ![100, 102, 62, -111, -36], ![-172, -160, -80, 328, -117]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [32, 9, 49, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 46, 59], [36, 60, 48], [0, 1]]
 g := ![![[6, 45, 9], [53, 81, 37], [93, 11], [53, 59, 42], [77, 47], [1]], ![[50, 0, 103, 93], [69, 1, 17, 50], [82, 69], [82, 34, 81, 94], [29, 69], [25, 65, 48, 46]], ![[93, 38, 79, 81], [69, 82, 97, 102], [86, 61], [99, 34, 47, 16], [80, 14], [73, 59, 102, 61]]]
 h' := ![![[22, 46, 59], [16, 26, 104], [62, 70, 12], [16, 36, 92], [58, 91, 91], [75, 98, 58], [0, 1]], ![[36, 60, 48], [4, 51, 70], [86, 96, 35], [28, 104, 47], [51, 41, 22], [4, 73, 60], [22, 46, 59]], ![[0, 1], [58, 30, 40], [59, 48, 60], [52, 74, 75], [64, 82, 101], [22, 43, 96], [36, 60, 48]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 93], []]
 b := ![[], [20, 22, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [32, 9, 49, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2310050, -255486, -1092375, 772161, 555285]
  a := ![0, 8, 5, -1, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-817478, -928542, -552021, 772161, 555285]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 1225043 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-33, -15, 2, 1, 6]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![-33, -15, 2, 1, 6]] 
 ![![107, 0, 0, 0, 0], ![30, 1, 0, 0, 0], ![70, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![81, 0, 0, 0, 1]] where
  M :=![![![-33, -15, 2, 1, 6], ![-48, -48, -20, -9, 2], ![16, -25, -27, -13, -10], ![64, 19, -12, -6, -14], ![56, -22, -42, -20, -21]]]
  hmulB := by decide  
  f := ![![![-43, -31, 10, -69, 26]], ![![-14, -8, 4, -19, 6]], ![![-22, -21, 5, -43, 18]], ![![-5, -2, -2, -7, 4]], ![![-41, -23, 12, -55, 17]]]
  g := ![![![-2, -15, 2, 1, 6], ![25, -48, -20, -9, 2], ![33, -25, -27, -13, -10], ![14, 19, -12, -6, -14], ![51, -22, -42, -20, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 5, 2, 1, 0]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![5, 5, 2, 1, 0]] 
 ![![107, 0, 0, 0, 0], ![101, 1, 0, 0, 0], ![92, 0, 1, 0, 0], ![65, 0, 0, 1, 0], ![46, 0, 0, 0, 1]] where
  M :=![![![5, 5, 2, 1, 0], ![0, 10, 8, 3, 2], ![-8, 1, 5, 3, 2], ![-8, -9, -4, 0, 2], ![-20, -4, 4, 0, 5]]]
  hmulB := by decide  
  f := ![![![423, -251, 110, -69, 84]], ![![393, -233, 102, -64, 78]], ![![372, -221, 97, -61, 74]], ![![253, -150, 66, -41, 50]], ![![186, -110, 48, -30, 37]]]
  g := ![![![-7, 5, 2, 1, 0], ![-19, 10, 8, 3, 2], ![-8, 1, 5, 3, 2], ![11, -9, -4, 0, 2], ![-2, -4, 4, 0, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![-489, 298, -112, 96, -118]] ![![-33, -15, 2, 1, 6]]
  ![![-423, 251, -110, 69, -84]] where
 M := ![![![-423, 251, -110, 69, -84]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![-423, 251, -110, 69, -84]] ![![5, 5, 2, 1, 0]]
  ![![107, 0, 0, 0, 0]] where
 M := ![![![-107, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1, I107N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
    exact isPrimeI107N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0 ⊙ MulI107N1)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1709, -1035, 458, -297, 358]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![1709, -1035, 458, -297, 358]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![0, 0, 109, 0, 0], ![44, 69, 50, 1, 0], ![2, 44, 100, 0, 1]] where
  M :=![![![1709, -1035, 458, -297, 358], ![-2864, 1726, -760, 497, -594], ![3808, -2309, 1015, -663, 794], ![-1744, 1057, -472, 304, -366], ![1536, -938, 406, -272, 321]]]
  hmulB := by decide  
  f := ![![![1, -5, -2, 3, -2]], ![![16, -12, -20, -3, 6]], ![![-32, 1, 7, -23, -6]], ![![-4, -9, -10, -11, 0]], ![![-22, -4, -2, -22, -3]]]
  g := ![![![129, 34, -188, -297, 358], ![-216, -59, 310, 497, -594], ![288, 78, -415, -663, 794], ![-132, -35, 192, 304, -366], ![118, 34, -166, -272, 321]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [89, 12, 89, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [108, 15, 90], [21, 93, 19], [0, 1]]
 g := ![![[49, 80, 5], [37, 31], [0, 36, 49], [103, 48, 15], [108, 73], [1]], ![[68, 80, 40, 18], [69, 64], [20, 35, 80, 42], [31, 100, 33, 23], [7, 71], [39, 67, 55, 8]], ![[4, 55, 48, 6], [71, 43], [74, 104, 90, 32], [105, 4, 91, 37], [65, 61], [82, 65, 61, 101]]]
 h' := ![![[108, 15, 90], [86, 67, 21], [0, 78, 85], [98, 26, 7], [53, 11, 48], [20, 97, 20], [0, 1]], ![[21, 93, 19], [24, 15, 26], [72, 28, 101], [1, 60, 48], [69, 51, 4], [16, 45, 17], [108, 15, 90]], ![[0, 1], [10, 27, 62], [94, 3, 32], [77, 23, 54], [102, 47, 57], [1, 76, 72], [21, 93, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41, 50], []]
 b := ![[], [51, 97, 60], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [89, 12, 89, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![13030849, -2876960, -9894312, 2276686, 7342396]
  a := ![3, -5, -3, -1, -52]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-934203, -4431502, -7871268, 2276686, 7342396]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 1295029 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, -127, -101, -48, -27]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![-7, -127, -101, -48, -27]] 
 ![![109, 0, 0, 0, 0], ![56, 1, 0, 0, 0], ![39, 0, 1, 0, 0], ![79, 0, 0, 1, 0], ![48, 0, 0, 0, 1]] where
  M :=![![![-7, -127, -101, -48, -27], ![216, -139, -212, -100, -96], ![276, 102, -29, -16, -52], ![100, 260, 172, 81, 32], ![414, 278, 56, 24, -51]]]
  hmulB := by decide  
  f := ![![![-885, 133, 689, -68, -527]], ![![-416, 69, 348, -12, -272]], ![![-331, 41, 226, -52, -165]], ![![-755, 103, 547, -91, -409]], ![![-314, 68, 322, 40, -265]]]
  g := ![![![148, -127, -101, -48, -27], ![264, -139, -212, -100, -96], ![-5, 102, -29, -16, -52], ![-267, 260, 172, 81, 32], ![-154, 278, 56, 24, -51]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1

def I109N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![665, -12, -183, 325, 61]] i)))

def SI109N2: IdealEqSpanCertificate' Table ![![665, -12, -183, 325, 61]] 
 ![![109, 0, 0, 0, 0], ![63, 1, 0, 0, 0], ![55, 0, 1, 0, 0], ![89, 0, 0, 1, 0], ![84, 0, 0, 0, 1]] where
  M :=![![![665, -12, -183, 325, 61], ![-488, -180, -552, -813, 650], ![-2356, 293, 1559, -389, -1138], ![4796, 227, -180, 3298, -714], ![2410, -650, -2868, -668, 2453]]]
  hmulB := by decide  
  f := ![![![-9397, 4158, -2493, 1325, -1639]], ![![-5311, 2308, -1419, 738, -923]], ![![-4899, 2197, -1312, 694, -867]], ![![-7573, 3361, -2013, 1069, -1325]], ![![-7282, 3248, -1950, 1028, -1285]]]
  g := ![![![-207, -12, -183, 325, 61], ![541, -180, -552, -813, 650], ![217, 293, 1559, -389, -1138], ![-2139, 227, -180, 3298, -714], ![500, -650, -2868, -668, 2453]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N2 : Nat.card (O ⧸ I109N2) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N2)

lemma isPrimeI109N2 : Ideal.IsPrime I109N2 := prime_ideal_of_norm_prime hp109.out _ NI109N2
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![1709, -1035, 458, -297, 358]] ![![-7, -127, -101, -48, -27]]
  ![![9397, -4158, 2493, -1325, 1639]] where
 M := ![![![9397, -4158, 2493, -1325, 1639]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![9397, -4158, 2493, -1325, 1639]] ![![665, -12, -183, 325, 61]]
  ![![109, 0, 0, 0, 0]] where
 M := ![![![-109, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N1, I109N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N1
    exact isPrimeI109N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0 ⊙ MulI109N1)
instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 2, -11, 37, 21]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![47, 2, -11, 37, 21]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![0, 0, 113, 0, 0], ![0, 0, 0, 113, 0], ![13, 27, 21, 104, 1]] where
  M :=![![![47, 2, -11, 37, 21], ![-168, -36, -28, -101, 74], ![-212, 3, 153, -1, -138], ![636, -9, -120, 342, -38], ![90, -126, -324, -184, 259]]]
  hmulB := by decide  
  f := ![![![177, -108, 47, -31, 37]], ![![-296, 178, -80, 51, -62]], ![![396, -239, 105, -69, 82]], ![![-180, 111, -48, 32, -38]], ![![-141, 87, -38, 25, -30]]]
  g := ![![![-2, -5, -4, -19, 21], ![-10, -18, -14, -69, 74], ![14, 33, 27, 127, -138], ![10, 9, 6, 38, -38], ![-29, -63, -51, -240, 259]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 4 2 6 [109, 82, 102, 6, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [43, 61, 76, 92], [58, 103, 16, 70], [6, 61, 21, 64], [0, 1]]
 g := ![![[39, 38, 93, 72], [69, 108, 81], [51, 67, 44], [63, 6, 77], [22, 47, 107, 1], []], ![[44, 19, 85, 43, 41, 79], [0, 34, 25], [16, 81, 9], [4, 78, 2], [35, 5, 47, 1, 54, 34], [56, 33, 4, 21, 61, 5]], ![[29, 69, 105, 112, 6, 75], [86, 68, 53], [16, 9, 7], [40, 5, 95], [3, 14, 51, 80, 9, 33], [44, 78, 90, 10, 3, 45]], ![[94, 86, 86, 111, 68, 100], [75, 90, 32], [7, 50, 53], [84, 71, 14], [67, 11, 49, 10, 102, 77], [41, 107, 23, 38, 52, 97]]]
 h' := ![![[43, 61, 76, 92], [100, 8, 28, 80], [29, 24, 33, 9], [86, 61, 66, 65], [88, 79, 93, 90], [0, 0, 0, 1], [0, 1]], ![[58, 103, 16, 70], [52, 53, 8, 32], [39, 96, 41, 5], [38, 44, 79, 3], [94, 46, 74, 51], [66, 105, 27, 85], [43, 61, 76, 92]], ![[6, 61, 21, 64], [62, 33, 100, 28], [82, 107, 48, 77], [40, 30, 61, 81], [85, 26, 97, 35], [24, 83, 91, 44], [58, 103, 16, 70]], ![[0, 1], [38, 19, 90, 86], [90, 112, 104, 22], [66, 91, 20, 77], [71, 75, 75, 50], [41, 38, 108, 96], [6, 61, 21, 64]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [87, 96, 88], []]
 b := ![[], [], [82, 94, 110, 73], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 4
  hpos := by decide
  P := [109, 82, 102, 6, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11285372, 4238197, 18985873, 8184546, -17253262]
  a := ![1, 3, 2, -1, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1885018, 4159967, 3374375, 15951538, -17253262]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 163047361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-177, 108, -47, 31, -37]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![-177, 108, -47, 31, -37]] 
 ![![113, 0, 0, 0, 0], ![18, 1, 0, 0, 0], ![55, 0, 1, 0, 0], ![61, 0, 0, 1, 0], ![63, 0, 0, 0, 1]] where
  M :=![![![-177, 108, -47, 31, -37], ![296, -178, 80, -51, 62], ![-396, 239, -105, 69, -82], ![180, -111, 48, -32, 38], ![-162, 96, -42, 28, -33]]]
  hmulB := by decide  
  f := ![![![-47, -2, 11, -37, -21]], ![![-6, 0, 2, -5, -4]], ![![-21, -1, 4, -18, -9]], ![![-31, -1, 7, -23, -11]], ![![-27, 0, 9, -19, -14]]]
  g := ![![![8, 108, -47, 31, -37], ![-15, -178, 80, -51, 62], ![18, 239, -105, 69, -82], ![-8, -111, 48, -32, 38], ![7, 96, -42, 28, -33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![47, 2, -11, 37, 21]] ![![-177, 108, -47, 31, -37]]
  ![![113, 0, 0, 0, 0]] where
 M := ![![![-113, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0)
instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-407, -351, -1043, -262, -457]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![-407, -351, -1043, -262, -457]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![0, 0, 127, 0, 0], ![125, 118, 86, 1, 0], ![44, 44, 3, 0, 1]] where
  M :=![![![-407, -351, -1043, -262, -457], ![3656, -1277, -1092, -910, -524], ![268, 2192, -345, 342, -648], ![764, 1354, 1748, 587, 604], ![1890, 2938, 808, 576, -283]]]
  hmulB := by decide  
  f := ![![![41, -213, -783, -626, 785]], ![![-6280, 297, 2396, -2510, -1252]], ![![8148, 568, 357, 6158, -1884]], ![![-193, 437, 1629, 1225, -1613]], ![![-2126, 40, 591, -1034, -201]]]
  g := ![![![413, 399, 180, -262, -457], ![1106, 1017, 620, -910, -524], ![-110, -76, -219, 342, -648], ![-781, -744, -398, 587, 604], ![-454, -414, -377, 576, -283]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [39, 51, 38, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [105, 43, 76], [111, 83, 51], [0, 1]]
 g := ![![[95, 87, 34], [87, 13, 74], [126, 43, 1], [78, 26, 19], [75, 58, 47], [1]], ![[59, 58, 44, 37], [93, 18, 118, 100], [23, 106, 30, 37], [92, 102, 14, 62], [94, 111, 18, 103], [11, 31, 103, 64]], ![[69, 17, 121, 63], [76, 23, 55, 125], [91, 40, 29, 110], [2, 102, 60, 55], [23, 29, 50, 57], [60, 72, 95, 63]]]
 h' := ![![[105, 43, 76], [36, 6, 62], [39, 61, 70], [6, 104, 1], [123, 6, 20], [88, 76, 89], [0, 1]], ![[111, 83, 51], [59, 94, 14], [15, 74, 32], [70, 94, 113], [41, 74, 84], [99, 87, 82], [105, 43, 76]], ![[0, 1], [58, 27, 51], [118, 119, 25], [126, 56, 13], [20, 47, 23], [41, 91, 83], [111, 83, 51]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62, 4], []]
 b := ![[], [81, 63, 20], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [39, 51, 38, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16970381, 1259863, 7417942, -6368909, -4186618]
  a := ![1, -11, -7, -1, 47]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![7585468, 7377971, 4470110, -6368909, -4186618]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 2048383 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, -213, -783, -626, 785]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![41, -213, -783, -626, 785]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![123, 42, 1, 0, 0], ![41, 97, 0, 1, 0], ![87, 85, 0, 0, 1]] where
  M :=![![![41, -213, -783, -626, 785], ![-6280, 297, 2396, -2510, -1252], ![8148, 568, 357, 6158, -1884], ![10676, -1770, -8672, 417, 6784], ![-19930, -320, 3014, -11808, 673]]]
  hmulB := by decide  
  f := ![![![-407, -351, -1043, -262, -457]], ![![3656, -1277, -1092, -910, -524]], ![![817, -745, -1374, -552, -621]], ![![2667, -1078, -1157, -775, -543]], ![![2183, -1072, -1439, -784, -666]]]
  g := ![![![423, 210, -783, -626, 785], ![-702, 1965, 2396, -2510, -1252], ![-979, -3556, 357, 6158, -1884], ![3701, -2005, -8672, 417, 6784], ![275, 7569, 3014, -11808, 673]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P1 : CertificateIrreducibleZModOfList' 127 2 2 6 [72, 107, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [20, 126], [0, 1]]
 g := ![![[35, 30], [38, 87], [28, 122], [35, 17], [32, 15], [20, 1]], ![[0, 97], [0, 40], [55, 5], [121, 110], [78, 112], [40, 126]]]
 h' := ![![[20, 126], [58, 86], [16, 50], [20, 54], [109, 12], [84, 74], [0, 1]], ![[0, 1], [0, 41], [0, 77], [84, 73], [95, 115], [40, 53], [20, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [68]]
 b := ![[], [41, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N1 : CertifiedPrimeIdeal' SI127N1 127 where
  n := 2
  hpos := by decide
  P := [72, 107, 1]
  hirr := P127P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10250, -414, -862, -9460, -572]
  a := ![-1, 13, 9, 2, -30]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![4200, 7890, -862, -9460, -572]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N1 B_one_repr
lemma NI127N1 : Nat.card (O ⧸ I127N1) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![-407, -351, -1043, -262, -457]] ![![41, -213, -783, -626, 785]]
  ![![127, 0, 0, 0, 0]] where
 M := ![![![127, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC127 : ContainsPrimesAboveP 127 ![I127N0, I127N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
    exact isPrimeI127N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 127 (by decide) (𝕀 ⊙ MulI127N0)
instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0, 0, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0, 0, 0]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![0, 0, 131, 0, 0], ![0, 0, 0, 131, 0], ![0, 0, 0, 0, 131]] where
  M :=![![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![0, 0, 131, 0, 0], ![0, 0, 0, 131, 0], ![0, 0, 0, 0, 131]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 5 2 7 [17, 82, 44, 98, 30, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 114, 56, 84, 57], [64, 48, 19, 95, 107], [76, 49, 12, 110, 24], [59, 50, 44, 104, 74], [0, 1]]
 g := ![![[52, 67, 121, 122, 46], [36, 78, 125, 52, 25], [54, 2, 78, 64], [67, 72, 31, 21], [58, 16, 101, 1], [], []], ![[103, 83, 13, 89, 84, 5, 58, 110], [72, 40, 80, 20, 94, 80, 32, 82], [6, 68, 87, 113], [26, 128, 25, 39], [89, 101, 59, 62], [110, 70, 57, 3], [31, 58, 7, 105]], ![[120, 88, 128, 103, 37, 19, 64, 16], [68, 62, 105, 124, 128, 119, 3, 45], [94, 61, 8, 5], [33, 60, 105, 13], [110, 83, 126, 94], [56, 68, 82, 27], [14, 73, 37, 52]], ![[114, 28, 115, 73, 91, 72, 12, 70], [130, 85, 92, 41, 65, 85, 60, 88], [100, 6, 59, 113], [86, 122, 2, 75], [14, 124, 103, 34], [85, 116, 118, 117], [15, 125, 52, 52]], ![[10, 19, 115, 5, 2, 32, 93, 60], [70, 126, 41, 32, 33, 102, 92, 39], [77, 105, 46, 84], [3, 66, 107, 100], [23, 87, 66, 11], [35, 40, 92, 28], [70, 28, 59, 105]]]
 h' := ![![[33, 114, 56, 84, 57], [43, 13, 66, 130, 35], [19, 16, 4, 54, 5], [85, 51, 93, 88, 123], [62, 81, 52, 116, 26], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[64, 48, 19, 95, 107], [29, 70, 130, 105, 33], [54, 1, 4, 29, 24], [126, 84, 65, 9, 84], [100, 1, 22, 108, 68], [98, 46, 56, 6, 18], [38, 66, 104, 14, 38], [33, 114, 56, 84, 57]], ![[76, 49, 12, 110, 24], [104, 87, 29, 43, 49], [48, 80, 85, 92, 39], [27, 30, 96, 49, 23], [123, 60, 94, 94, 119], [40, 64, 47, 59, 116], [59, 87, 125, 111, 17], [64, 48, 19, 95, 107]], ![[59, 50, 44, 104, 74], [40, 41, 115, 44, 56], [87, 83, 43, 95, 109], [79, 34, 17, 118, 84], [10, 65, 127, 119, 59], [95, 3, 99, 83, 77], [19, 32, 29, 14, 36], [76, 49, 12, 110, 24]], ![[0, 1], [16, 51, 53, 71, 89], [4, 82, 126, 123, 85], [93, 63, 122, 129, 79], [119, 55, 98, 87, 121], [95, 18, 60, 114, 50], [64, 77, 3, 123, 40], [59, 50, 44, 104, 74]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [87, 15, 19, 44], [], [], []]
 b := ![[], [114, 5, 67, 128, 36], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 5
  hpos := by decide
  P := [17, 82, 44, 98, 30, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2064313327, -271534180, -544926988, -1944393700, 939697584]
  a := ![0, -10, -6, -10, 8]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-15758117, -2072780, -4159748, -14842700, 7173264]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 38579489651 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def PBC131 : ContainsPrimesAboveP 131 ![I131N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![131, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 131 (by decide) 𝕀

instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1219093, 737681, -325171, 212128, -254265]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![-1219093, 737681, -325171, 212128, -254265]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![0, 0, 137, 0, 0], ![0, 0, 0, 137, 0], ![10, 30, 127, 27, 1]] where
  M :=![![![-1219093, 737681, -325171, 212128, -254265], ![2034120, -1230839, 542576, -353940, 424256], ![-2714084, 1642288, -723931, 472260, -566068], ![1247212, -754704, 332672, -217023, 260132], ![-1096886, 663710, -292568, 190860, -228769]]]
  hmulB := by decide  
  f := ![![![-27, 1, 11, -12, -9]], ![![72, 9, 8, 52, -24]], ![![60, -12, -71, -20, 64]], ![![-292, 4, 68, -151, -8]], ![![12, -8, -49, -37, 51]]]
  g := ![![![9661, 61063, 233332, 51659, -254265], ![-16120, -101887, -389328, -86196, 424256], ![21508, 135944, 519465, 115008, -566068], ![-9884, -62472, -238716, -52851, 260132], ![8692, 54940, 209935, 46479, -228769]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 4 2 7 [131, 71, 44, 7, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [45, 133, 116, 126], [116, 84, 46, 83], [106, 56, 112, 65], [0, 1]]
 g := ![![[76, 52, 73, 81], [117, 47, 72], [38, 127, 76], [62, 60, 122, 4], [96, 136, 49], [1], []], ![[103, 117, 84, 39, 2, 126], [84, 133, 38], [20, 114, 115], [9, 53, 63, 1, 112, 44], [21, 132, 87], [30, 118, 130], [92, 26, 121]], ![[71, 114, 6, 118, 69, 3], [85, 57, 7], [122, 45, 115], [50, 15, 132, 8, 59, 3], [31, 2, 69], [112, 1, 56], [67, 102, 39]], ![[107, 51, 36, 22, 76, 112], [90, 10, 119], [26, 60, 76], [123, 62, 83, 91, 99, 65], [51, 66, 115], [61, 0, 128], [131, 55, 115]]]
 h' := ![![[45, 133, 116, 126], [82, 66, 71, 128], [105, 17, 21, 49], [98, 54, 64, 79], [64, 135, 106, 2], [6, 66, 93, 130], [0, 0, 1], [0, 1]], ![[116, 84, 46, 83], [43, 80, 10, 136], [19, 102, 41, 60], [6, 47, 53, 72], [49, 99, 21, 74], [34, 48, 88, 19], [111, 114, 82, 33], [45, 133, 116, 126]], ![[106, 56, 112, 65], [118, 35, 3, 77], [108, 128, 130, 12], [46, 39, 133, 65], [64, 82, 34, 60], [17, 95, 86, 53], [21, 136, 100, 78], [116, 84, 46, 83]], ![[0, 1], [118, 93, 53, 70], [20, 27, 82, 16], [136, 134, 24, 58], [120, 95, 113, 1], [15, 65, 7, 72], [103, 24, 91, 26], [106, 56, 112, 65]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [114, 82, 91], []]
 b := ![[], [], [0, 88, 42, 126], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 4
  hpos := by decide
  P := [131, 71, 44, 7, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![75113400, 59060834, 218550484, 239795906, -242054710]
  a := ![13, 10, 7, 1, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![18216500, 53435782, 225981742, 49454548, -242054710]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 352275361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-27, 1, 11, -12, -9]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![-27, 1, 11, -12, -9]] 
 ![![137, 0, 0, 0, 0], ![83, 1, 0, 0, 0], ![76, 0, 1, 0, 0], ![24, 0, 0, 1, 0], ![134, 0, 0, 0, 1]] where
  M :=![![![-27, 1, 11, -12, -9], ![72, 9, 8, 52, -24], ![60, -12, -71, -20, 64], ![-292, 4, 68, -151, -8], ![18, 40, 118, 108, -115]]]
  hmulB := by decide  
  f := ![![![-1219093, 737681, -325171, 212128, -254265]], ![![-723727, 437932, -193041, 125932, -150947]], ![![-696096, 421212, -185671, 121124, -145184]], ![![-204460, 123720, -54536, 35577, -42644]], ![![-1200404, 726372, -320186, 208876, -250367]]]
  g := ![![![4, 1, 11, -12, -9], ![5, 9, 8, 52, -24], ![-12, -12, -71, -20, 64], ![-8, 4, 68, -151, -8], ![4, 40, 118, 108, -115]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![-1219093, 737681, -325171, 212128, -254265]] ![![-27, 1, 11, -12, -9]]
  ![![137, 0, 0, 0, 0]] where
 M := ![![![137, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0)
instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![422359, -255571, 112661, -73492, 88089]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![422359, -255571, 112661, -73492, 88089]] 
 ![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![0, 0, 139, 0, 0], ![0, 0, 0, 139, 0], ![43, 55, 92, 29, 1]] where
  M :=![![![422359, -255571, 112661, -73492, 88089], ![-704712, 426433, -187980, 122636, -146984], ![940292, -568982, 250803, -163632, 196128], ![-432156, 261472, -115232, 75173, -90140], ![380062, -229944, 101366, -66088, 79247]]]
  hmulB := by decide  
  f := ![![![-157, -41, 33, 16, 35]], ![![-280, -197, -44, -20, 32]], ![![12, -142, -123, -56, -36]], ![![284, 28, -100, -49, -72]], ![![-91, -180, -111, -51, -16]]]
  g := ![![![-24212, -36694, -57493, -18907, 88089], ![40400, 61227, 95932, 31548, -146984], ![-53908, -81698, -128007, -42096, 196128], ![24776, 37548, 58832, 19347, -90140], ![-21781, -33011, -51722, -17009, 79247]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 4 2 7 [66, 66, 66, 105, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [59, 65, 79, 25], [5, 54, 41, 23], [109, 19, 19, 91], [0, 1]]
 g := ![![[136, 27, 48, 54], [67, 89, 10, 47], [51, 25, 1], [96, 59, 81, 125], [42, 66, 44], [1], []], ![[100, 39, 97, 6, 67, 79], [80, 26, 71, 28, 5, 42], [36, 107, 5], [114, 32, 44, 77, 90, 52], [126, 67, 51], [71, 22, 55], [76, 41, 69]], ![[12, 28, 108, 133, 112, 114], [136, 70, 14, 73, 11, 23], [31, 97, 13], [35, 84, 19, 49, 44, 76], [63, 93, 81], [13, 134, 66], [78, 134, 112]], ![[82, 30, 67, 81, 75, 41], [106, 73, 72, 67, 122, 16], [20, 128, 66], [22, 79, 136, 124, 41, 120], [3, 70, 52], [57, 36, 113], [91, 62, 80]]]
 h' := ![![[59, 65, 79, 25], [26, 133, 104, 101], [137, 15, 68, 66], [58, 23, 65, 1], [55, 55, 117, 60], [73, 73, 73, 34], [0, 0, 1], [0, 1]], ![[5, 54, 41, 23], [41, 19, 30, 9], [133, 36, 110, 92], [110, 14, 20, 127], [101, 92, 36, 67], [76, 46, 63, 32], [133, 87, 20, 65], [59, 65, 79, 25]], ![[109, 19, 19, 91], [114, 86, 82, 122], [122, 80, 66, 138], [120, 17, 28, 41], [25, 125, 93, 129], [98, 17, 32, 130], [20, 31, 12, 109], [5, 54, 41, 23]], ![[0, 1], [96, 40, 62, 46], [79, 8, 34, 121], [136, 85, 26, 109], [7, 6, 32, 22], [109, 3, 110, 82], [37, 21, 106, 104], [109, 19, 19, 91]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [115, 135, 25], []]
 b := ![[], [], [39, 123, 84, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 4
  hpos := by decide
  P := [66, 66, 66, 105, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-12786776, 2173363, 10366003, -497816, -7846111]
  a := ![-1, -5, -3, -1, 9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2335223, 3120212, 5267685, 1633377, -7846111]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 373301041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-157, -41, 33, 16, 35]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![-157, -41, 33, 16, 35]] 
 ![![139, 0, 0, 0, 0], ![81, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![47, 0, 0, 1, 0], ![23, 0, 0, 0, 1]] where
  M :=![![![-157, -41, 33, 16, 35], ![-280, -197, -44, -20, 32], ![12, -142, -123, -56, -36], ![284, 28, -100, -49, -72], ![162, -170, -212, -104, -89]]]
  hmulB := by decide  
  f := ![![![422359, -255571, 112661, -73492, 88089]], ![![241053, -145862, 64299, -41944, 50275]], ![![52343, -31673, 13962, -9108, 10917]], ![![139703, -84535, 37265, -24309, 29137]], ![![72621, -43943, 19371, -12636, 15146]]]
  g := ![![![8, -41, 33, 16, 35], ![119, -197, -44, -20, 32], ![121, -142, -123, -56, -36], ![25, 28, -100, -49, -72], ![173, -170, -212, -104, -89]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![422359, -255571, 112661, -73492, 88089]] ![![-157, -41, 33, 16, 35]]
  ![![139, 0, 0, 0, 0]] where
 M := ![![![139, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC139 : ContainsPrimesAboveP 139 ![I139N0, I139N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
    exact isPrimeI139N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 139 (by decide) (𝕀 ⊙ MulI139N0)
instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-175, 21, -21, -178, 83]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![-175, 21, -21, -178, 83]] 
 ![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![0, 0, 149, 0, 0], ![0, 0, 0, 149, 0], ![32, 20, 129, 93, 1]] where
  M :=![![![-175, 21, -21, -178, 83], ![-664, 181, 564, -30, -356], ![1756, -20, -427, 950, 148], ![-260, -386, -1104, -1035, 1128], ![-3550, 128, 1362, -1312, -679]]]
  hmulB := by decide  
  f := ![![![-7253, 4389, -1935, 1262, -1513]], ![![12104, -7323, 3228, -2106, 2524]], ![![-16148, 9772, -4307, 2810, -3368]], ![![7420, -4490, 1980, -1291, 1548]], ![![-9326, 5644, -2487, 1623, -1945]]]
  g := ![![![-19, -11, -72, -53, 83], ![72, 49, 312, 222, -356], ![-20, -20, -131, -86, 148], ![-244, -154, -984, -711, 1128], ![122, 92, 597, 415, -679]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 4 2 7 [37, 11, 59, 82, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [102, 127, 35, 116], [56, 101, 46, 22], [58, 69, 68, 11], [0, 1]]
 g := ![![[110, 38, 11, 124], [30, 83, 29], [11, 143, 27, 17], [93, 125, 110], [16, 48, 72, 19], [1], []], ![[117, 79, 34, 140, 87, 17], [74, 64, 24], [98, 115, 107, 118, 139, 113], [97, 90, 145], [9, 21, 109, 36, 12, 125], [90, 139, 6], [133, 27, 46]], ![[5, 55, 63, 61, 133, 119], [5, 97, 81], [58, 88, 77, 41, 146, 9], [18, 105, 133], [27, 143, 15, 140, 20, 64], [39, 4, 114], [32, 33, 37]], ![[93, 93, 2, 41, 26, 128], [84, 138, 148], [134, 18, 90, 7, 62, 109], [52, 61, 143], [71, 49, 120, 139, 111, 138], [90, 46, 30], [65, 67, 121]]]
 h' := ![![[102, 127, 35, 116], [43, 82, 121, 71], [40, 105, 82, 25], [2, 118, 60, 100], [4, 13, 105, 40], [112, 138, 90, 67], [0, 0, 1], [0, 1]], ![[56, 101, 46, 22], [60, 10, 0, 2], [50, 20, 142, 89], [75, 119, 73, 47], [45, 27, 64, 61], [103, 74, 34, 23], [119, 53, 13, 30], [102, 127, 35, 116]], ![[58, 69, 68, 11], [93, 24, 143, 133], [24, 64, 114, 140], [15, 131, 26, 129], [54, 108, 8, 27], [123, 0, 130, 103], [15, 54, 111, 73], [56, 101, 46, 22]], ![[0, 1], [38, 33, 34, 92], [49, 109, 109, 44], [117, 79, 139, 22], [113, 1, 121, 21], [1, 86, 44, 105], [65, 42, 24, 46], [58, 69, 68, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [125, 35, 66], []]
 b := ![[], [], [109, 61, 77, 146], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 4
  hpos := by decide
  P := [37, 11, 59, 82, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-90590560, 259071670, 967050969, 742451368, -954061110]
  a := ![3, -14, -7, -4, 34]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![204291040, 129800630, 832489491, 600470702, -954061110]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 492884401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7253, 4389, -1935, 1262, -1513]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![-7253, 4389, -1935, 1262, -1513]] 
 ![![149, 0, 0, 0, 0], ![112, 1, 0, 0, 0], ![79, 0, 1, 0, 0], ![139, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-7253, 4389, -1935, 1262, -1513], ![12104, -7323, 3228, -2106, 2524], ![-16148, 9772, -4307, 2810, -3368], ![7420, -4490, 1980, -1291, 1548], ![-6526, 3950, -1740, 1136, -1361]]]
  hmulB := by decide  
  f := ![![![-175, 21, -21, -178, 83]], ![![-136, 17, -12, -134, 60]], ![![-81, 11, -14, -88, 45]], ![![-165, 17, -27, -173, 85]], ![![-25, 1, 9, -10, -4]]]
  g := ![![![-3489, 4389, -1935, 1262, -1513], ![5822, -7323, 3228, -2106, 2524], ![-7769, 9772, -4307, 2810, -3368], ![3569, -4490, 1980, -1291, 1548], ![-3141, 3950, -1740, 1136, -1361]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![-175, 21, -21, -178, 83]] ![![-7253, 4389, -1935, 1262, -1513]]
  ![![149, 0, 0, 0, 0]] where
 M := ![![![149, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC149 : ContainsPrimesAboveP 149 ![I149N0, I149N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
    exact isPrimeI149N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 149 (by decide) (𝕀 ⊙ MulI149N0)
instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1461, 792, 1288, 616, 606]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![-1461, 792, 1288, 616, 606]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![0, 0, 151, 0, 0], ![0, 0, 0, 151, 0], ![100, 94, 40, 6, 1]] where
  M :=![![![-1461, 792, 1288, 616, 606], ![-4848, -613, 1564, 748, 1232], ![-2504, -2390, -911, -416, 132], ![1896, -2180, -2624, -1209, -1032], ![-2276, -4338, -2662, -1260, -361]]]
  hmulB := by decide  
  f := ![![![3405, -2060, 908, -592, 710]], ![![-5680, 3437, -1516, 988, -1184]], ![![7576, -4586, 2023, -1320, 1580]], ![![-3480, 2108, -928, 609, -728]], ![![608, -368, 162, -106, 127]]]
  g := ![![![-411, -372, -152, -20, 606], ![-848, -771, -316, -44, 1232], ![-104, -98, -41, -8, 132], ![696, 628, 256, 33, -1032], ![224, 196, 78, 6, -361]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 4 2 7 [137, 72, 44, 25, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [132, 81, 16, 135], [30, 149, 128, 66], [115, 71, 7, 101], [0, 1]]
 g := ![![[31, 65, 139, 4], [16, 99, 146, 32], [10, 70, 7, 121], [2, 65, 58], [91, 34, 14, 21], [1], []], ![[38, 99, 122, 92, 72, 129], [67, 16, 123, 42, 42, 70], [80, 11, 115, 83, 61, 101], [75, 81, 125], [3, 16, 104, 70, 45, 70], [29, 122, 127], [46, 34, 105]], ![[72, 42, 141, 39, 139, 132], [119, 48, 89, 74, 75, 71], [35, 142, 27, 142, 109, 46], [24, 22, 5], [96, 108, 112, 46, 45, 13], [136, 88, 17], [137, 106, 128]], ![[102, 83, 24, 27, 72, 92], [35, 48, 6, 87, 114, 82], [95, 49, 122, 149, 97, 26], [18, 34, 137], [57, 47, 54, 92, 83, 132], [119, 71, 21], [61, 69, 84]]]
 h' := ![![[132, 81, 16, 135], [73, 53, 22, 2], [140, 134, 115, 33], [5, 142, 28, 11], [66, 9, 33, 71], [14, 79, 107, 126], [0, 0, 1], [0, 1]], ![[30, 149, 128, 66], [111, 40, 93, 71], [24, 107, 79, 40], [114, 24, 82, 133], [11, 44, 114, 124], [90, 106, 123, 40], [99, 126, 82, 91], [132, 81, 16, 135]], ![[115, 71, 7, 101], [122, 149, 94, 105], [64, 129, 45, 125], [4, 1, 90, 64], [11, 44, 129, 55], [126, 5, 13, 68], [100, 107, 44, 35], [30, 149, 128, 66]], ![[0, 1], [40, 60, 93, 124], [36, 83, 63, 104], [121, 135, 102, 94], [41, 54, 26, 52], [93, 112, 59, 68], [36, 69, 24, 25], [115, 71, 7, 101]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [109, 138, 24], []]
 b := ![[], [], [66, 51, 54, 82], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 4
  hpos := by decide
  P := [137, 72, 44, 25, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-35578859, 17714591, 72756627, 35531394, -66942245]
  a := ![1, -7, -5, -1, 17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![44096991, 41789971, 18214877, 2895264, -66942245]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 519885601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3405, -2060, 908, -592, 710]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![3405, -2060, 908, -592, 710]] 
 ![![151, 0, 0, 0, 0], ![139, 1, 0, 0, 0], ![85, 0, 1, 0, 0], ![63, 0, 0, 1, 0], ![105, 0, 0, 0, 1]] where
  M :=![![![3405, -2060, 908, -592, 710], ![-5680, 3437, -1516, 988, -1184], ![7576, -4586, 2023, -1320, 1580], ![-3480, 2108, -928, 609, -728], ![3068, -1854, 814, -532, 641]]]
  hmulB := by decide  
  f := ![![![-1461, 792, 1288, 616, 606]], ![![-1377, 725, 1196, 572, 566]], ![![-839, 430, 719, 344, 342]], ![![-597, 316, 520, 249, 246]], ![![-1031, 522, 878, 420, 419]]]
  g := ![![![1161, -2060, 908, -592, 710], ![-1937, 3437, -1516, 988, -1184], ![2585, -4586, 2023, -1320, 1580], ![-1189, 2108, -928, 609, -728], ![1045, -1854, 814, -532, 641]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![-1461, 792, 1288, 616, 606]] ![![3405, -2060, 908, -592, 710]]
  ![![151, 0, 0, 0, 0]] where
 M := ![![![151, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC151 : ContainsPrimesAboveP 151 ![I151N0, I151N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
    exact isPrimeI151N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 151 (by decide) (𝕀 ⊙ MulI151N0)


lemma PB324I3_primes (p : ℕ) :
  p ∈ Set.range ![107, 109, 113, 127, 131, 137, 139, 149, 151] ↔ Nat.Prime p ∧ 103 < p ∧ p ≤ 151 := by
  rw [← List.mem_ofFn']
  convert primes_range 103 151 (by omega)

def PB324I3 : PrimesBelowBoundCertificateInterval O 103 151 324 where
  m := 9
  g := ![3, 3, 2, 2, 1, 2, 2, 2, 2]
  P := ![107, 109, 113, 127, 131, 137, 139, 149, 151]
  hP := PB324I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I107N0, I107N1, I107N2]
    · exact ![I109N0, I109N1, I109N2]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1]
    · exact ![I131N0]
    · exact ![I137N0, I137N1]
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC107
    · exact PBC109
    · exact PBC113
    · exact PBC127
    · exact PBC131
    · exact PBC137
    · exact PBC139
    · exact PBC149
    · exact PBC151
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![1225043, 107, 107]
    · exact ![1295029, 109, 109]
    · exact ![163047361, 113]
    · exact ![2048383, 16129]
    · exact ![38579489651]
    · exact ![352275361, 137]
    · exact ![373301041, 139]
    · exact ![492884401, 149]
    · exact ![519885601, 151]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
      exact NI107N2
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
      exact NI109N2
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
      exact NI139N1
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
  β := ![I107N1, I107N2, I109N1, I109N2, I113N1, I137N1, I139N1, I149N1, I151N1]
  Il := ![[I107N1, I107N2], [I109N1, I109N2], [I113N1], [], [], [I137N1], [I139N1], [I149N1], [I151N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
