
import IdealArithmetic.Examples.NF5_5_10125000000_1.RI5_5_10125000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, -1, -3, 0, 2]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![3, -1, -3, 0, 2]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![3, -1, -3, 0, 2], ![-60, 57, 78, 32, 0], ![62, 9, -14, 46, 64], ![-884, 928, 1204, 555, 92], ![-604, 1216, 1402, 1062, 609]]]
  hmulB := by decide  
  f := ![![![4900, 4913, 1763, -62, -192]], ![![2818, 3004, 1135, -30, -124]], ![![2871, 2635, 868, -44, -94]], ![![-1452, -1180, -336, 27, 36]], ![![-1634, -1915, -775, 12, 85]]]
  g := ![![![3, -1, -3, 0, 2], ![-69, 57, 78, 32, 0], ![38, 9, -14, 46, 64], ![-1044, 928, 1204, 555, 92], ![-1003, 1216, 1402, 1062, 609]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![30, -3, -9, -1, 1]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![30, -3, -9, -1, 1]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![30, -3, -9, -1, 1], ![-32, 47, 36, 2, -4], ![78, -56, -53, -4, 6], ![-78, 48, 50, 5, -6], ![52, -53, -48, -5, 6]]]
  hmulB := by decide  
  f := ![![![-12, 9, 10, 1, -1]], ![![16, -11, -12, 0, 2]], ![![-38, 31, 35, 7, -1]], ![![14, 5, 10, 22, 13]], ![![-99, 116, 139, 70, 25]]]
  g := ![![![15, -3, -9, -1, 1], ![-16, 47, 36, 2, -4], ![39, -56, -53, -4, 6], ![-39, 48, 50, 5, -6], ![26, -53, -48, -5, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-107, 80, 74, 5, -8]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![-107, 80, 74, 5, -8]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-107, 80, 74, 5, -8], ![250, -185, -170, -9, 20], ![-434, 330, 309, 29, -28], ![324, -211, -174, 33, 48], ![-426, 405, 432, 153, 35]]]
  hmulB := by decide  
  f := ![![![236, -151, -176, -15, 20]], ![![-197, 169, 176, 14, -20]], ![![747, -536, -597, -50, 68]], ![![-637, 473, 522, 45, -60]], ![![618, -462, -510, -45, 59]]]
  g := ![![![-133, 80, 74, 5, -8], ![307, -185, -170, -9, 20], ![-551, 330, 309, 29, -28], ![338, -211, -174, 33, 48], ![-708, 405, 432, 153, 35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![3, -1, -3, 0, 2]] ![![30, -3, -9, -1, 1]]
  ![![-8, 6, 0, -3, 1]] where
 M := ![![![-8, 6, 0, -3, 1]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![-8, 6, 0, -3, 1]] ![![30, -3, -9, -1, 1]]
  ![![-146, 109, 90, 0, -8]] where
 M := ![![![-146, 109, 90, 0, -8]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![-146, 109, 90, 0, -8]] ![![-107, 80, 74, 5, -8]]
  ![![7220, -5385, -4980, -325, 548]] where
 M := ![![![7220, -5385, -4980, -325, 548]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![7220, -5385, -4980, -325, 548]] ![![-107, 80, 74, 5, -8]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![-296218, 220940, 204196, 13264, -22440]]]
 hmul := by decide  
 g := ![![![![-148109, 110470, 102098, 6632, -11220]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-665, 488, 538, 44, -61]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![-665, 488, 538, 44, -61]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![-665, 488, 538, 44, -61], ![1918, -1408, -1552, -127, 176], ![-3726, 2735, 3015, 247, -342], ![4418, -3243, -3576, -294, 406], ![-3618, 2656, 2930, 242, -333]]]
  hmulB := by decide  
  f := ![![![-1, -14, -8, 0, 1]], ![![-10, 2, 4, 1, 0]], ![![6, -3, -1, 3, 2]], ![![-22, 29, 32, 16, 6]], ![![-40, 52, 70, 46, 19]]]
  g := ![![![-181, 488, 538, 44, -61], ![522, -1408, -1552, -127, 176], ![-1014, 2735, 3015, 247, -342], ![1202, -3243, -3576, -294, 406], ![-984, 2656, 2930, 242, -333]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3111, -2327, -2148, -139, 236]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![3111, -2327, -2148, -139, 236]] 
 ![![3, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![3111, -2327, -2148, -139, 236], ![-7358, 5480, 5064, 327, -556], ![12346, -9209, -8499, -545, 932], ![-10846, 8093, 7444, 464, -812], ![8228, -6132, -5620, -338, 609]]]
  hmulB := by decide  
  f := ![![![245, -327, -400, -233, -92]], ![![928, -1268, -1556, -927, -372]], ![![3506, -4767, -5847, -3469, -1388]], ![![17132, -23373, -28680, -17068, -6844]], ![![48368, -65942, -80908, -48120, -19287]]]
  g := ![![![2681, -2327, -2148, -139, 236], ![-6324, 5480, 5064, 327, -556], ![10618, -9209, -8499, -545, 932], ![-9320, 8093, 7444, 464, -812], ![7056, -6132, -5620, -338, 609]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![-665, 488, 538, 44, -61]] ![![-665, 488, 538, 44, -61]]
  ![![-211289, 155098, 170850, 13952, -19366]] where
 M := ![![![-211289, 155098, 170850, 13952, -19366]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![-211289, 155098, 170850, 13952, -19366]] ![![3111, -2327, -2148, -139, 236]]
  ![![116097, -85259, -93498, -7597, 10590]] where
 M := ![![![116097, -85259, -93498, -7597, 10590]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![116097, -85259, -93498, -7597, 10590]] ![![3111, -2327, -2148, -139, 236]]
  ![![3718763, -2774358, -2556298, -165194, 280834]] where
 M := ![![![3718763, -2774358, -2556298, -165194, 280834]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N3 : IdealMulLeCertificate' Table 
  ![![3718763, -2774358, -2556298, -165194, 280834]] ![![3111, -2327, -2148, -139, 236]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![4525139025, -3375084189, -3119266350, -202512621, 342866814]]]
 hmul := by decide  
 g := ![![![![1508379675, -1125028063, -1039755450, -67504207, 114288938]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9481, -12916, -15846, -9418, -3773]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![9481, -12916, -15846, -9418, -3773]] 
 ![![5, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![9481, -12916, -15846, -9418, -3773], ![94354, -128698, -157916, -93961, -37672], ![423942, -578025, -709219, -421839, -169086], ![2067274, -2819049, -3458948, -2057636, -824842], ![5881546, -8020102, -9840550, -5853684, -2346503]]]
  hmulB := by decide  
  f := ![![![-21417, 16010, 14868, 1010, -1649]], ![![10298, -7672, -7192, -521, 808]], ![![-17790, 13269, 12605, 1005, -1446]], ![![17546, -13089, -13060, -1374, 1606]], ![![-27949, 20860, 20674, 2106, -2520]]]
  g := ![![![4160, -12916, -15846, -9418, -3773], ![41474, -128698, -157916, -93961, -37672], ![186240, -578025, -709219, -421839, -169086], ![908360, -2819049, -3458948, -2057636, -824842], ![2584211, -8020102, -9840550, -5853684, -2346503]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![9481, -12916, -15846, -9418, -3773]] ![![9481, -12916, -15846, -9418, -3773]]
  ![![-49507231425, 67508839250, 82832458818, 49273534592, 19751854270]] where
 M := ![![![-49507231425, 67508839250, 82832458818, 49273534592, 19751854270]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![-49507231425, 67508839250, 82832458818, 49273534592, 19751854270]] ![![9481, -12916, -15846, -9418, -3773]]
  ![![259049845638118259, -353244443553564198, -433426291346863308, -257827012468910094, -103352877459812097]] where
 M := ![![![259049845638118259, -353244443553564198, -433426291346863308, -257827012468910094, -103352877459812097]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![259049845638118259, -353244443553564198, -433426291346863308, -257827012468910094, -103352877459812097]] ![![9481, -12916, -15846, -9418, -3773]]
  ![![-1355495365833631567170367, 1848374798540627783682160, 2267931594029419633350168, 1349096810798927124221560, 540800733145595184374276]] where
 M := ![![![-1355495365833631567170367, 1848374798540627783682160, 2267931594029419633350168, 1349096810798927124221560, 540800733145595184374276]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![-1355495365833631567170367, 1848374798540627783682160, 2267931594029419633350168, 1349096810798927124221560, 540800733145595184374276]] ![![9481, -12916, -15846, -9418, -3773]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![7092718709291137997288727935505, -9671742778204688752750149218300, -11867101322380507084285741352550, -7059237848971732547219253703250, -2829775427244737870005538793625]]]
 hmul := by decide  
 g := ![![![![1418543741858227599457745587101, -1934348555640937750550029843660, -2373420264476101416857148270510, -1411847569794346509443850740650, -565955085448947574001107758725]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-89, 65, 66, 1, -6]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![-89, 65, 66, 1, -6]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![1, 4, 1, 0, 0], ![3, 1, 0, 1, 0], ![3, 3, 0, 0, 1]] where
  M :=![![![-89, 65, 66, 1, -6], ![182, -132, -112, 17, 4], ![-134, 93, -13, -91, 32], ![-662, 503, 880, 328, -184], ![1356, -1014, -1572, -480, 301]]]
  hmulB := by decide  
  f := ![![![-2775, 2005, 1874, 123, -206]], ![![6426, -4870, -4476, -289, 492]], ![![1721, -1338, -1219, -78, 134]], ![![1105, -858, -782, -50, 86]], ![![519, -441, -390, -24, 43]]]
  g := ![![![-20, -26, 66, 1, -6], ![33, 41, -112, 17, 4], ![8, 20, -13, -91, 32], ![-282, -399, 880, 328, -184], ![495, 693, -1572, -480, 301]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [3, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 6], [0, 1]]
 g := ![![[2, 4], [1, 1]], ![[6, 3], [2, 6]]]
 h' := ![![[1, 6], [4, 5], [0, 1]], ![[0, 1], [2, 2], [1, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [5, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 2
  hpos := by decide
  P := [3, 6, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-785088, 1677168, 1909787, 1484176, 887748]
  a := ![-25, -17, 5, -1, -50]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1401521, -1444200, 1909787, 1484176, 887748]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2775, 2005, 1874, 123, -206]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![-2775, 2005, 1874, 123, -206]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![4, 6, 4, 1, 0], ![4, 0, 6, 0, 1]] where
  M :=![![![-2775, 2005, 1874, 123, -206], ![6426, -4870, -4476, -289, 492], ![-10882, 8109, 7497, 487, -824], ![9634, -7151, -6620, -430, 728], ![-7320, 5508, 5076, 330, -557]]]
  hmulB := by decide  
  f := ![![![-89, 65, 66, 1, -6]], ![![182, -132, -112, 17, 4]], ![![-134, 93, -13, -91, 32]], ![![-66, 49, 60, 10, -8]], ![![28, -28, -198, -146, 67]]]
  g := ![![![-349, 181, 374, 123, -206], ![802, -448, -896, -289, 492], ![-1362, 741, 1499, 487, -824], ![1206, -653, -1324, -430, 728], ![-916, 504, 1014, 330, -557]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P1 : CertificateIrreducibleZModOfList' 7 3 2 2 [3, 6, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 1, 5], [4, 5, 2], [0, 1]]
 g := ![![[4, 4, 1], [1]], ![[4, 3], [3, 4, 6, 6]], ![[3, 3, 1, 2], [1, 0, 3, 1]]]
 h' := ![![[2, 1, 5], [4, 1, 6], [0, 1]], ![[4, 5, 2], [6, 3], [2, 1, 5]], ![[0, 1], [5, 3, 1], [4, 5, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2], []]
 b := ![[], [1, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N1 : CertifiedPrimeIdeal' SI7N1 7 where
  n := 3
  hpos := by decide
  P := [3, 6, 1, 1]
  hirr := P7P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![195006450449, -275813236961, -336202703988, -205741419307, -87074377241]
  a := ![-37, -48, -6, -1, -77]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![195181376663, 136947896983, 144172748098, -205741419307, -87074377241]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N1 B_one_repr
lemma NI7N1 : Nat.card (O ⧸ I7N1) = 343 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![-89, 65, 66, 1, -6]] ![![-2775, 2005, 1874, 123, -206]]
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


def P11P0 : CertificateIrreducibleZModOfList' 11 5 2 3 [5, 3, 9, 9, 8, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 4, 4, 4, 8], [3, 7, 4, 5, 7], [4, 4, 6, 5, 7], [9, 6, 8, 8], [0, 1]]
 g := ![![[7, 0, 8, 6, 9], [1], []], ![[4, 10, 10, 3, 2, 2, 5, 10], [1, 6, 9, 1, 10, 1, 7, 6], [1, 8, 3, 9]], ![[1, 4, 3, 9, 1, 0, 9, 6], [5, 7, 1, 3, 5, 2, 4, 10], [3, 5, 8, 5]], ![[0, 3, 0, 9, 0, 8], [0, 0, 2, 0, 6, 0, 3, 6], [10, 0, 8, 5]], ![[4, 1, 6, 0, 6, 0, 6], [2, 10, 3, 10, 8, 7, 2], [1, 9]]]
 h' := ![![[9, 4, 4, 4, 8], [6, 8, 2, 2, 3], [0, 0, 1], [0, 1]], ![[3, 7, 4, 5, 7], [4, 10, 4, 3, 9], [10, 7, 7, 2, 3], [9, 4, 4, 4, 8]], ![[4, 4, 6, 5, 7], [6, 2, 5, 8, 2], [5, 8, 2, 9, 5], [3, 7, 4, 5, 7]], ![[9, 6, 8, 8], [4, 10, 7, 3], [10, 2, 0, 4, 9], [4, 4, 6, 5, 7]], ![[0, 1], [10, 3, 4, 6, 8], [10, 5, 1, 7, 5], [9, 6, 8, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 7, 9, 2], [], [], []]
 b := ![[], [9, 7, 6, 8, 8], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 5
  hpos := by decide
  P := [5, 3, 9, 9, 8, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![267620179294604785, -365075480312752803, -447910725215351486, -266527101876918619, -106907324698663093]
  a := ![-8, -7, 1, -1, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![24329107208600435, -33188680028432073, -40719156837759226, -24229736534265329, -9718847699878463]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3257, -5473, -2612, -19, 288]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-3257, -5473, -2612, -19, 288]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![3, 0, 7, 10, 1]] where
  M :=![![![-3257, -5473, -2612, -19, 288], ![-8678, -2990, 612, 267, -76], ![5746, -5135, -5083, -377, 572], ![-4618, 7553, 6376, 406, -716], ![8920, -806, -3228, -392, 369]]]
  hmulB := by decide  
  f := ![![![107, -143, -176, -103, -40]], ![![994, -1372, -1680, -1009, -412]], ![![4674, -6317, -7763, -4585, -1812]], ![![22098, -30291, -37132, -22180, -8964]], ![![24459, -33426, -40997, -24430, -9827]]]
  g := ![![![-317, -421, -356, -223, 288], ![-650, -230, 88, 79, -76], ![310, -395, -699, -469, 572], ![-190, 581, 876, 582, -716], ![601, -62, -447, -314, 369]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 4 2 3 [9, 10, 10, 2, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 10, 1, 9], [0, 6, 9, 7], [0, 9, 3, 10], [0, 1]]
 g := ![![[6, 10, 11, 3], [7, 11, 1], []], ![[11, 11, 12, 5, 12, 9], [12, 12, 9], [5, 7, 10, 2, 7, 1]], ![[0, 6, 7, 10, 0, 2], [6, 5, 1], [7, 5, 0, 11, 0, 5]], ![[0, 9, 4, 4, 6, 3], [8, 1, 1], [2, 6, 9, 6, 5, 12]]]
 h' := ![![[11, 10, 1, 9], [2, 0, 6, 9], [0, 0, 0, 1], [0, 1]], ![[0, 6, 9, 7], [10, 5, 11, 1], [12, 7, 8, 10], [11, 10, 1, 9]], ![[0, 9, 3, 10], [2, 7, 3, 11], [2, 2, 10, 1], [0, 6, 9, 7]], ![[0, 1], [5, 1, 6, 5], [8, 4, 8, 1], [0, 9, 3, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [3, 5], []]
 b := ![[], [], [11, 11, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 4
  hpos := by decide
  P := [9, 10, 10, 2, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-29826906734669663, 40861375414626858, 50094359193021328, 29908810887986714, 12076860206392546]
  a := ![52, 39, -8, -1, 103]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5081345181065177, 3143182724202066, -2649512480902038, -6989214705841442, 12076860206392546]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 28561 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2087, 2238, 1848, 106, -203]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![-2087, 2238, 1848, 106, -203]] 
 ![![13, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![-2087, 2238, 1848, 106, -203], ![6302, -3888, -3856, -267, 424], ![-9778, 7371, 6787, 439, -746], ![8478, -6683, -6060, -386, 666], ![-6914, 4658, 4466, 300, -491]]]
  hmulB := by decide  
  f := ![![![11263, -8268, -9110, -746, 1033]], ![![7898, -5798, -6388, -523, 724]], ![![4858, -3567, -3933, -325, 446]], ![![299, -223, -238, -18, 21]], ![![8226, -6050, -6682, -572, 751]]]
  g := ![![![-2221, 2238, 1848, 106, -203], ![4087, -3888, -3856, -267, 424], ![-7563, 7371, 6787, 439, -746], ![6824, -6683, -6060, -386, 666], ![-4842, 4658, 4466, 300, -491]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-3257, -5473, -2612, -19, 288]] ![![-2087, 2238, 1848, 106, -203]]
  ![![13, 0, 0, 0, 0]] where
 M := ![![![-4305665, -3794713, -1241344, 63115, 135109]]]
 hmul := by decide  
 g := ![![![![-331205, -291901, -95488, 4855, 10393]]]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2727, 3746, 4606, 2756, 1109]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![-2727, 3746, 4606, 2756, 1109]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![11, 10, 4, 9, 1]] where
  M :=![![![-2727, 3746, 4606, 2756, 1109], ![-27758, 37786, 46340, 27527, 11024], ![-123954, 169139, 207569, 123541, 49542], ![-605710, 825843, 1013268, 602684, 241570], ![-1722474, 2348890, 2882078, 1714484, 687293]]]
  hmulB := by decide  
  f := ![![![-13413, 9920, 10896, 888, -1235]], ![![38826, -28412, -31336, -2561, 3552]], ![![-75254, 55249, 60857, 4969, -6898]], ![![89026, -65389, -72012, -5878, 8162]], ![![39301, -28771, -31726, -2592, 3596]]]
  g := ![![![-878, -432, 10, -425, 1109], ![-8766, -4262, 132, -4217, 11024], ![-39348, -19193, 553, -18961, 49542], ![-191940, -93521, 2764, -92438, 241570], ![-546041, -266120, 7818, -263009, 687293]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 4 2 4 [16, 0, 7, 8, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 16, 9, 10], [10, 0, 13, 13], [12, 0, 12, 11], [0, 1]]
 g := ![![[4, 7, 0, 2], [13, 8, 13], [1], []], ![[14, 0, 9, 15, 5, 3], [15, 11, 9], [3, 14, 13], [3, 9, 15]], ![[5, 3, 1, 2, 1, 16], [13, 9, 15], [7, 9, 15], [9, 6, 16]], ![[14, 3, 10, 5, 14, 14], [10, 10, 1], [15, 4, 4], [16, 10, 2]]]
 h' := ![![[4, 16, 9, 10], [14, 8, 10, 11], [1, 0, 10, 9], [0, 0, 1], [0, 1]], ![[10, 0, 13, 13], [13, 8, 6, 11], [7, 1, 6, 14], [2, 1, 16, 9], [4, 16, 9, 10]], ![[12, 0, 12, 11], [4, 4, 10, 9], [5, 8, 9, 10], [7, 6, 9, 10], [10, 0, 13, 13]], ![[0, 1], [9, 14, 8, 3], [13, 8, 9, 1], [7, 10, 8, 15], [12, 0, 12, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [13, 6, 13], []]
 b := ![[], [], [15, 14, 3, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 4
  hpos := by decide
  P := [16, 0, 7, 8, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5693837102814038, 7802705364794358, 9565256394990710, 5712339427027768, 2307700934953126]
  a := ![-35, -20, 10, 2, -69]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1828149846311672, -898488469690406, 19673685598718, -885704058091198, 2307700934953126]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 83521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13413, -9920, -10896, -888, 1235]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![13413, -9920, -10896, -888, 1235]] 
 ![![17, 0, 0, 0, 0], ![15, 1, 0, 0, 0], ![16, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![13413, -9920, -10896, -888, 1235], ![-38826, 28412, 31336, 2561, -3552], ![75254, -55249, -60857, -4969, 6898], ![-89026, 65389, 72012, 5878, -8162], ![72818, -53398, -58842, -4804, 6669]]]
  hmulB := by decide  
  f := ![![![2727, -3746, -4606, -2756, -1109]], ![![4039, -5528, -6790, -4051, -1627]], ![![9858, -13475, -16545, -9861, -3958]], ![![35630, -48579, -59604, -35452, -14210]], ![![101322, -138170, -169534, -100852, -40429]]]
  g := ![![![19797, -9920, -10896, -888, 1235], ![-56846, 28412, 31336, 2561, -3552], ![110453, -55249, -60857, -4969, 6898], ![-130709, 65389, 72012, 5878, -8162], ![106780, -53398, -58842, -4804, 6669]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![-2727, 3746, 4606, 2756, 1109]] ![![13413, -9920, -10896, -888, 1235]]
  ![![17, 0, 0, 0, 0]] where
 M := ![![![-17, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 17 (by decide) (𝕀 ⊙ MulI17N0)
instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![285, 204, 18, -20, 2]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![285, 204, 18, -20, 2]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![8, 5, 2, 1, 0], ![4, 0, 10, 0, 1]] where
  M :=![![![285, 204, 18, -20, 2], ![-100, 565, 528, 94, -80], ![1344, -946, -1393, -326, 228], ![-3696, 2526, 3676, 889, -612], ![4640, -3754, -5088, -1222, 849]]]
  hmulB := by decide  
  f := ![![![-6081, 8292, 10174, 6052, 2426]], ![![-60676, 82739, 101520, 60390, 24208]], ![![-272392, 371438, 455749, 271106, 108676]], ![![-117132, 159723, 195978, 116579, 46732]], ![![-343588, 468522, 574870, 341966, 137081]]]
  g := ![![![23, 16, 2, -20, 2], ![-28, 5, 60, 94, -80], ![160, 36, -159, -326, 228], ![-440, -101, 422, 889, -612], ![580, 124, -586, -1222, 849]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 3 2 4 [17, 11, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 18, 6], [7, 0, 13], [0, 1]]
 g := ![![[3, 6, 17], [9, 11, 17], [13, 1], []], ![[14, 0, 8, 16], [16, 9, 1, 11], [], [0, 17]], ![[4, 14, 18, 3], [7, 13, 15, 18], [0, 1], [12, 17]]]
 h' := ![![[6, 18, 6], [18, 10, 13], [7, 11, 6], [0, 0, 1], [0, 1]], ![[7, 0, 13], [14, 10, 3], [4, 7, 9], [17, 3], [6, 18, 6]], ![[0, 1], [11, 18, 3], [9, 1, 4], [16, 16, 18], [7, 0, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 12], []]
 b := ![[], [18, 18, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 3
  hpos := by decide
  P := [17, 11, 6, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-357658983, 734832338, 845813326, 646497930, 374416400]
  a := ![8, -2, -6, -10, 16]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-369858317, -131455648, -220597186, 646497930, 374416400]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 6859 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-61, 58, 62, 22, 5]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![-61, 58, 62, 22, 5]] 
 ![![19, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![18, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-61, 58, 62, 22, 5], ![-106, 204, 272, 197, 88], ![-1070, 1359, 1631, 911, 350], ![-4286, 5933, 7312, 4402, 1778], ![-12710, 17264, 21158, 12546, 5019]]]
  hmulB := by decide  
  f := ![![![-829, -40, 228, 30, -25]], ![![-1, -74, -48, -1, 5]], ![![-904, 45, 303, 31, -32]], ![![106, -59, -56, 8, 2]], ![![-22, 40, 10, -18, 5]]]
  g := ![![![-65, 58, 62, 22, 5], ![-274, 204, 272, 197, 88], ![-1673, 1359, 1631, 911, 350], ![-7465, 5933, 7312, 4402, 1778], ![-21622, 17264, 21158, 12546, 5019]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1

def I19N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, 6, 6, 0, -1]] i)))

def SI19N2: IdealEqSpanCertificate' Table ![![-7, 6, 6, 0, -1]] 
 ![![19, 0, 0, 0, 0], ![15, 1, 0, 0, 0], ![13, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![-7, 6, 6, 0, -1], ![30, -24, -28, -7, 0], ![-22, 1, -3, -21, -14], ![174, -203, -244, -122, -42], ![290, -426, -526, -332, -139]]]
  hmulB := by decide  
  f := ![![![-2031, 1524, 1408, 92, -155]], ![![-1349, 1014, 936, 61, -103]], ![![-1819, 1363, 1261, 83, -139]], ![![-575, 433, 396, 24, -43]], ![![-730, 546, 510, 36, -57]]]
  g := ![![![-9, 6, 6, 0, -1], ![43, -24, -28, -7, 0], ![13, 1, -3, -21, -14], ![403, -203, -244, -122, -42], ![898, -426, -526, -332, -139]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N2 : Nat.card (O ⧸ I19N2) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N2)

lemma isPrimeI19N2 : Ideal.IsPrime I19N2 := prime_ideal_of_norm_prime hp19.out _ NI19N2
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![285, 204, 18, -20, 2]] ![![-61, 58, 62, 22, 5]]
  ![![2031, -1524, -1408, -92, 155]] where
 M := ![![![2031, -1524, -1408, -92, 155]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI19N1 : IdealMulLeCertificate' Table 
  ![![2031, -1524, -1408, -92, 155]] ![![-7, 6, 6, 0, -1]]
  ![![19, 0, 0, 0, 0]] where
 M := ![![![-19, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-21331, 15659, 17240, 1407, -1954]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![-21331, 15659, 17240, 1407, -1954]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![13, 19, 13, 4, 1]] where
  M :=![![![-21331, 15659, 17240, 1407, -1954], ![61434, -45098, -49656, -4053, 5628], ![-119190, 87495, 96343, 7863, -10920], ![140946, -103467, -113940, -9302, 12912], ![-115184, 84548, 93104, 7590, -10557]]]
  hmulB := by decide  
  f := ![![![243, 251, 92, -3, -10]], ![![294, 296, 108, -3, -12]], ![![30, 27, 5, -3, 0]], ![![-150, -117, -24, 8, 0]], ![![365, 372, 135, -5, -15]]]
  g := ![![![177, 2295, 1854, 401, -1954], ![-510, -6610, -5340, -1155, 5628], ![990, 12825, 10361, 2241, -10920], ![-1170, -15165, -12252, -2650, 12912], ![959, 12397, 10015, 2166, -10557]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 4 2 4 [18, 5, 15, 9, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 13, 13, 13], [17, 4, 8, 21], [0, 5, 2, 12], [0, 1]]
 g := ![![[4, 18, 18, 4], [11, 18, 13, 9], [14, 1], []], ![[0, 21, 20, 10, 6, 12], [18, 3, 20, 13, 10, 13], [16, 0, 10, 17, 7, 12], [17, 13, 8]], ![[22, 2, 8, 20, 7, 20], [9, 0, 11, 1, 14, 20], [9, 15, 13, 6, 1, 11], [2, 1, 4]], ![[0, 6, 4, 19, 8, 18], [21, 11, 0, 18, 0, 4], [19, 22, 7, 11, 16, 12], [19, 17, 6]]]
 h' := ![![[20, 13, 13, 13], [9, 13, 2, 2], [1, 4, 15, 20], [0, 0, 1], [0, 1]], ![[17, 4, 8, 21], [18, 18, 8, 10], [22, 21, 8, 22], [2, 17, 18, 10], [20, 13, 13, 13]], ![[0, 5, 2, 12], [16, 20, 14, 17], [22, 7, 21, 17], [0, 16, 20, 12], [17, 4, 8, 21]], ![[0, 1], [13, 18, 22, 17], [3, 14, 2, 10], [3, 13, 7, 1], [0, 5, 2, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [10, 0, 19], []]
 b := ![[], [], [3, 6, 20, 21], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 4
  hpos := by decide
  P := [18, 5, 15, 9, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1407258882336, 1932845792775, 2368488127152, 1416982259661, 574450060191]
  a := ![4, 1, -2, -1, 9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-385874333253, -390508928298, -221711419797, -38296433961, 574450060191]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 279841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![243, 251, 92, -3, -10]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![243, 251, 92, -3, -10]] 
 ![![23, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![18, 0, 1, 0, 0], ![14, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![243, 251, 92, -3, -10], ![294, 296, 108, -3, -12], ![30, 27, 5, -3, 0], ![-150, -117, -24, 8, 0], ![-140, -214, -112, -12, 13]]]
  hmulB := by decide  
  f := ![![![-21331, 15659, 17240, 1407, -1954]], ![![-3821, 2805, 3088, 252, -350]], ![![-21876, 16059, 17681, 1443, -2004]], ![![-6856, 5033, 5540, 452, -628]], ![![-5008, 3676, 4048, 330, -459]]]
  g := ![![![-136, 251, 92, -3, -10], ![-160, 296, 108, -3, -12], ![-9, 27, 5, -3, 0], ![43, -117, -24, 8, 0], ![154, -214, -112, -12, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![-21331, 15659, 17240, 1407, -1954]] ![![243, 251, 92, -3, -10]]
  ![![23, 0, 0, 0, 0]] where
 M := ![![![23, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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


lemma PB3864I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB3864I0 : PrimesBelowBoundCertificateInterval O 1 23 3864 where
  m := 9
  g := ![5, 5, 5, 2, 1, 2, 2, 3, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB3864I0_primes
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
    · exact ![I17N0, I17N1]
    · exact ![I19N0, I19N1, I19N2]
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
    · exact ![3, 3, 3, 3, 3]
    · exact ![5, 5, 5, 5, 5]
    · exact ![49, 343]
    · exact ![161051]
    · exact ![28561, 13]
    · exact ![83521, 17]
    · exact ![6859, 19, 19]
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
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
      exact NI19N2
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I5N0, I7N0, I7N1, I13N1, I17N1, I19N1, I19N2, I23N1]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N0, I3N1, I3N1, I3N1], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N0, I7N1], [], [I13N1], [I17N1], [I19N1, I19N2], [I23N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
