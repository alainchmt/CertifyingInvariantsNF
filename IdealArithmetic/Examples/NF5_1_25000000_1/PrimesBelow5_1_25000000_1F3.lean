
import IdealArithmetic.Examples.NF5_1_25000000_1.RI5_1_25000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0, 0, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0, 0, 0]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![0, 0, 107, 0, 0], ![0, 0, 0, 107, 0], ![0, 0, 0, 0, 107]] where
  M :=![![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![0, 0, 107, 0, 0], ![0, 0, 0, 107, 0], ![0, 0, 0, 0, 107]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 5 2 6 [63, 28, 77, 20, 40, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [26, 81, 105, 67, 106], [22, 106, 34, 101, 80], [100, 27, 24, 38, 55], [26, 106, 51, 8, 80], [0, 1]]
 g := ![![[93, 43, 41, 24, 44], [82, 53, 41, 25, 62], [35, 95, 85, 85], [15, 42, 15, 54, 90], [67, 1], []], ![[26, 100, 18, 87, 78, 48, 76, 45], [97, 79, 105, 55, 60, 96, 32, 20], [94, 69, 75, 90], [77, 40, 59, 98, 20, 105, 97, 74], [106, 68, 97, 57], [104, 28, 44, 95, 24, 19, 27, 106]], ![[24, 48, 29, 70, 56, 24, 1, 45], [18, 64, 9, 87, 49, 56, 0, 31], [78, 19, 29, 40], [11, 82, 29, 66, 23, 23, 104, 7], [6, 81, 9, 16], [100, 71, 6, 10, 55, 100, 53, 5]], ![[10, 24, 25, 60, 9, 58, 69, 72], [64, 42, 68, 73, 101, 88, 31, 80], [61, 66, 57, 102], [88, 54, 38, 79, 82, 51, 53, 95], [17, 83, 32, 99], [26, 99, 25, 1, 33, 74, 68, 97]], ![[39, 8, 60, 58, 0, 102, 11, 73], [59, 55, 7, 30, 105, 5, 93, 18], [86, 50, 58, 69], [95, 71, 37, 60, 37, 34, 83, 98], [26, 51, 34, 1], [65, 17, 106, 28, 17, 24, 69, 5]]]
 h' := ![![[26, 81, 105, 67, 106], [77, 28, 99, 63, 77], [45, 57, 18, 84, 13], [18, 94, 5, 63, 37], [59, 94, 56, 81, 82], [0, 0, 0, 1], [0, 1]], ![[22, 106, 34, 101, 80], [31, 64, 10, 77, 94], [11, 72, 98, 43, 27], [35, 35, 54, 87, 82], [72, 33, 97, 2, 56], [3, 55, 86, 41, 59], [26, 81, 105, 67, 106]], ![[100, 27, 24, 38, 55], [61, 90, 47, 68, 26], [64, 74, 52, 93, 25], [22, 8, 95, 5, 88], [73, 2, 49, 64, 20], [68, 49, 99, 41, 4], [22, 106, 34, 101, 80]], ![[26, 106, 51, 8, 80], [76, 40, 64, 81, 72], [23, 68, 83, 55, 14], [96, 61, 84, 70, 67], [28, 73, 56, 77, 62], [52, 0, 60, 61, 45], [100, 27, 24, 38, 55]], ![[0, 1], [83, 99, 101, 32, 52], [76, 50, 70, 46, 28], [95, 16, 83, 96, 47], [75, 12, 63, 97, 101], [106, 3, 76, 70, 106], [26, 106, 51, 8, 80]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 42, 77, 85], [], [], []]
 b := ![[], [100, 84, 74, 77, 85], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 5
  hpos := by decide
  P := [63, 28, 77, 20, 40, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-23554825372481, -3192959088194, -23172779010552, -39749884242606, 38930333145256]
  a := ![26, 17, 31, 30, -91]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-220138554883, -29840739142, -216568028136, -371494245258, 363834889208]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 14025517307 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def PBC107 : ContainsPrimesAboveP 107 ![I107N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![107, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 107 (by decide) 𝕀

instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-537, 689, 17, 188, -312]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![-537, 689, 17, 188, -312]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![40, 28, 1, 0, 0], ![27, 100, 0, 1, 0], ![31, 18, 0, 0, 1]] where
  M :=![![![-537, 689, 17, 188, -312], ![872, -896, -29, -248, 380], ![-1024, 1339, 38, 364, -596], ![708, -874, -22, -239, 393], ![-140, 248, 8, 66, -111]]]
  hmulB := by decide  
  f := ![![![19, -15, -57, -32, 88]], ![![-288, 26, -1, -244, 40]], ![![-64, 3, -12, -64, 28]], ![![-251, 17, -25, -233, 73]], ![![-43, -1, -21, -54, 39]]]
  g := ![![![31, -119, 17, 188, -312], ![-28, 164, -29, -248, 380], ![56, -233, 38, 364, -596], ![-38, 152, -22, -239, 393], ![11, -42, 8, 66, -111]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [62, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [83, 108], [0, 1]]
 g := ![![[18, 105], [97], [38, 49], [108, 80], [74], [83, 1]], ![[13, 4], [97], [72, 60], [99, 29], [74], [57, 108]]]
 h' := ![![[83, 108], [1, 66], [42, 36], [62, 102], [83, 25], [86, 69], [0, 1]], ![[0, 1], [29, 43], [87, 73], [26, 7], [87, 84], [36, 40], [83, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55]]
 b := ![[], [85, 82]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [62, 26, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2307095, -825298, -2910089, -3898270, 5395662]
  a := ![239, 117, 236, 172, -835]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![477837, 3425342, -2910089, -3898270, 5395662]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, -3, -1, -2, 5]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![-7, -3, -1, -2, 5]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![18, 7, 1, 0, 0], ![14, 98, 0, 1, 0], ![95, 40, 0, 0, 1]] where
  M :=![![![-7, -3, -1, -2, 5], ![-16, -4, 3, -4, 1], ![4, -5, 18, 30, -25], ![12, -6, -32, -21, 46], ![-16, -6, -10, -16, 19]]]
  hmulB := by decide  
  f := ![![![-55, 71, -1, 20, -39]], ![![116, -96, -11, -26, 23]], ![![-2, 7, -1, 2, -6]], ![![98, -78, -10, -21, 16]], ![![-5, 27, -5, 8, -26]]]
  g := ![![![-4, 0, -1, -2, 5], ![-1, 3, 3, -4, 1], ![15, -19, 18, 30, -25], ![-32, 4, -32, -21, 46], ![-13, 8, -10, -16, 19]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P1 : CertificateIrreducibleZModOfList' 109 2 2 6 [88, 75, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [34, 108], [0, 1]]
 g := ![![[12, 83], [38], [33, 48], [58, 75], [48], [34, 1]], ![[0, 26], [38], [30, 61], [101, 34], [48], [68, 108]]]
 h' := ![![[34, 108], [30, 44], [39, 93], [19, 87], [30, 82], [60, 87], [0, 1]], ![[0, 1], [0, 65], [40, 16], [34, 22], [93, 27], [75, 22], [34, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77]]
 b := ![[], [54, 93]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N1 : CertifiedPrimeIdeal' SI109N1 109 where
  n := 2
  hpos := by decide
  P := [88, 75, 1]
  hirr := P109P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16078, -2993, -14573, -24822, 25014]
  a := ![19, 11, 21, 18, -66]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-16354, 14046, -14573, -24822, 25014]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N1 B_one_repr
lemma NI109N1 : Nat.card (O ⧸ I109N1) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N1

def I109N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 2, -1]] i)))

def SI109N2: IdealEqSpanCertificate' Table ![![3, 0, 0, 2, -1]] 
 ![![109, 0, 0, 0, 0], ![74, 1, 0, 0, 0], ![83, 0, 1, 0, 0], ![94, 0, 0, 1, 0], ![76, 0, 0, 0, 1]] where
  M :=![![![3, 0, 0, 2, -1], ![0, -1, -8, -8, 11], ![-28, 8, 15, -14, -23], ![44, 0, 18, 53, -33], ![20, -2, -6, 10, 5]]]
  hmulB := by decide  
  f := ![![![51, -486, 14, -128, 299]], ![![26, -327, 10, -86, 203]], ![![37, -380, 11, -100, 234]], ![![42, -414, 12, -109, 255]], ![![32, -342, 10, -90, 211]]]
  g := ![![![-1, 0, 0, 2, -1], ![6, -1, -8, -8, 11], ![11, 8, 15, -14, -23], ![-36, 0, 18, 53, -33], ![-6, -2, -6, 10, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N2 : Nat.card (O ⧸ I109N2) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N2)

lemma isPrimeI109N2 : Ideal.IsPrime I109N2 := prime_ideal_of_norm_prime hp109.out _ NI109N2
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![-537, 689, 17, 188, -312]] ![![-7, -3, -1, -2, 5]]
  ![![51, -486, 14, -128, 299]] where
 M := ![![![51, -486, 14, -128, 299]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![51, -486, 14, -128, 299]] ![![3, 0, 0, 2, -1]]
  ![![109, 0, 0, 0, 0]] where
 M := ![![![109, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0, 0, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0, 0, 0]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![0, 0, 113, 0, 0], ![0, 0, 0, 113, 0], ![0, 0, 0, 0, 113]] where
  M :=![![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![0, 0, 113, 0, 0], ![0, 0, 0, 113, 0], ![0, 0, 0, 0, 113]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 5 2 6 [85, 29, 44, 8, 106, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 10, 55, 50, 52], [28, 36, 79, 57, 31], [33, 77, 49, 32, 91], [49, 102, 43, 87, 52], [0, 1]]
 g := ![![[73, 111, 93, 97, 98], [50, 91, 12, 13], [6, 40, 59, 44], [107, 66, 28, 52], [41, 7, 1], []], ![[87, 90, 13, 33, 57, 23, 11, 85], [17, 55, 40, 111], [90, 18, 96, 52], [30, 70, 107, 91], [5, 65, 11, 95, 72, 2, 42, 15], [58, 49, 69, 80, 78, 42, 69, 36]], ![[42, 59, 41, 68, 84, 73, 98, 112], [34, 67, 82, 11], [23, 3, 64, 52], [3, 14, 52, 100], [104, 66, 41, 66, 67, 94, 69, 99], [89, 20, 73, 32, 65, 48, 81, 72]], ![[105, 47, 96, 15, 85, 0, 40, 81], [2, 110, 96, 104], [67, 107, 106, 25], [109, 63, 98, 85], [40, 81, 4, 15, 19, 104, 102, 61], [42, 81, 38, 52, 14, 46, 65, 87]], ![[83, 51, 103, 69, 30, 84, 15, 82], [26, 36, 37, 72], [68, 56, 13, 64], [41, 81, 2, 62], [67, 26, 64, 90, 97, 112, 14, 14], [106, 35, 4, 27, 74, 93, 85, 36]]]
 h' := ![![[10, 10, 55, 50, 52], [107, 72, 2, 37, 18], [96, 90, 16, 31, 37], [43, 61, 108, 105, 65], [18, 24, 55, 13, 74], [0, 0, 0, 1], [0, 1]], ![[28, 36, 79, 57, 31], [77, 9, 100, 82, 71], [36, 108, 40, 12, 87], [51, 35, 109, 44, 74], [62, 89, 0, 7, 59], [25, 91, 57, 63, 80], [10, 10, 55, 50, 52]], ![[33, 77, 49, 32, 91], [39, 10, 89, 85, 27], [68, 60, 69, 26, 24], [92, 95, 71, 56, 74], [102, 102, 44, 55, 103], [36, 48, 2, 73, 6], [28, 36, 79, 57, 31]], ![[49, 102, 43, 87, 52], [26, 73, 78, 60, 19], [99, 69, 13, 111, 45], [101, 41, 87, 27, 5], [10, 38, 47, 45, 56], [49, 54, 42, 0, 8], [33, 77, 49, 32, 91]], ![[0, 1], [1, 62, 70, 75, 91], [105, 12, 88, 46, 33], [3, 107, 77, 107, 8], [18, 86, 80, 106, 47], [46, 33, 12, 89, 19], [49, 102, 43, 87, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 12, 31, 76], [], [], []]
 b := ![[], [65, 102, 98, 54, 42], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 5
  hpos := by decide
  P := [85, 29, 44, 8, 106, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8740226145489101, 7819821783025772, 36998750803880936, 38899343246452160, -58701881376267662]
  a := ![-107, -61, -118, -103, 375]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![77347134030877, 69201962681644, 327422573485672, 344241975632320, -519485675896174]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 18424351793 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def PBC113 : ContainsPrimesAboveP 113 ![I113N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![113, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 113 (by decide) 𝕀

instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1457, -408, 244, -104, 872]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![-1457, -408, 244, -104, 872]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![117, 7, 1, 0, 0], ![86, 109, 0, 1, 0], ![66, 3, 0, 0, 1]] where
  M :=![![![-1457, -408, 244, -104, 872], ![-3280, -1005, 496, -248, 1888], ![-7056, -2288, 979, -552, 3928], ![696, 152, -144, 43, -456], ![-4640, -1536, 624, -368, 2555]]]
  hmulB := by decide  
  f := ![![![81, 8, 4, 88, -24]], ![![-80, -91, -336, -376, 544]], ![![59, 5, -9, 56, 0]], ![![2, -73, -280, -245, 440]], ![![46, 1, -8, 40, 3]]]
  g := ![![![-619, 52, 244, -104, 872], ![-1296, 133, 496, -248, 1888], ![-2625, 309, 979, -552, 3928], ![346, -17, -144, 43, -456], ![-1690, 209, 624, -368, 2555]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [75, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [124, 126], [0, 1]]
 g := ![![[61, 74], [10, 69], [20, 62], [31, 74], [31, 38], [124, 1]], ![[93, 53], [57, 58], [88, 65], [63, 53], [44, 89], [121, 126]]]
 h' := ![![[124, 126], [12, 70], [24, 113], [88, 69], [88, 57], [98, 61], [0, 1]], ![[0, 1], [56, 57], [66, 14], [8, 58], [44, 70], [42, 66], [124, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31]]
 b := ![[], [55, 79]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [75, 3, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-94375, 2634, -18734, -93910, 43021]
  a := ![35, 28, 52, 60, -123]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![57751, 80637, -18734, -93910, 43021]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-371, -244, -30, -48, 87]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![-371, -244, -30, -48, 87]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![19, 71, 1, 0, 0], ![66, 11, 0, 1, 0], ![46, 73, 0, 0, 1]] where
  M :=![![![-371, -244, -30, -48, 87], ![-252, -305, -112, -54, -75], ![408, -256, -313, -28, -603], ![476, 242, -8, 51, -181], ![484, -78, -222, 2, -497]]]
  hmulB := by decide  
  f := ![![![-185, 202, -8, 38, -67]], ![![192, -269, 34, -88, 65]], ![![79, -117, 19, -40, 23]], ![![-78, 79, -4, 9, -24]], ![![42, -81, 16, -38, 14]]]
  g := ![![![-5, -31, -30, -48, 87], ![70, 108, -112, -54, -75], ![283, 522, -313, -28, -603], ![44, 106, -8, 51, -181], ![216, 409, -222, 2, -497]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P1 : CertificateIrreducibleZModOfList' 127 2 2 6 [25, 105, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 126], [0, 1]]
 g := ![![[55, 61], [11, 4], [63, 42], [95, 44], [42, 115], [22, 1]], ![[0, 66], [99, 123], [98, 85], [47, 83], [32, 12], [44, 126]]]
 h' := ![![[22, 126], [106, 76], [76, 2], [38, 114], [93, 67], [85, 78], [0, 1]], ![[0, 1], [0, 51], [120, 125], [6, 13], [43, 60], [23, 49], [22, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41]]
 b := ![[], [92, 84]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N1 : CertifiedPrimeIdeal' SI127N1 127 where
  n := 2
  hpos := by decide
  P := [25, 105, 1]
  hirr := P127P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-85035, 13942, 35744, -43330, -44478]
  a := ![-28, -30, -56, -78, 98]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![32611, 9446, 35744, -43330, -44478]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N1 B_one_repr
lemma NI127N1 : Nat.card (O ⧸ I127N1) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N1

def I127N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8879, 10244, 296, 2812, -4488]] i)))

def SI127N2: IdealEqSpanCertificate' Table ![![-8879, 10244, 296, 2812, -4488]] 
 ![![127, 0, 0, 0, 0], ![49, 1, 0, 0, 0], ![12, 0, 1, 0, 0], ![57, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![-8879, 10244, 296, 2812, -4488], ![12328, -14207, -412, -3900, 6220], ![-17080, 19716, 569, 5412, -8640], ![11392, -13140, -380, -3607, 5756], ![-2896, 3352, 96, 920, -1471]]]
  hmulB := by decide  
  f := ![![![-17, -44, 104, 172, -72]], ![![-7, -19, 36, 64, -20]], ![![-28, -4, 9, -4, 0]], ![![9, -16, 68, 109, -68]], ![![7, -4, 8, 20, -7]]]
  g := ![![![-5065, 10244, 296, 2812, -4488], ![7025, -14207, -412, -3900, 6220], ![-9748, 19716, 569, 5412, -8640], ![6497, -13140, -380, -3607, 5756], ![-1657, 3352, 96, 920, -1471]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N2 : Nat.card (O ⧸ I127N2) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N2)

lemma isPrimeI127N2 : Ideal.IsPrime I127N2 := prime_ideal_of_norm_prime hp127.out _ NI127N2
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![-1457, -408, 244, -104, 872]] ![![-371, -244, -30, -48, 87]]
  ![![1115459, 324300, -179718, 81576, -657851]] where
 M := ![![![1115459, 324300, -179718, 81576, -657851]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![1115459, 324300, -179718, 81576, -657851]] ![![-8879, 10244, 296, 2812, -4488]]
  ![![127, 0, 0, 0, 0]] where
 M := ![![![-2156333, -913384, 152146, -200660, 979805]]]
 hmul := by decide  
 g := ![![![![-16979, -7192, 1198, -1580, 7715]]]]
 hle2 := by decide  


def PBC127 : ContainsPrimesAboveP 127 ![I127N0, I127N1, I127N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
    exact isPrimeI127N1
    exact isPrimeI127N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 127 (by decide) (𝕀 ⊙ MulI127N0 ⊙ MulI127N1)
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


def P131P0 : CertificateIrreducibleZModOfList' 131 5 2 7 [77, 121, 102, 73, 50, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 84, 36, 18, 127], [55, 58, 128, 3, 32], [3, 46, 106, 38, 120], [128, 73, 123, 72, 114], [0, 1]]
 g := ![![[49, 75, 1, 51, 11], [48, 95, 130, 71, 28], [4, 32, 93, 62], [116, 62, 93, 7], [98, 69, 81, 1], [], []], ![[11, 5, 95, 82, 41, 99, 16, 79], [75, 96, 50, 122, 118, 111, 80, 71], [87, 33, 54, 125], [126, 124, 5, 44], [8, 93, 42, 13], [116, 65, 0, 38], [19, 87, 104, 16]], ![[56, 26, 56, 5, 32, 85, 32, 110], [130, 92, 88, 82, 64, 124, 117, 57], [123, 45, 55, 41], [124, 40, 90, 58], [105, 42, 87, 48], [18, 102, 31, 41], [29, 89, 82, 107]], ![[13, 87, 61, 92, 44, 8, 30, 40], [11, 74, 66, 5, 41, 45, 1, 87], [5, 96, 33, 46], [76, 93, 54, 36], [91, 80, 41, 112], [93, 28, 54, 41], [116, 5, 57, 121]], ![[14, 59, 104, 87, 40, 87, 68, 44], [78, 129, 10, 91, 17, 90, 44, 5], [12, 64, 32, 107], [115, 6, 110, 117], [62, 21, 7, 27], [12, 125, 17, 38], [80, 29, 1, 27]]]
 h' := ![![[26, 84, 36, 18, 127], [103, 4, 43, 44, 50], [17, 38, 88, 115, 40], [60, 62, 4, 5, 18], [52, 121, 46, 34, 20], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[55, 58, 128, 3, 32], [72, 68, 60, 88, 119], [41, 114, 49, 106, 43], [94, 52, 128, 66, 16], [44, 65, 60, 106, 100], [108, 44, 47, 7, 12], [130, 86, 114, 68, 118], [26, 84, 36, 18, 127]], ![[3, 46, 106, 38, 120], [111, 108, 78, 14, 40], [38, 113, 52, 87, 102], [48, 19, 55, 18, 33], [65, 106, 125, 90, 53], [91, 86, 39, 106, 21], [6, 79, 23, 101, 33], [55, 58, 128, 3, 32]], ![[128, 73, 123, 72, 114], [114, 1, 119, 120, 100], [44, 121, 118, 110, 2], [6, 87, 121, 122, 96], [116, 37, 121, 42, 125], [7, 125, 14, 59, 80], [116, 3, 74, 115, 98], [3, 46, 106, 38, 120]], ![[0, 1], [11, 81, 93, 127, 84], [38, 7, 86, 106, 75], [62, 42, 85, 51, 99], [128, 64, 41, 121, 95], [29, 7, 31, 90, 17], [6, 94, 50, 109, 13], [128, 73, 123, 72, 114]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [124, 10, 105, 23], [], [], []]
 b := ![[], [51, 82, 48, 94, 104], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 5
  hpos := by decide
  P := [77, 121, 102, 73, 50, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![54735850060976, -6977950803275, -7754259261359, 39994177288763, 5535888118437]
  a := ![17, 23, 43, 61, -53]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![417830916496, -53266800025, -59192818789, 305299063273, 42258687927]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, 8, 0, 2, -4]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![-5, 8, 0, 2, -4]] 
 ![![137, 0, 0, 0, 0], ![23, 1, 0, 0, 0], ![19, 0, 1, 0, 0], ![81, 0, 0, 1, 0], ![122, 0, 0, 0, 1]] where
  M :=![![![-5, 8, 0, 2, -4], ![12, -9, 0, -2, 2], ![-4, 16, -1, 6, -8], ![4, -10, -2, -7, 8], ![0, 4, 0, 0, -3]]]
  hmulB := by decide  
  f := ![![![-301, -92, 44, -22, 164]], ![![-55, -17, 8, -4, 30]], ![![-51, -16, 7, -4, 28]], ![![-177, -54, 26, -13, 96]], ![![-274, -84, 40, -20, 149]]]
  g := ![![![1, 8, 0, 2, -4], ![1, -9, 0, -2, 2], ![1, 16, -1, 6, -8], ![-1, -10, -2, -7, 8], ![2, 4, 0, 0, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N0 : Nat.card (O ⧸ I137N0) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N0)

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := prime_ideal_of_norm_prime hp137.out _ NI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-21815, 25158, 728, 6906, -11019]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![-21815, 25158, 728, 6906, -11019]] 
 ![![137, 0, 0, 0, 0], ![76, 1, 0, 0, 0], ![115, 0, 1, 0, 0], ![136, 0, 0, 1, 0], ![19, 0, 0, 0, 1]] where
  M :=![![![-21815, 25158, 728, 6906, -11019], ![30264, -34899, -1010, -9580, 15285], ![-41980, 48414, 1401, 13290, -21205], ![27984, -32272, -934, -8859, 14135], ![-7132, 8226, 238, 2258, -3603]]]
  hmulB := by decide  
  f := ![![![-267, -28, 114, 24, 121]], ![![-152, -17, 64, 14, 71]], ![![-241, -28, 93, 12, 118]], ![![-268, -26, 120, 27, 109]], ![![-45, -6, 20, 6, 18]]]
  g := ![![![-20054, 25158, 728, 6906, -11019], ![27819, -34899, -1010, -9580, 15285], ![-38592, 48414, 1401, 13290, -21205], ![25725, -32272, -934, -8859, 14135], ![-6557, 8226, 238, 2258, -3603]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1

def I137N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 17, 77, 72, -120]] i)))

def SI137N2: IdealEqSpanCertificate' Table ![![7, 17, 77, 72, -120]] 
 ![![137, 0, 0, 0, 0], ![90, 1, 0, 0, 0], ![120, 0, 1, 0, 0], ![26, 0, 0, 1, 0], ![111, 0, 0, 0, 1]] where
  M :=![![![7, 17, 77, 72, -120], ![336, -60, -117, 188, 144], ![-952, -157, -1046, -1696, 1748], ![-508, 442, 1686, 1001, -2567], ![372, 96, 568, 802, -927]]]
  hmulB := by decide  
  f := ![![![-1107801, 1277877, 36959, 350780, -559760]], ![![-716530, 826544, 23905, 226888, -362060]], ![![-985896, 1137259, 32892, 312180, -498164]], ![![-199866, 230552, 6668, 63287, -100991]], ![![-900203, 1038411, 30033, 285046, -454865]]]
  g := ![![![5, 17, 77, 72, -120], ![-8, -60, -117, 188, 144], ![-82, -157, -1046, -1696, 1748], ![119, 442, 1686, 1001, -2567], ![41, 96, 568, 802, -927]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N2 : Nat.card (O ⧸ I137N2) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N2)

lemma isPrimeI137N2 : Ideal.IsPrime I137N2 := prime_ideal_of_norm_prime hp137.out _ NI137N2

def I137N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![329, -379, -11, -104, 166]] i)))

def SI137N3: IdealEqSpanCertificate' Table ![![329, -379, -11, -104, 166]] 
 ![![137, 0, 0, 0, 0], ![91, 1, 0, 0, 0], ![76, 0, 1, 0, 0], ![94, 0, 0, 1, 0], ![69, 0, 0, 0, 1]] where
  M :=![![![329, -379, -11, -104, 166], ![-456, 526, 15, 144, -230], ![632, -729, -20, -200, 318], ![-420, 486, 14, 135, -213], ![108, -124, -4, -34, 55]]]
  hmulB := by decide  
  f := ![![![233, 177, 35, 36, -26]], ![![155, 119, 24, 24, -16]], ![![124, 99, 22, 20, -10]], ![![158, 120, 24, 25, -17]], ![![113, 89, 19, 18, -9]]]
  g := ![![![248, -379, -11, -104, 166], ![-344, 526, 15, 144, -230], ![477, -729, -20, -200, 318], ![-319, 486, 14, 135, -213], ![81, -124, -4, -34, 55]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N3 : Nat.card (O ⧸ I137N3) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N3)

lemma isPrimeI137N3 : Ideal.IsPrime I137N3 := prime_ideal_of_norm_prime hp137.out _ NI137N3

def I137N4 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-371, 160, 534, 138, -788]] i)))

def SI137N4: IdealEqSpanCertificate' Table ![![-371, 160, 534, 138, -788]] 
 ![![137, 0, 0, 0, 0], ![131, 1, 0, 0, 0], ![101, 0, 1, 0, 0], ![34, 0, 0, 1, 0], ![70, 0, 0, 0, 1]] where
  M :=![![![-371, 160, 534, 138, -788], ![2876, -113, 676, 3022, -1398], ![-452, -2492, -10849, -9610, 16960], ![-12648, 3254, 8818, -3267, -12228], ![-656, 1300, 5296, 3944, -8175]]]
  hmulB := by decide  
  f := ![![![2608949, -3010236, -86942, -826318, 1318916]], ![![2468243, -2847929, -82250, -781764, 1247814]], ![![1960013, -2261516, -65315, -620792, 990876]], ![![623042, -718882, -20762, -197335, 314976]], ![![1339246, -1545268, -44628, -424180, 677057]]]
  g := ![![![-181, 160, 534, 138, -788], ![-405, -113, 676, 3022, -1398], ![4097, -2492, -10849, -9610, 16960], ![-2646, 3254, 8818, -3267, -12228], ![-1954, 1300, 5296, 3944, -8175]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N4 : Nat.card (O ⧸ I137N4) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N4)

lemma isPrimeI137N4 : Ideal.IsPrime I137N4 := prime_ideal_of_norm_prime hp137.out _ NI137N4
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![-5, 8, 0, 2, -4]] ![![-21815, 25158, 728, 6906, -11019]]
  ![![435683, -502430, -14540, -137920, 220057]] where
 M := ![![![435683, -502430, -14540, -137920, 220057]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI137N1 : IdealMulLeCertificate' Table 
  ![![435683, -502430, -14540, -137920, 220057]] ![![7, 17, 77, 72, -120]]
  ![![-55, 23, -3, -30, 1]] where
 M := ![![![-55, 23, -3, -30, 1]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI137N2 : IdealMulLeCertificate' Table 
  ![![-55, 23, -3, -30, 1]] ![![329, -379, -11, -104, 166]]
  ![![-17771, 20426, 586, 5548, -8929]] where
 M := ![![![-17771, 20426, 586, 5548, -8929]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI137N3 : IdealMulLeCertificate' Table 
  ![![-17771, 20426, 586, 5548, -8929]] ![![-371, 160, 534, 138, -788]]
  ![![137, 0, 0, 0, 0]] where
 M := ![![![759665, -166318, -404972, 302222, 540191]]]
 hmul := by decide  
 g := ![![![![5545, -1214, -2956, 2206, 3943]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N1, I137N2, I137N3, I137N4] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
    exact isPrimeI137N2
    exact isPrimeI137N3
    exact isPrimeI137N4
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0 ⊙ MulI137N1 ⊙ MulI137N2 ⊙ MulI137N3)
instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0, 0, 0]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0, 0, 0]] 
 ![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![0, 0, 139, 0, 0], ![0, 0, 0, 139, 0], ![0, 0, 0, 0, 139]] where
  M :=![![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![0, 0, 139, 0, 0], ![0, 0, 0, 139, 0], ![0, 0, 0, 0, 139]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 5 2 7 [78, 116, 96, 14, 107, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [137, 91, 88, 115, 85], [1, 106, 104, 133, 31], [106, 128, 39, 81, 47], [66, 91, 47, 88, 115], [0, 1]]
 g := ![![[82, 54, 46, 55, 54], [29, 35, 71, 65, 120], [30, 45, 107, 129], [56, 3, 60, 61, 79], [84, 37, 32, 1], [], []], ![[80, 125, 85, 113, 36, 64, 78, 19], [114, 74, 106, 61, 85, 107, 61, 123], [51, 75, 12, 112], [43, 68, 50, 82, 9, 72, 68, 98], [44, 108, 105, 49], [44, 111, 78, 42], [95, 96, 133, 136]], ![[43, 79, 34, 47, 61, 64, 118, 52], [60, 99, 33, 78, 128, 61, 86, 89], [50, 17, 89, 45], [54, 36, 92, 84, 107, 132, 71, 11], [112, 124, 136, 131], [110, 96, 81, 120], [104, 113, 78, 127]], ![[94, 97, 24, 33, 34, 39, 105, 107], [94, 78, 1, 54, 83, 5, 98, 45], [63, 109, 84, 83], [52, 70, 88, 50, 67, 117, 100, 4], [34, 113, 44, 25], [126, 1, 59, 129], [16, 62, 45, 124]], ![[13, 114, 111, 63, 110, 122, 114, 98], [27, 83, 134, 4, 66, 93, 122, 17], [120, 93, 97, 77], [54, 37, 5, 20, 28, 46, 108, 58], [57, 85, 104, 120], [93, 70, 49, 120], [31, 52, 30, 20]]]
 h' := ![![[137, 91, 88, 115, 85], [101, 29, 41, 42, 38], [29, 68, 38, 102, 113], [80, 25, 133, 117, 44], [120, 19, 21, 100, 94], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[1, 106, 104, 133, 31], [110, 72, 84, 124, 8], [124, 53, 110, 46, 44], [99, 132, 73, 126, 116], [17, 27, 52, 124, 97], [35, 5, 37, 104, 7], [100, 32, 95, 102, 96], [137, 91, 88, 115, 85]], ![[106, 128, 39, 81, 47], [47, 60, 101, 18, 107], [138, 49, 138, 40, 84], [110, 80, 92, 99, 36], [98, 112, 8, 1, 88], [76, 84, 101, 52, 100], [90, 45, 60, 91, 113], [1, 106, 104, 133, 31]], ![[66, 91, 47, 88, 115], [16, 136, 135, 96, 62], [3, 12, 12, 115, 89], [82, 88, 100, 64, 19], [9, 12, 22, 136, 59], [24, 17, 74, 119, 5], [119, 11, 43, 111, 95], [106, 128, 39, 81, 47]], ![[0, 1], [58, 120, 56, 137, 63], [71, 96, 119, 114, 87], [102, 92, 19, 11, 63], [56, 108, 36, 56, 79], [38, 33, 66, 3, 26], [131, 51, 79, 113, 113], [66, 91, 47, 88, 115]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 34, 26, 6], [], [], []]
 b := ![[], [69, 122, 114, 117, 31], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 5
  hpos := by decide
  P := [78, 116, 96, 14, 107, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![25681684480, 4250721748, 28684179556, 46286064808, -47737244963]
  a := ![-1, -5, -8, -15, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![184760320, 30580732, 206361004, 332993272, -343433417]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 51888844699 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def PBC139 : ContainsPrimesAboveP 139 ![I139N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![139, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 139 (by decide) 𝕀

instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2465, -741, 381, -184, 1430]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![-2465, -741, 381, -184, 1430]] 
 ![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![147, 30, 1, 0, 0], ![16, 95, 0, 1, 0], ![101, 63, 0, 0, 1]] where
  M :=![![![-2465, -741, 381, -184, 1430], ![-5352, -1716, 757, -416, 3002], ![-11176, -3763, 1462, -896, 6094], ![1280, 330, -234, 87, -795], ![-7276, -2492, 924, -590, 3927]]]
  hmulB := by decide  
  f := ![![![-141, 195, 39, 100, -138]], ![![352, -302, -127, -68, 286]], ![![-75, 134, 11, 80, -76]], ![![212, -172, -71, -27, 159]], ![![55, 5, -26, 42, 25]]]
  g := ![![![-1342, -569, 381, -184, 1430], ![-2773, -1168, 757, -416, 3002], ![-5552, -2325, 1462, -896, 6094], ![769, 330, -234, 87, -795], ![-3559, -1487, 924, -590, 3927]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [16, 43, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [106, 148], [0, 1]]
 g := ![![[12, 28], [116], [66, 6], [145], [83, 45], [61], [1]], ![[0, 121], [116], [106, 143], [145], [85, 104], [61], [1]]]
 h' := ![![[106, 148], [101, 37], [136, 99], [84, 119], [13, 61], [25, 94], [133, 106], [0, 1]], ![[0, 1], [0, 112], [51, 50], [33, 30], [72, 88], [6, 55], [45, 43], [106, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [64, 100]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [16, 43, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-134242, -8980, -59730, -154452, 122277]
  a := ![-45, -32, -57, -62, 159]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-8273, 58741, -59730, -154452, 122277]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![265, 142, -4, 30, -103]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![265, 142, -4, 30, -103]] 
 ![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![97, 15, 1, 0, 0], ![72, 147, 0, 1, 0], ![113, 64, 0, 0, 1]] where
  M :=![![![265, 142, -4, 30, -103], ![352, 201, 14, 40, -99], ![316, 286, 69, 54, -17], ![-256, -124, 14, -27, 115], ![116, 146, 54, 26, 37]]]
  hmulB := by decide  
  f := ![![![-15, -4, -42, -44, 65]], ![![-172, 31, 88, -78, -113]], ![![-23, 1, -15, -30, 25]], ![![-176, 27, 60, -103, -70]], ![![-87, 10, 4, -70, 4]]]
  g := ![![![68, 16, -4, 30, -103], ![49, 3, 14, 40, -99], ![-56, -51, 69, 54, -17], ![-85, -25, 14, -27, 115], ![-75, -46, 54, 26, 37]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P1 : CertificateIrreducibleZModOfList' 149 2 2 7 [122, 54, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [95, 148], [0, 1]]
 g := ![![[147, 133], [73], [7, 25], [104], [58, 7], [85], [1]], ![[117, 16], [73], [147, 124], [104], [127, 142], [85], [1]]]
 h' := ![![[95, 148], [144, 27], [40, 85], [91, 5], [76, 36], [44, 93], [27, 95], [0, 1]], ![[0, 1], [27, 122], [69, 64], [119, 144], [69, 113], [88, 56], [112, 54], [95, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [141, 88]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N1 : CertifiedPrimeIdeal' SI149N1 149 where
  n := 2
  hpos := by decide
  P := [122, 54, 1]
  hirr := P149P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-38749, -1619, -14754, -43321, 30936]
  a := ![-23, -17, -32, -35, 81]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![6817, 30926, -14754, -43321, 30936]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N1 B_one_repr
lemma NI149N1 : Nat.card (O ⧸ I149N1) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N1

def I149N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2049, -2353, -69, -646, 1028]] i)))

def SI149N2: IdealEqSpanCertificate' Table ![![2049, -2353, -69, -646, 1028]] 
 ![![149, 0, 0, 0, 0], ![104, 1, 0, 0, 0], ![61, 0, 1, 0, 0], ![71, 0, 0, 1, 0], ![18, 0, 0, 0, 1]] where
  M :=![![![2049, -2353, -69, -646, 1028], ![-2820, 3272, 93, 898, -1438], ![3956, -4523, -134, -1242, 1972], ![-2624, 3020, 88, 829, -1321], ![684, -764, -24, -210, 329]]]
  hmulB := by decide  
  f := ![![![-227, 3, 89, -62, -60]], ![![-156, 2, 65, -38, -46]], ![![-87, -4, 21, -32, 0]], ![![-133, 5, 47, -47, -33]], ![![-34, 2, 18, -6, -17]]]
  g := ![![![1868, -2353, -69, -646, 1028], ![-2595, 3272, 93, 898, -1438], ![3592, -4523, -134, -1242, 1972], ![-2397, 3020, 88, 829, -1321], ![608, -764, -24, -210, 329]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N2 : Nat.card (O ⧸ I149N2) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N2)

lemma isPrimeI149N2 : Ideal.IsPrime I149N2 := prime_ideal_of_norm_prime hp149.out _ NI149N2
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![-2465, -741, 381, -184, 1430]] ![![265, 142, -4, 30, -103]]
  ![![-580677, -158409, 100419, -40868, 352527]] where
 M := ![![![-580677, -158409, 100419, -40868, 352527]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI149N1 : IdealMulLeCertificate' Table 
  ![![-580677, -158409, 100419, -40868, 352527]] ![![2049, -2353, -69, -646, 1028]]
  ![![149, 0, 0, 0, 0]] where
 M := ![![![2529871, 1071608, -178502, 235420, -1149535]]]
 hmul := by decide  
 g := ![![![![16979, 7192, -1198, 1580, -7715]]]]
 hle2 := by decide  


def PBC149 : ContainsPrimesAboveP 149 ![I149N0, I149N1, I149N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
    exact isPrimeI149N1
    exact isPrimeI149N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 149 (by decide) (𝕀 ⊙ MulI149N0 ⊙ MulI149N1)
instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, 7, -1, 2, -1]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![-7, 7, -1, 2, -1]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![93, 121, 1, 0, 0], ![47, 40, 0, 1, 0], ![8, 103, 0, 0, 1]] where
  M :=![![![-7, 7, -1, 2, -1], ![0, -12, -3, -12, 11], ![-20, 21, 30, 26, -51], ![48, -18, -20, 13, 30], ![0, -2, -14, -8, 21]]]
  hmulB := by decide  
  f := ![![![83, 7, -27, 4, -71]], ![![276, 48, -63, 14, -185]], ![![277, 44, -68, 14, -195]], ![![99, 15, -25, 5, -71]], ![![196, 34, -45, 10, -132]]]
  g := ![![![0, 1, -1, 2, -1], ![5, -2, -3, -12, 11], ![-24, 4, 30, 26, -51], ![7, -8, -20, 13, 30], ![10, -1, -14, -8, 21]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [139, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [133, 150], [0, 1]]
 g := ![![[74, 88], [54, 139], [92, 81], [139], [40, 44], [22], [1]], ![[0, 63], [119, 12], [144, 70], [139], [3, 107], [22], [1]]]
 h' := ![![[133, 150], [44, 36], [47, 130], [132, 142], [27, 21], [106, 78], [12, 133], [0, 1]], ![[0, 1], [0, 115], [123, 21], [143, 9], [102, 130], [61, 73], [34, 18], [133, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [138]]
 b := ![[], [17, 69]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [139, 18, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-159, 519, 3017, 2783, -3972]
  a := ![2, 5, 9, 15, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2515, -442, 3017, 2783, -3972]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![45, -23, -7, -6, -6]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![45, -23, -7, -6, -6]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![79, 113, 1, 0, 0], ![107, 131, 0, 1, 0], ![45, 43, 0, 0, 1]] where
  M :=![![![45, -23, -7, -6, -6], ![36, 50, -13, 14, -60], ![212, -5, -32, -2, -82], ![-32, 36, 4, 9, -9], ![124, 24, -20, 6, -67]]]
  hmulB := by decide  
  f := ![![![-21, -1, 5, -10, -2]], ![![28, 4, 49, 74, -76]], ![![11, 2, 38, 50, -56]], ![![7, 3, 46, 55, -67]], ![![1, 1, 16, 18, -23]]]
  g := ![![![10, 12, -7, -6, -6], ![15, 15, -13, 14, -60], ![44, 49, -32, -2, -82], ![-6, -8, 4, 9, -9], ![27, 29, -20, 6, -67]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P1 : CertificateIrreducibleZModOfList' 151 2 2 7 [124, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [138, 150], [0, 1]]
 g := ![![[89, 123], [22, 55], [13, 123], [2], [111, 145], [18], [1]], ![[0, 28], [62, 96], [75, 28], [2], [38, 6], [18], [1]]]
 h' := ![![[138, 150], [141, 127], [49, 120], [130, 127], [128, 105], [7, 121], [27, 138], [0, 1]], ![[0, 1], [0, 24], [150, 31], [140, 24], [122, 46], [95, 30], [45, 13], [138, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [127]]
 b := ![[], [73, 139]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N1 : CertifiedPrimeIdeal' SI151N1 151 where
  n := 2
  hpos := by decide
  P := [124, 13, 1]
  hirr := P151P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-974404, -74836, -491018, -1172334, 959833]
  a := ![127, 90, 156, 164, -441]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![795121, 1110683, -491018, -1172334, 959833]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N1 B_one_repr
lemma NI151N1 : Nat.card (O ⧸ I151N1) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N1

def I151N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, -2, 0, 0, 1]] i)))

def SI151N2: IdealEqSpanCertificate' Table ![![-3, -2, 0, 0, 1]] 
 ![![151, 0, 0, 0, 0], ![68, 1, 0, 0, 0], ![57, 0, 1, 0, 0], ![118, 0, 0, 1, 0], ![133, 0, 0, 0, 1]] where
  M :=![![![-3, -2, 0, 0, 1], ![-4, -3, -2, -2, 3], ![-8, -2, 1, -4, -5], ![12, 2, 4, 11, -9], ![4, -2, -2, 2, -1]]]
  hmulB := by decide  
  f := ![![![463, -564, -18, -154, 247]], ![![204, -249, -8, -68, 109]], ![![181, -220, -7, -60, 96]], ![![358, -436, -14, -119, 191]], ![![409, -498, -16, -136, 218]]]
  g := ![![![0, -2, 0, 0, 1], ![1, -3, -2, -2, 3], ![8, -2, 1, -4, -5], ![-3, 2, 4, 11, -9], ![1, -2, -2, 2, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N2 : Nat.card (O ⧸ I151N2) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N2)

lemma isPrimeI151N2 : Ideal.IsPrime I151N2 := prime_ideal_of_norm_prime hp151.out _ NI151N2
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![-7, 7, -1, 2, -1]] ![![45, -23, -7, -6, -6]]
  ![![-463, 564, 18, 154, -247]] where
 M := ![![![-463, 564, 18, 154, -247]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI151N1 : IdealMulLeCertificate' Table 
  ![![-463, 564, 18, 154, -247]] ![![-3, -2, 0, 0, 1]]
  ![![151, 0, 0, 0, 0]] where
 M := ![![![-151, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC151 : ContainsPrimesAboveP 151 ![I151N0, I151N1, I151N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
    exact isPrimeI151N1
    exact isPrimeI151N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 151 (by decide) (𝕀 ⊙ MulI151N0 ⊙ MulI151N1)


lemma PB312I3_primes (p : ℕ) :
  p ∈ Set.range ![107, 109, 113, 127, 131, 137, 139, 149, 151] ↔ Nat.Prime p ∧ 103 < p ∧ p ≤ 151 := by
  rw [← List.mem_ofFn']
  convert primes_range 103 151 (by omega)

def PB312I3 : PrimesBelowBoundCertificateInterval O 103 151 312 where
  m := 9
  g := ![1, 3, 1, 3, 1, 5, 1, 3, 3]
  P := ![107, 109, 113, 127, 131, 137, 139, 149, 151]
  hP := PB312I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I107N0]
    · exact ![I109N0, I109N1, I109N2]
    · exact ![I113N0]
    · exact ![I127N0, I127N1, I127N2]
    · exact ![I131N0]
    · exact ![I137N0, I137N1, I137N2, I137N3, I137N4]
    · exact ![I139N0]
    · exact ![I149N0, I149N1, I149N2]
    · exact ![I151N0, I151N1, I151N2]
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
    · exact ![14025517307]
    · exact ![11881, 11881, 109]
    · exact ![18424351793]
    · exact ![16129, 16129, 127]
    · exact ![38579489651]
    · exact ![137, 137, 137, 137, 137]
    · exact ![51888844699]
    · exact ![22201, 22201, 149]
    · exact ![22801, 22801, 151]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
      exact NI109N2
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
      exact NI127N2
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
      exact NI137N2
      exact NI137N3
      exact NI137N4
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
      exact NI149N2
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
      exact NI151N2
  β := ![I109N2, I127N2, I137N0, I137N1, I137N2, I137N3, I137N4, I149N2, I151N2]
  Il := ![[], [I109N2], [], [I127N2], [], [I137N0, I137N1, I137N2, I137N3, I137N4], [], [I149N2], [I151N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
