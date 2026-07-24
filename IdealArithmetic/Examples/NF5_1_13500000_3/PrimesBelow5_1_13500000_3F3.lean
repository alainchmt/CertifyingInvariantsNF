
import IdealArithmetic.Examples.NF5_1_13500000_3.RI5_1_13500000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1595, -726, -1762, 2352, 5534]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![-1595, -726, -1762, 2352, 5534]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![0, 0, 107, 0, 0], ![0, 0, 0, 107, 0], ![71, 67, 73, 50, 1]] where
  M :=![![![-1595, -726, -1762, 2352, 5534], ![-12728, -1005, -3770, 5884, 10792], ![-19632, -10614, -14725, 15996, 39208], ![-40060, -8678, -12202, 14325, 28160], ![444, -4500, -4788, 4020, 12685]]]
  hmulB := by decide  
  f := ![![![-2665, -366, 1534, -552, -2042]], ![![5960, -1683, -1138, 860, 440]], ![![1680, 5682, -5963, 1164, 10280]], ![![-21212, -718, 10198, -4065, -12632]], ![![-6713, 2261, 947, -914, 107]]]
  g := ![![![-3687, -3472, -3792, -2564, 5534], ![-7280, -6767, -7398, -4988, 10792], ![-26200, -24650, -26887, -18172, 39208], ![-19060, -17714, -19326, -13025, 28160], ![-8413, -7985, -8699, -5890, 12685]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 4 2 6 [17, 48, 20, 7, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [90, 73, 53, 96], [93, 31, 10, 90], [24, 2, 44, 28], [0, 1]]
 g := ![![[1, 32, 36, 52], [4, 38, 64, 85], [48, 100, 79], [80, 60, 50, 16], [29, 100, 1], []], ![[76, 99, 73, 57, 95, 18], [75, 88, 36, 18, 76, 71], [91, 25, 27], [61, 94, 47, 25, 99, 2], [58, 39, 14], [21, 65, 106, 103, 94, 60]], ![[28, 78, 39, 37, 15, 79], [52, 18, 91, 80, 55, 49], [29, 37, 10], [103, 18, 91, 15, 36, 13], [68, 93, 61], [23, 5, 22, 82, 47, 9]], ![[12, 92, 16, 83, 103, 32], [19, 16, 41, 22, 49, 7], [35, 1, 100], [6, 79, 91, 24, 17, 6], [6, 66, 56], [8, 80, 70, 19, 7, 17]]]
 h' := ![![[90, 73, 53, 96], [39, 71, 36, 65], [38, 68, 7, 70], [31, 7, 88, 87], [42, 11, 60, 103], [0, 0, 0, 1], [0, 1]], ![[93, 31, 10, 90], [48, 11, 64, 58], [105, 0, 91, 86], [58, 57, 0, 54], [64, 97, 106, 52], [80, 81, 57, 96], [90, 73, 53, 96]], ![[24, 2, 44, 28], [22, 36, 71, 42], [53, 13, 25, 4], [92, 82, 0, 63], [82, 18, 36, 12], [75, 26, 75, 32], [93, 31, 10, 90]], ![[0, 1], [13, 96, 43, 49], [96, 26, 91, 54], [100, 68, 19, 10], [69, 88, 12, 47], [99, 0, 82, 85], [24, 2, 44, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [95, 75, 11], []]
 b := ![[], [], [100, 12, 83, 51], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 4
  hpos := by decide
  P := [17, 48, 20, 7, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![35282821, -19838348, 3736980, -27971576, -46982306]
  a := ![-22, -8, 30, -26, -77]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![31504921, 29233422, 32088274, 21692932, -46982306]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 131079601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2665, 366, -1534, 552, 2042]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![2665, 366, -1534, 552, 2042]] 
 ![![107, 0, 0, 0, 0], ![53, 1, 0, 0, 0], ![80, 0, 1, 0, 0], ![47, 0, 0, 1, 0], ![84, 0, 0, 0, 1]] where
  M :=![![![2665, 366, -1534, 552, 2042], ![-5960, 1683, 1138, -860, -440], ![-1680, -5682, 5963, -1164, -10280], ![21212, 718, -10198, 4065, 12632], ![-9564, -1788, 5940, -2052, -8111]]]
  hmulB := by decide  
  f := ![![![1595, 726, 1762, -2352, -5534]], ![![909, 369, 908, -1220, -2842]], ![![1376, 642, 1455, -1908, -4504]], ![![1075, 400, 888, -1167, -2694]], ![![1248, 612, 1428, -1884, -4463]]]
  g := ![![![-855, 366, -1534, 552, 2042], ![-1017, 1683, 1138, -860, -440], ![6922, -5682, 5963, -1164, -10280], ![-4235, 718, -10198, 4065, 12632], ![3624, -1788, 5940, -2052, -8111]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![-1595, -726, -1762, 2352, 5534]] ![![2665, 366, -1534, 552, 2042]]
  ![![107, 0, 0, 0, 0]] where
 M := ![![![-107, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-359, -40, -12, 0, -73]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![-359, -40, -12, 0, -73]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![18, 101, 1, 0, 0], ![72, 32, 0, 1, 0], ![102, 81, 0, 0, 1]] where
  M :=![![![-359, -40, -12, 0, -73], ![292, -371, -186, -24, 292], ![-1264, 82, 357, -468, -1504], ![1926, -502, 34, -567, -414], ![-1054, 316, 308, -194, -975]]]
  hmulB := by decide  
  f := ![![![-3373, 2480, -756, -258, 2271]], ![![-10116, -4387, 8570, -2544, -12696]], ![![-9558, -3693, 7683, -2336, -11250]], ![![-5302, 522, 1906, -911, -2000]], ![![-10532, -1023, 5674, -2118, -7371]]]
  g := ![![![67, 65, -12, 0, -73], ![-224, -41, -186, -24, 292], ![1646, 925, 357, -468, -1504], ![774, 438, 34, -567, -414], ![980, 499, 308, -194, -975]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [23, 89, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [20, 108], [0, 1]]
 g := ![![[56, 36], [25], [24, 105], [61, 108], [102], [20, 1]], ![[13, 73], [25], [53, 4], [41, 1], [102], [40, 108]]]
 h' := ![![[20, 108], [19, 103], [102, 5], [14, 66], [83, 76], [85, 50], [0, 1]], ![[0, 1], [8, 6], [93, 104], [26, 43], [77, 33], [104, 59], [20, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [92]]
 b := ![[], [85, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [23, 89, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![107543, -66506, -59222, 51036, 159723]
  a := ![17, -58, -22, -45, 58]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-172411, -79411, -59222, 51036, 159723]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -1, 1, 0, -2]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![-1, -1, 1, 0, -2]] 
 ![![109, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![73, 0, 1, 0, 0], ![105, 0, 0, 1, 0], ![34, 0, 0, 0, 1]] where
  M :=![![![-1, -1, 1, 0, -2], ![8, 0, -5, 2, 8], ![-24, 5, 4, -2, -4], ![0, -11, 7, -1, -10], ![-8, 6, -2, 0, 3]]]
  hmulB := by decide  
  f := ![![![19, -1, 11, -24, -50]], ![![2, 0, 1, -2, -4]], ![![15, 0, 9, -18, -38]], ![![23, 0, 12, -25, -52]], ![![6, 0, 4, -8, -17]]]
  g := ![![![0, -1, 1, 0, -2], ![-1, 0, -5, 2, 8], ![0, 5, 4, -2, -4], ![0, -11, 7, -1, -10], ![0, 6, -2, 0, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1

def I109N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-27, 8, 6, -2, -18]] i)))

def SI109N2: IdealEqSpanCertificate' Table ![![-27, 8, 6, -2, -18]] 
 ![![109, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![59, 0, 0, 1, 0], ![69, 0, 0, 0, 1]] where
  M :=![![![-27, 8, 6, -2, -18], ![64, -23, -16, 4, 44], ![-160, 52, 41, -16, -120], ![176, -56, -38, 7, 106], ![-144, 48, 36, -12, -103]]]
  hmulB := by decide  
  f := ![![![-23, -80, 70, -10, -122]], ![![2, -7, 4, 0, -8]], ![![-11, -4, 7, -2, -10]], ![![-17, -48, 44, -7, -76]], ![![-15, -48, 42, -6, -73]]]
  g := ![![![11, 8, 6, -2, -18], ![-26, -23, -16, 4, 44], ![75, 52, 41, -16, -120], ![-61, -56, -38, 7, 106], ![63, 48, 36, -12, -103]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N2 : Nat.card (O ⧸ I109N2) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N2)

lemma isPrimeI109N2 : Ideal.IsPrime I109N2 := prime_ideal_of_norm_prime hp109.out _ NI109N2

def I109N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, -16, 10, -2, -12]] i)))

def SI109N3: IdealEqSpanCertificate' Table ![![7, -16, 10, -2, -12]] 
 ![![109, 0, 0, 0, 0], ![101, 1, 0, 0, 0], ![45, 0, 1, 0, 0], ![75, 0, 0, 1, 0], ![26, 0, 0, 0, 1]] where
  M :=![![![7, -16, 10, -2, -12], ![40, 15, -28, 12, 20], ![-32, 24, -17, -8, 88], ![-212, -36, 138, -39, -242], ![100, 16, -68, 16, 139]]]
  hmulB := by decide  
  f := ![![![2611, 744, 1210, -1466, -3200]], ![![2483, 711, 1150, -1390, -3036]], ![![1235, 368, 569, -674, -1480]], ![![1945, 580, 896, -1061, -2330]], ![![658, 192, 304, -364, -797]]]
  g := ![![![15, -16, 10, -2, -12], ![-15, 15, -28, 12, 20], ![-31, 24, -17, -8, 88], ![59, -36, 138, -39, -242], ![-30, 16, -68, 16, 139]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N3 : Nat.card (O ⧸ I109N3) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N3)

lemma isPrimeI109N3 : Ideal.IsPrime I109N3 := prime_ideal_of_norm_prime hp109.out _ NI109N3
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![-359, -40, -12, 0, -73]] ![![-1, -1, 1, 0, -2]]
  ![![911, -139, -61, -56, 227]] where
 M := ![![![911, -139, -61, -56, 227]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![911, -139, -61, -56, 227]] ![![-27, 8, 6, -2, -18]]
  ![![-66277, 21345, 15489, -4518, -44511]] where
 M := ![![![-66277, 21345, 15489, -4518, -44511]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI109N2 : IdealMulLeCertificate' Table 
  ![![-66277, 21345, 15489, -4518, -44511]] ![![7, -16, 10, -2, -12]]
  ![![109, 0, 0, 0, 0]] where
 M := ![![![-3599071, 1202815, 879521, -271192, -2508417]]]
 hmul := by decide  
 g := ![![![![-33019, 11035, 8069, -2488, -23013]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N1, I109N2, I109N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N1
    exact isPrimeI109N2
    exact isPrimeI109N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0 ⊙ MulI109N1 ⊙ MulI109N2)
instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-607, 111, -99, 284, 409]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![-607, 111, -99, 284, 409]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![0, 0, 113, 0, 0], ![0, 0, 0, 113, 0], ![22, 71, 68, 88, 1]] where
  M :=![![![-607, 111, -99, 284, 409], ![-500, -422, -775, 938, 2340], ![-5608, -337, -1370, 2202, 3772], ![-2890, -2177, -2615, 2565, 6700], ![-2550, 266, -54, 422, 69]]]
  hmulB := by decide  
  f := ![![![-89, 71, -25, -6, 69]], ![![-300, -120, 245, -74, -360]], ![![1144, -129, -396, 194, 404]], ![![-270, 531, -365, 29, 730]], ![![276, 272, -373, 92, 597]]]
  g := ![![![-85, -256, -247, -316, 409], ![-460, -1474, -1415, -1814, 2340], ![-784, -2373, -2282, -2918, 3772], ![-1330, -4229, -4055, -5195, 6700], ![-36, -41, -42, -50, 69]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 4 2 6 [63, 3, 79, 41, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [30, 39, 78, 62], [0, 47, 29, 19], [42, 26, 6, 32], [0, 1]]
 g := ![![[91, 81, 92, 109], [5, 48, 77], [8, 84, 100], [52, 85, 36], [43, 20, 72, 1], []], ![[57, 47, 96, 94, 7, 49], [2, 28, 36], [4, 31, 18], [12, 88, 53], [58, 98, 70, 18, 75, 9], [91, 61, 47, 66, 17, 11]], ![[37, 78, 57, 55, 26, 90], [13, 40, 36], [90, 44, 25], [99, 37, 99], [60, 82, 81, 37, 1, 68], [73, 69, 16, 22, 31, 79]], ![[70, 15, 1, 23, 85, 100], [49, 39, 95], [73, 112, 60], [2, 35, 109], [53, 43, 54, 12, 37, 41], [81, 87, 30, 39, 95, 111]]]
 h' := ![![[30, 39, 78, 62], [68, 43, 69, 83], [48, 58, 23, 23], [10, 54, 62, 103], [3, 80, 30, 107], [0, 0, 0, 1], [0, 1]], ![[0, 47, 29, 19], [40, 75, 64, 84], [36, 68, 50, 6], [66, 107, 76, 40], [12, 91, 102, 77], [23, 49, 78, 36], [30, 39, 78, 62]], ![[42, 26, 6, 32], [71, 1, 80, 38], [41, 45, 51, 6], [93, 33, 40, 108], [62, 57, 41, 72], [34, 67, 24, 42], [0, 47, 29, 19]], ![[0, 1], [52, 107, 13, 21], [38, 55, 102, 78], [111, 32, 48, 88], [89, 111, 53, 83], [55, 110, 11, 34], [42, 26, 6, 32]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [61, 41, 18], []]
 b := ![[], [], [102, 64, 106, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 4
  hpos := by decide
  P := [63, 3, 79, 41, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2436171, 2766, 1253018, -1922340, -4082320]
  a := ![-7, -5, 10, -11, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![816347, 2565022, 2467706, 3162140, -4082320]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 163047361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-89, 71, -25, -6, 69]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![-89, 71, -25, -6, 69]] 
 ![![113, 0, 0, 0, 0], ![15, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![98, 0, 0, 1, 0], ![20, 0, 0, 0, 1]] where
  M :=![![![-89, 71, -25, -6, 69], ![-300, -120, 245, -74, -360], ![1144, -129, -396, 194, 404], ![-270, 531, -365, 29, 730], ![414, -262, 54, 38, -209]]]
  hmulB := by decide  
  f := ![![![-607, 111, -99, 284, 409]], ![![-85, 11, -20, 46, 75]], ![![-55, -2, -13, 22, 37]], ![![-552, 77, -109, 269, 414]], ![![-130, 22, -18, 54, 73]]]
  g := ![![![-17, 71, -25, -6, 69], ![139, -120, 245, -74, -360], ![-209, -129, -396, 194, 404], ![-224, 531, -365, 29, 730], ![42, -262, 54, 38, -209]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![-607, 111, -99, 284, 409]] ![![-89, 71, -25, -6, 69]]
  ![![113, 0, 0, 0, 0]] where
 M := ![![![113, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-213, 25, 73, -36, -74]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![-213, 25, 73, -36, -74]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![52, 23, 1, 0, 0], ![37, 16, 0, 1, 0], ![7, 18, 0, 0, 1]] where
  M :=![![![-213, 25, 73, -36, -74], ![152, -176, 93, 2, -208], ![840, 247, -604, 194, 860], ![-1408, 303, 355, -217, -258], ![824, -66, -310, 144, 335]]]
  hmulB := by decide  
  f := ![![![157, 107, 93, -68, -190]], ![![488, 182, 135, -86, -192]], ![![156, 81, 65, -44, -116]], ![![111, 56, 44, -29, -76]], ![![77, 33, 25, -16, -39]]]
  g := ![![![-17, 2, 73, -36, -74], ![-26, 11, 93, 2, -208], ![150, -35, -604, 194, 860], ![-79, 2, 355, -217, -258], ![73, -10, -310, 144, 335]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [22, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [121, 126], [0, 1]]
 g := ![![[58, 52], [120, 35], [49, 69], [11, 68], [107, 69], [121, 1]], ![[0, 75], [37, 92], [16, 58], [111, 59], [74, 58], [115, 126]]]
 h' := ![![[121, 126], [27, 68], [65, 110], [12, 14], [59, 24], [5, 14], [0, 1]], ![[0, 1], [0, 59], [40, 17], [55, 113], [42, 103], [48, 113], [121, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [88]]
 b := ![[], [5, 44]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [22, 6, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-33703, -6316, -19547, 21516, 50268]
  a := ![31, 27, -42, 50, 108]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1301, -6345, -19547, 21516, 50268]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 7, -13, 4, 20]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![13, 7, -13, 4, 20]] 
 ![![127, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![46, 0, 1, 0, 0], ![106, 0, 0, 1, 0], ![57, 0, 0, 0, 1]] where
  M :=![![![13, 7, -13, 4, 20], ![-64, 4, 23, -10, -24], ![56, -51, 16, 6, -44], ![132, 37, -99, 33, 142], ![-44, -30, 46, -12, -71]]]
  hmulB := by decide  
  f := ![![![-2109, 717, 535, -180, -1528]], ![![-107, 37, 28, -10, -80]], ![![-866, 295, 220, -74, -628]], ![![-1650, 563, 421, -143, -1202]], ![![-1039, 353, 263, -88, -751]]]
  g := ![![![-8, 7, -13, 4, 20], ![10, 4, 23, -10, -24], ![13, -51, 16, 6, -44], ![-57, 37, -99, 33, 142], ![27, -30, 46, -12, -71]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1

def I127N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, 9, -5, 0, 11]] i)))

def SI127N2: IdealEqSpanCertificate' Table ![![-7, 9, -5, 0, 11]] 
 ![![127, 0, 0, 0, 0], ![109, 1, 0, 0, 0], ![57, 0, 1, 0, 0], ![14, 0, 0, 1, 0], ![40, 0, 0, 0, 1]] where
  M :=![![![-7, 9, -5, 0, 11], ![-44, -12, 31, -10, -44], ![136, -23, -40, 22, 36], ![-6, 65, -57, 9, 104], ![38, -34, 14, 2, -35]]]
  hmulB := by decide  
  f := ![![![249, 71, 59, -46, -87]], ![![215, 63, 52, -40, -77]], ![![119, 34, 27, -20, -37]], ![![24, 11, 7, -3, -8]], ![![82, 22, 18, -14, -25]]]
  g := ![![![-9, 9, -5, 0, 11], ![11, -12, 31, -10, -44], ![25, -23, -40, 22, 36], ![-64, 65, -57, 9, 104], ![34, -34, 14, 2, -35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N2 : Nat.card (O ⧸ I127N2) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N2)

lemma isPrimeI127N2 : Ideal.IsPrime I127N2 := prime_ideal_of_norm_prime hp127.out _ NI127N2

def I127N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-787, -506, -306, 102, 376]] i)))

def SI127N3: IdealEqSpanCertificate' Table ![![-787, -506, -306, 102, 376]] 
 ![![127, 0, 0, 0, 0], ![113, 1, 0, 0, 0], ![58, 0, 1, 0, 0], ![32, 0, 0, 1, 0], ![49, 0, 0, 0, 1]] where
  M :=![![![-787, -506, -306, 102, 376], ![-1096, -991, -366, -204, -76], ![-512, -1666, 81, -1548, -2552], ![2556, -494, 1442, -2913, -5694], ![148, -280, 136, -472, -855]]]
  hmulB := by decide  
  f := ![![![5635, -74, -2490, 1026, 3084]], ![![4949, -33, -2216, 906, 2760]], ![![2482, -106, -1031, 440, 1248]], ![![1716, -42, -738, 311, 890]], ![![2025, -38, -886, 366, 1101]]]
  g := ![![![413, -506, -306, 102, 376], ![1121, -991, -366, -204, -76], ![2816, -1666, 81, -1548, -2552], ![2732, -494, 1442, -2913, -5694], ![637, -280, 136, -472, -855]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N3 : Nat.card (O ⧸ I127N3) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N3)

lemma isPrimeI127N3 : Ideal.IsPrime I127N3 := prime_ideal_of_norm_prime hp127.out _ NI127N3
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![-213, 25, 73, -36, -74]] ![![13, 7, -13, 4, 20]]
  ![![-1777, -4226, 4672, -964, -7930]] where
 M := ![![![-1777, -4226, 4672, -964, -7930]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![-1777, -4226, 4672, -964, -7930]] ![![-7, 9, -5, 0, 11]]
  ![![538219, 134223, -365073, 120508, 511883]] where
 M := ![![![538219, 134223, -365073, 120508, 511883]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI127N2 : IdealMulLeCertificate' Table 
  ![![538219, 134223, -365073, 120508, 511883]] ![![-787, -506, -306, 102, 376]]
  ![![127, 0, 0, 0, 0]] where
 M := ![![![7747, -381, -2921, 1270, 3175]]]
 hmul := by decide  
 g := ![![![![61, -3, -23, 10, 25]]]]
 hle2 := by decide  


def PBC127 : ContainsPrimesAboveP 127 ![I127N0, I127N1, I127N2, I127N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
    exact isPrimeI127N1
    exact isPrimeI127N2
    exact isPrimeI127N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 127 (by decide) (𝕀 ⊙ MulI127N0 ⊙ MulI127N1 ⊙ MulI127N2)
instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2505, 342, 810, -418, -766]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![-2505, 342, 810, -418, -766]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![0, 0, 131, 0, 0], ![0, 0, 0, 131, 0], ![104, 4, 106, 97, 1]] where
  M :=![![![-2505, 342, 810, -418, -766], ![1392, -2113, 1318, -52, -2788], ![10944, 2658, -7377, 2428, 10424], ![-16688, 4054, 3810, -2495, -2458], ![10064, -1064, -3568, 1708, 3795]]]
  hmulB := by decide  
  f := ![![![-203, -98, -86, 66, 166]], ![![-400, -223, -162, 92, 260]], ![![-672, -470, -255, 44, 248]], ![![-208, -330, -38, -213, -318]], ![![-872, -710, -308, -67, 105]]]
  g := ![![![589, 26, 626, 564, -766], ![2224, 69, 2266, 2064, -2788], ![-8192, -298, -8491, -7700, 10424], ![1824, 106, 2018, 1801, -2458], ![-2936, -124, -3098, -2797, 3795]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 4 2 7 [94, 120, 42, 124, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 54, 127, 49], [81, 102, 93, 109], [45, 105, 42, 104], [0, 1]]
 g := ![![[103, 13, 9, 121], [41, 19, 110, 28], [53, 4, 91], [39, 102, 89], [110, 17, 49], [1], []], ![[117, 53, 38, 92, 95, 27], [97, 16, 114, 105, 86, 44], [25, 66, 74], [28, 0, 34], [52, 115, 58], [0, 127, 89], [114, 40, 43]], ![[103, 30, 47, 120, 96, 105], [87, 44, 24, 45, 98, 125], [119, 71, 45], [86, 117, 44], [125, 65, 5], [52, 87, 107], [127, 82, 91]], ![[58, 14, 35, 62, 39, 87], [59, 32, 82, 100, 1, 90], [58, 10, 105], [126, 66, 46], [78, 61, 59], [77, 39, 109], [124, 84, 74]]]
 h' := ![![[12, 54, 127, 49], [76, 127, 81, 11], [105, 98, 107, 40], [41, 45, 66, 22], [68, 33, 26, 58], [37, 11, 89, 7], [0, 0, 1], [0, 1]], ![[81, 102, 93, 109], [63, 105, 29, 96], [120, 114, 11, 33], [51, 22, 86, 104], [71, 105, 58, 77], [80, 54, 85, 53], [39, 100, 63, 73], [12, 54, 127, 49]], ![[45, 105, 42, 104], [80, 95, 108, 126], [12, 32, 32, 6], [71, 50, 91, 62], [65, 116, 92, 31], [126, 52, 62, 108], [125, 126, 39, 99], [81, 102, 93, 109]], ![[0, 1], [40, 66, 44, 29], [71, 18, 112, 52], [105, 14, 19, 74], [40, 8, 86, 96], [6, 14, 26, 94], [63, 36, 28, 90], [45, 105, 42, 104]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [20, 50, 114], []]
 b := ![[], [], [14, 55, 35, 29], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 4
  hpos := by decide
  P := [94, 120, 42, 124, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![146727425, 111514222, -29560873, -49414199, 95624485]
  a := ![-35, -7, 48, -31, -122]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-74795565, -2068578, -77601193, -71183124, 95624485]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 294499921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-203, -98, -86, 66, 166]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![-203, -98, -86, 66, 166]] 
 ![![131, 0, 0, 0, 0], ![87, 1, 0, 0, 0], ![29, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![105, 0, 0, 0, 1]] where
  M :=![![![-203, -98, -86, 66, 166], ![-400, -223, -162, 92, 260], ![-672, -470, -255, 44, 248], ![-208, -330, -38, -213, -318], ![-112, -96, -40, -12, 9]]]
  hmulB := by decide  
  f := ![![![-2505, 342, 810, -418, -766]], ![![-1653, 211, 548, -278, -530]], ![![-471, 96, 123, -74, -90]], ![![-223, 44, 60, -35, -48]], ![![-1931, 266, 622, -322, -585]]]
  g := ![![![-53, -98, -86, 66, 166], ![-31, -223, -162, 92, 260], ![163, -470, -255, 44, 248], ![489, -330, -38, -213, -318], ![65, -96, -40, -12, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![-2505, 342, 810, -418, -766]] ![![-203, -98, -86, 66, 166]]
  ![![131, 0, 0, 0, 0]] where
 M := ![![![131, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC131 : ContainsPrimesAboveP 131 ![I131N0, I131N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
    exact isPrimeI131N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 131 (by decide) (𝕀 ⊙ MulI131N0)
instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3215, -453, -1031, 532, 988]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![3215, -453, -1031, 532, 988]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![0, 0, 137, 0, 0], ![18, 132, 80, 1, 0], ![83, 95, 70, 0, 1]] where
  M :=![![![3215, -453, -1031, 532, 988], ![-1824, 2716, -1669, 66, 3496], ![-13720, -3427, 9312, -3074, -13060], ![20884, -5099, -4717, 3131, 2854], ![-12556, 1302, 4454, -2148, -4629]]]
  hmulB := by decide  
  f := ![![![-1041, 303, 215, -52, -632]], ![![2320, -878, -649, 222, 1800]], ![![-6312, 1893, 1390, -410, -4092]], ![![-1542, 283, 203, -29, -706]], ![![-2287, 555, 400, -90, -1253]]]
  g := ![![![-645, -1201, -823, 532, 988], ![-2140, -2468, -1837, 66, 3496], ![8216, 11993, 8536, -3074, -13060], ![-1988, -5033, -3321, 3131, 2854], ![2995, 5289, 3652, -2148, -4629]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [59, 45, 11, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [119, 81, 92], [7, 55, 45], [0, 1]]
 g := ![![[63, 41, 11], [18, 68], [57, 118], [4, 30, 14], [133, 22], [126, 1], []], ![[30, 119, 46, 124], [91, 68], [105, 4], [22, 35, 98, 131], [58, 37], [58, 11], [27, 107]], ![[50, 67, 70, 86], [81, 135], [67, 77], [9, 7, 0, 106], [57, 126], [6, 122], [74, 107]]]
 h' := ![![[119, 81, 92], [35, 131, 55], [136, 58, 94], [38, 45, 114], [25, 96, 98], [101, 25, 76], [0, 0, 1], [0, 1]], ![[7, 55, 45], [81, 83, 7], [92, 46, 94], [56, 134, 135], [112, 119, 111], [66, 4, 41], [101, 105, 55], [119, 81, 92]], ![[0, 1], [116, 60, 75], [127, 33, 86], [45, 95, 25], [2, 59, 65], [25, 108, 20], [67, 32, 81], [7, 55, 45]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39], []]
 b := ![[], [6, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [59, 45, 11, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8241431, -1461002, -2970534, 966262, 6225982]
  a := ![28, -2, -38, 10, 98]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3838743, -5258948, -3767082, 966262, 6225982]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 2571353 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1041, 303, 215, -52, -632]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![-1041, 303, 215, -52, -632]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![124, 114, 1, 0, 0], ![56, 72, 0, 1, 0], ![26, 43, 0, 0, 1]] where
  M :=![![![-1041, 303, 215, -52, -632], ![2320, -878, -649, 222, 1800], ![-6312, 1893, 1390, -410, -4092], ![6204, -2227, -1591, 459, 4414], ![-5476, 1786, 1310, -404, -3765]]]
  hmulB := by decide  
  f := ![![![3215, -453, -1031, 532, 988]], ![![-1824, 2716, -1669, 66, 3496]], ![![1292, 1825, -2254, 514, 3708]], ![![508, 1205, -1333, 275, 2262]], ![![-54, 776, -687, 106, 1251]]]
  g := ![![![-61, 49, 215, -52, -632], ![172, -148, -649, 222, 1800], ![-360, 357, 1390, -410, -4092], ![460, -319, -1591, 459, 4414], ![-346, 317, 1310, -404, -3765]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P1 : CertificateIrreducibleZModOfList' 137 2 2 7 [10, 72, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [65, 136], [0, 1]]
 g := ![![[62, 65], [73], [69], [8, 73], [100], [115], [1]], ![[40, 72], [73], [69], [95, 64], [100], [115], [1]]]
 h' := ![![[65, 136], [110, 105], [93, 115], [57, 53], [20, 22], [46, 10], [127, 65], [0, 1]], ![[0, 1], [85, 32], [33, 22], [77, 84], [80, 115], [11, 127], [105, 72], [65, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31]]
 b := ![[], [10, 84]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N1 : CertifiedPrimeIdeal' SI137N1 137 where
  n := 2
  hpos := by decide
  P := [10, 72, 1]
  hirr := P137P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7003, -5430, 1996, 1332, -416]
  a := ![-13, 7, 23, 2, -52]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2221, -2270, 1996, 1332, -416]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N1 B_one_repr
lemma NI137N1 : Nat.card (O ⧸ I137N1) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![3215, -453, -1031, 532, 988]] ![![-1041, 303, 215, -52, -632]]
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

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0, 0, 0]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0, 0, 0]] 
 ![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![0, 0, 139, 0, 0], ![0, 0, 0, 139, 0], ![0, 0, 0, 0, 139]] where
  M :=![![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![0, 0, 139, 0, 0], ![0, 0, 0, 139, 0], ![0, 0, 0, 0, 139]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 5 2 7 [130, 129, 115, 125, 134, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 85, 24, 47, 132], [101, 72, 131, 53, 67], [52, 85, 95, 122, 36], [99, 35, 28, 56, 43], [0, 1]]
 g := ![![[127, 53, 72, 33, 24], [22, 73, 48, 134, 46], [104, 10, 105, 52], [113, 75, 52, 109, 45], [11, 39, 5, 1], [], []], ![[6, 83, 45, 95, 69, 38, 12, 90], [95, 90, 107, 70, 22, 133, 112, 102], [10, 131, 72, 5], [40, 67, 46, 57, 72, 66, 6, 115], [24, 1, 137, 80], [127, 116, 130, 4], [42, 77, 4, 49]], ![[129, 24, 87, 79, 109, 7, 17, 9], [68, 9, 1, 25, 67, 1, 53, 52], [11, 42, 65, 67], [28, 70, 75, 47, 77, 78, 20, 45], [86, 16, 28, 77], [104, 126, 86, 71], [95, 65, 79, 41]], ![[101, 92, 74, 81, 9, 10, 130, 112], [78, 12, 104, 2, 138, 86, 137, 116], [133, 135, 7, 96], [66, 94, 12, 99, 47, 19, 133, 54], [21, 104, 45, 91], [105, 53, 127, 36], [51, 123, 113, 45]], ![[110, 46, 95, 118, 66, 63, 4, 119], [36, 91, 82, 90, 126, 127, 40, 135], [69, 90, 138, 55], [101, 130, 55, 119, 61, 122, 110, 39], [36, 21, 41, 107], [5, 58, 10, 129], [30, 126, 22, 42]]]
 h' := ![![[31, 85, 24, 47, 132], [59, 28, 103, 12, 118], [92, 113, 41, 90, 18], [44, 69, 132, 105, 82], [99, 44, 4, 37, 36], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[101, 72, 131, 53, 67], [59, 57, 137, 95, 110], [8, 126, 119, 51, 103], [14, 73, 73, 112, 12], [19, 117, 29, 91, 87], [130, 100, 99, 65, 91], [88, 128, 102, 42, 137], [31, 85, 24, 47, 132]], ![[52, 85, 95, 122, 36], [55, 113, 64, 59, 82], [17, 8, 128, 50, 29], [125, 37, 40, 76, 22], [29, 91, 48, 49, 128], [28, 11, 91, 113, 63], [75, 94, 120, 120, 40], [101, 72, 131, 53, 67]], ![[99, 35, 28, 56, 43], [124, 7, 6, 65, 27], [71, 33, 137, 81, 75], [79, 58, 56, 47, 97], [28, 116, 92, 108, 40], [16, 46, 80, 120, 62], [105, 32, 4, 123, 6], [52, 85, 95, 122, 36]], ![[0, 1], [95, 73, 107, 47, 80], [71, 137, 131, 6, 53], [80, 41, 116, 77, 65], [57, 49, 105, 132, 126], [122, 121, 8, 119, 61], [63, 24, 51, 132, 95], [99, 35, 28, 56, 43]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50, 127, 89, 60], [], [], []]
 b := ![[], [28, 13, 80, 104, 88], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 5
  hpos := by decide
  P := [130, 129, 115, 125, 134, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7661126502, -2815776793, -1722007477, 483254072, 5552844558]
  a := ![13, -1, -18, 8, 46]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![55116018, -20257387, -12388543, 3476648, 39948522]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0, 0, 0]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0, 0, 0]] 
 ![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![0, 0, 149, 0, 0], ![0, 0, 0, 149, 0], ![0, 0, 0, 0, 149]] where
  M :=![![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![0, 0, 149, 0, 0], ![0, 0, 0, 149, 0], ![0, 0, 0, 0, 149]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 5 2 7 [70, 30, 147, 94, 107, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [123, 78, 23, 20, 108], [120, 64, 132, 47, 112], [51, 47, 69, 74, 96], [46, 108, 74, 8, 131], [0, 1]]
 g := ![![[77, 125, 76, 10, 100], [59, 70, 119, 120], [75, 51, 63, 39, 124], [131, 34, 46, 46], [77, 38, 31, 42, 1], [], []], ![[9, 136, 136, 59, 46, 25, 34, 59], [116, 143, 3, 19], [126, 110, 65, 32, 5, 31, 129, 21], [87, 0, 17, 33], [134, 66, 18, 80, 94, 103, 105, 91], [117, 114, 46, 114], [131, 72, 124, 42]], ![[119, 78, 99, 1, 19, 36, 89, 9], [111, 89, 135, 73], [44, 79, 79, 126, 59, 85, 79, 26], [7, 73, 9, 132], [102, 86, 79, 103, 126, 129, 32, 42], [71, 7, 49, 144], [44, 107, 82, 28]], ![[87, 13, 21, 33, 1, 57, 108, 129], [114, 10, 143, 63], [141, 127, 53, 51, 90, 126, 115, 22], [125, 117, 108, 7], [107, 127, 102, 108, 77, 34, 119, 54], [110, 36, 78, 17], [63, 4, 23, 127]], ![[99, 32, 85, 76, 68, 11, 50, 48], [47, 145, 14, 45], [75, 103, 72, 48, 101, 93, 87, 65], [48, 119, 64, 107], [127, 12, 89, 72, 148, 105, 50, 32], [57, 109, 93, 144], [101, 116, 59, 26]]]
 h' := ![![[123, 78, 23, 20, 108], [75, 148, 4, 135, 139], [114, 141, 126, 68, 92], [148, 22, 86, 36, 71], [123, 96, 122, 143, 33], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[120, 64, 132, 47, 112], [100, 52, 89, 31, 60], [144, 106, 77, 53, 67], [52, 39, 127, 10, 90], [114, 92, 128, 60, 114], [6, 109, 3, 19, 95], [148, 86, 121, 108, 76], [123, 78, 23, 20, 108]], ![[51, 47, 69, 74, 96], [146, 48, 67, 114, 143], [82, 124, 11, 97, 64], [2, 32, 69, 144, 36], [94, 57, 63, 130, 79], [112, 110, 107, 45, 82], [145, 143, 94, 17, 12], [120, 64, 132, 47, 112]], ![[46, 108, 74, 8, 131], [70, 16, 143, 80, 119], [147, 9, 146, 109, 130], [10, 87, 67, 119, 65], [77, 81, 1, 1, 56], [42, 43, 113, 102, 111], [128, 91, 44, 30, 49], [51, 47, 69, 74, 96]], ![[0, 1], [14, 34, 144, 87, 135], [131, 67, 87, 120, 94], [143, 118, 98, 138, 36], [15, 121, 133, 113, 16], [61, 36, 75, 132, 9], [112, 127, 38, 143, 12], [46, 108, 74, 8, 131]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [114, 118, 101, 16], [], [], []]
 b := ![[], [49, 27, 110, 142, 44], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 5
  hpos := by decide
  P := [70, 30, 147, 94, 107, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![395101306827, 14844956420, 77975120146, -155250543891, -227981480152]
  a := ![45, 13, -59, 47, 156]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2651686623, 99630580, 523322954, -1041949959, -1530077048]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 73439775749 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def PBC149 : ContainsPrimesAboveP 149 ![I149N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![149, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 149 (by decide) 𝕀

instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-435, -84, -210, 292, 616]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![-435, -84, -210, 292, 616]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![0, 0, 151, 0, 0], ![88, 96, 69, 1, 0], ![100, 73, 40, 0, 1]] where
  M :=![![![-435, -84, -210, 292, 616], ![-1296, -353, -604, 748, 1624], ![-3504, -1152, -1593, 1784, 3976], ![-3736, -1480, -1650, 1601, 3724], ![-824, -292, -368, 392, 885]]]
  hmulB := by decide  
  f := ![![![-77, 4, 34, -12, -56]], ![![176, -55, -36, 20, 56]], ![![-144, 160, -63, 8, 56]], ![![0, 40, -31, 9, 28]], ![![-4, 19, -12, 4, 5]]]
  g := ![![![-581, -484, -298, 292, 616], ![-1520, -1263, -776, 748, 1624], ![-3696, -3064, -1879, 1784, 3976], ![-3424, -2828, -1729, 1601, 3724], ![-820, -679, -416, 392, 885]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [110, 84, 112, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [86, 25, 48], [104, 125, 103], [0, 1]]
 g := ![![[131, 57, 25], [58, 98, 123], [90, 50, 116], [21, 139], [23, 37, 44], [39, 1], []], ![[82, 103, 67, 142], [122, 17, 11, 3], [46, 89, 73, 149], [91, 116], [22, 126, 58, 71], [78, 72], [146, 39]], ![[57, 69, 90, 69], [136, 97, 64, 105], [69, 78, 41, 20], [70, 40], [116, 43, 99, 76], [6, 21], [91, 39]]]
 h' := ![![[86, 25, 48], [113, 29, 5], [66, 94, 24], [116, 75, 95], [37, 107, 130], [89, 87, 78], [0, 0, 1], [0, 1]], ![[104, 125, 103], [57, 6, 54], [138, 137, 113], [94, 143, 73], [17, 138, 95], [105, 79, 34], [94, 128, 125], [86, 25, 48]], ![[0, 1], [62, 116, 92], [43, 71, 14], [77, 84, 134], [128, 57, 77], [129, 136, 39], [51, 23, 25], [104, 125, 103]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [125, 142], []]
 b := ![[], [28, 1, 104], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [110, 84, 112, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-112667, -432108, -188049, 181892, 584466]
  a := ![19, 5, -26, 18, 66]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-493813, -401058, -239187, 181892, 584466]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 3442951 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![77, -4, -34, 12, 56]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![77, -4, -34, 12, 56]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![124, 13, 1, 0, 0], ![100, 129, 0, 1, 0], ![4, 115, 0, 0, 1]] where
  M :=![![![77, -4, -34, 12, 56], ![-176, 55, 36, -20, -56], ![144, -160, 63, -8, -56], ![184, 72, -130, 57, 84], ![-8, -84, 64, -24, -27]]]
  hmulB := by decide  
  f := ![![![435, 84, 210, -292, -616]], ![![1296, 353, 604, -748, -1624]], ![![492, 107, 235, -316, -672]], ![![1420, 367, 666, -843, -1820]], ![![1004, 273, 468, -580, -1259]]]
  g := ![![![19, -50, -34, 12, 56], ![-16, 57, 36, -20, -56], ![-44, 43, 63, -8, -56], ![68, -101, -130, 57, 84], ![-36, 35, 64, -24, -27]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P1 : CertificateIrreducibleZModOfList' 151 2 2 7 [127, 100, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [51, 150], [0, 1]]
 g := ![![[21, 44], [23, 99], [61, 145], [19], [86, 2], [34], [1]], ![[0, 107], [89, 52], [57, 6], [19], [37, 149], [34], [1]]]
 h' := ![![[51, 150], [99, 78], [105, 117], [87, 121], [101, 87], [33, 105], [24, 51], [0, 1]], ![[0, 1], [0, 73], [32, 34], [67, 30], [8, 64], [103, 46], [58, 100], [51, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [144]]
 b := ![[], [127, 72]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N1 : CertifiedPrimeIdeal' SI151N1 151 where
  n := 2
  hpos := by decide
  P := [127, 100, 1]
  hirr := P151P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![611, -238, 193, 605, -155]
  a := ![-2, 3, 4, 3, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-551, -417, 193, 605, -155]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N1 B_one_repr
lemma NI151N1 : Nat.card (O ⧸ I151N1) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![-435, -84, -210, 292, 616]] ![![77, -4, -34, 12, 56]]
  ![![151, 0, 0, 0, 0]] where
 M := ![![![-151, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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


lemma PB229I3_primes (p : ℕ) :
  p ∈ Set.range ![107, 109, 113, 127, 131, 137, 139, 149, 151] ↔ Nat.Prime p ∧ 103 < p ∧ p ≤ 151 := by
  rw [← List.mem_ofFn']
  convert primes_range 103 151 (by omega)

def PB229I3 : PrimesBelowBoundCertificateInterval O 103 151 229 where
  m := 9
  g := ![2, 4, 2, 4, 2, 2, 1, 1, 2]
  P := ![107, 109, 113, 127, 131, 137, 139, 149, 151]
  hP := PB229I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1, I109N2, I109N3]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1, I127N2, I127N3]
    · exact ![I131N0, I131N1]
    · exact ![I137N0, I137N1]
    · exact ![I139N0]
    · exact ![I149N0]
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
    · exact ![131079601, 107]
    · exact ![11881, 109, 109, 109]
    · exact ![163047361, 113]
    · exact ![16129, 127, 127, 127]
    · exact ![294499921, 131]
    · exact ![2571353, 18769]
    · exact ![51888844699]
    · exact ![73439775749]
    · exact ![3442951, 22801]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
      exact NI109N2
      exact NI109N3
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
      exact NI127N2
      exact NI127N3
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
  β := ![I107N1, I109N1, I109N2, I109N3, I113N1, I127N1, I127N2, I127N3, I131N1]
  Il := ![[I107N1], [I109N1, I109N2, I109N3], [I113N1], [I127N1, I127N2, I127N3], [I131N1], [], [], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
