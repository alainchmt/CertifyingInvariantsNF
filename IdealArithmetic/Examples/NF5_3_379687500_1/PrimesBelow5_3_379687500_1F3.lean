
import IdealArithmetic.Examples.NF5_3_379687500_1.RI5_3_379687500_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9, -22, -7, 7, 14]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![-9, -22, -7, 7, 14]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![11, 56, 1, 0, 0], ![26, 85, 0, 1, 0], ![53, 68, 0, 0, 1]] where
  M :=![![![-9, -22, -7, 7, 14], ![0, -2, -15, 28, 56], ![0, 28, 26, 125, 224], ![-26, 125, 179, 807, 1442], ![6, -35, -48, -211, -377]]]
  hmulB := by decide  
  f := ![![![-403, 175, -727, 326, 826]], ![![174, -77, 327, -141, -350]], ![![49, -22, 95, -40, -98]], ![![40, -19, 84, -31, -70]], ![![-89, 38, -153, 71, 183]]]
  g := ![![![-8, -11, -7, 7, 14], ![-33, -50, -15, 28, 56], ![-144, -255, 26, 125, 224], ![-929, -1650, 179, 807, 1442], ![243, 432, -48, -211, -377]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [22, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [100, 106], [0, 1]]
 g := ![![[83, 29], [67, 14], [56], [102, 9], [87], [100, 1]], ![[94, 78], [76, 93], [56], [39, 98], [87], [93, 106]]]
 h' := ![![[100, 106], [24, 55], [61, 11], [3, 85], [81, 3], [47, 27], [0, 1]], ![[0, 1], [67, 52], [91, 96], [50, 22], [60, 104], [72, 80], [100, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44]]
 b := ![[], [77, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [22, 7, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-18112, 18162, 39276, 196796, 442890]
  a := ![5, -3, -9, -44, -105]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-271402, -458182, 39276, 196796, 442890]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-403, 175, -727, 326, 826]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![-403, 175, -727, 326, 826]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![0, 0, 107, 0, 0], ![9, 89, 51, 1, 0], ![72, 9, 47, 0, 1]] where
  M :=![![![-403, 175, -727, 326, 826], ![174, -77, 327, -141, -350], ![-68, 33, -150, 30, 28], ![-32, -38, 95, 192, 784], ![4, 27, -76, -93, -397]]]
  hmulB := by decide  
  f := ![![![-9, -22, -7, 7, 14]], ![![0, -2, -15, 28, 56]], ![![0, 28, 26, 125, 224]], ![![-1, 11, 1, 91, 168]], ![![-6, -3, 5, 60, 109]]]
  g := ![![![-587, -339, -525, 326, 826], ![249, 146, 224, -141, -350], ![-22, -27, -28, 30, 28], ![-544, -226, -435, 192, 784], ![275, 111, 218, -93, -397]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P1 : CertificateIrreducibleZModOfList' 107 3 2 6 [5, 83, 8, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [57, 60, 103], [42, 46, 4], [0, 1]]
 g := ![![[10, 82, 1], [65, 17, 16], [92, 1], [99, 60, 33], [67, 64], [1]], ![[73, 12, 94, 80], [17, 45, 84, 26], [83, 69], [26, 51, 12, 80], [9, 12], [48, 93, 75, 43]], ![[97, 86, 21, 29], [106, 105, 76, 75], [45, 83], [80, 99, 53, 57], [5, 10], [90, 75, 91, 64]]]
 h' := ![![[57, 60, 103], [103, 62, 106], [70, 22, 103], [40, 57, 106], [11, 85, 51], [102, 24, 99], [0, 1]], ![[42, 46, 4], [23, 103, 27], [29, 13, 49], [103, 17, 47], [101, 70, 80], [57, 3, 71], [57, 60, 103]], ![[0, 1], [3, 49, 81], [22, 72, 62], [51, 33, 61], [31, 59, 83], [22, 80, 44], [42, 46, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20, 35], []]
 b := ![[], [94, 77, 89], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N1 : CertifiedPrimeIdeal' SI107N1 107 where
  n := 3
  hpos := by decide
  P := [5, 83, 8, 1]
  hirr := P107P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![107809972769, -211006189459, -356621211803, -1740438552574, -3509728432224]
  a := ![59, -60, -118, -533, -1236]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2509086019309, 1740893279249, 2367878329757, -1740438552574, -3509728432224]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N1 B_one_repr
lemma NI107N1 : Nat.card (O ⧸ I107N1) = 1225043 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![-9, -22, -7, 7, 14]] ![![-403, 175, -727, 326, 826]]
  ![![107, 0, 0, 0, 0]] where
 M := ![![![107, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1019, 425, -1862, 805, 2064]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![-1019, 425, -1862, 805, 2064]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![0, 0, 109, 0, 0], ![84, 85, 89, 1, 0], ![89, 60, 37, 0, 1]] where
  M :=![![![-1019, 425, -1862, 805, 2064], ![454, -214, 776, -561, -1278], ![-156, -107, -619, -1093, -1836], ![350, -1249, -1550, -8184, -14694], ![-150, 352, 300, 2192, 3971]]]
  hmulB := by decide  
  f := ![![![1, -27, -56, 3, -24]], ![![-30, 4, 6, 139, 534]], ![![256, 109, -113, -835, -3240]], ![![172, 66, -123, -524, -2064]], ![![79, 20, -85, -230, -925]]]
  g := ![![![-2315, -1760, -1375, 805, 2064], ![1480, 1139, 899, -561, -1278], ![2340, 1862, 1510, -1093, -1836], ![18308, 14459, 11656, -8184, -14694], ![-4933, -3892, -3135, 2192, 3971]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [5, 37, 67, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 20, 16], [20, 88, 93], [0, 1]]
 g := ![![[61, 51, 22], [103, 78], [101, 54, 78], [99, 9, 1], [21, 20], [1]], ![[8, 27, 84, 48], [2, 46], [87, 10, 83, 28], [64, 80, 59, 102], [46, 88], [13, 94, 21, 63]], ![[9, 50, 80, 34], [93, 35], [99, 61, 71, 48], [48, 77, 83, 64], [105, 7], [14, 9, 83, 46]]]
 h' := ![![[22, 20, 16], [104, 44, 26], [40, 19, 80], [50, 76, 29], [29, 38, 1], [104, 72, 42], [0, 1]], ![[20, 88, 93], [54, 46, 49], [101, 19, 41], [8, 28, 62], [88, 32, 42], [10, 76, 52], [22, 20, 16]], ![[0, 1], [53, 19, 34], [54, 71, 97], [83, 5, 18], [95, 39, 66], [82, 70, 15], [20, 88, 93]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47, 21], []]
 b := ![[], [29, 15, 60], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [5, 37, 67, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![30488897, -64073331, -106110459, -516561516, -1030000131]
  a := ![4, -3, -7, -36, -83]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1239373100, 969207921, 770439168, -516561516, -1030000131]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 1295029 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, -15, -5, 8, 26]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![-7, -15, -5, 8, 26]] 
 ![![109, 0, 0, 0, 0], ![42, 1, 0, 0, 0], ![89, 0, 1, 0, 0], ![77, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  M :=![![![-7, -15, -5, 8, 26], ![10, 1, -17, -25, -106], ![-56, -15, 32, 194, 752], ![364, 138, -185, -1182, -4636], ![-198, -75, 102, 645, 2521]]]
  hmulB := by decide  
  f := ![![![-1058191, 440874, -1922507, 865037, 2193686]], ![![-403490, 168106, -733055, 329840, 836456]], ![![-865891, 360756, -1573139, 707838, 1795038]], ![![-746713, 311103, -1356618, 610414, 1547976]], ![![-88143, 36723, -160137, 72054, 182725]]]
  g := ![![![2, -15, -5, 8, 26], ![40, 1, -17, -25, -106], ![-220, -15, 32, 194, 752], ![1319, 138, -185, -1182, -4636], ![-720, -75, 102, 645, 2521]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1

def I109N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, -58, 253, -113, -286]] i)))

def SI109N2: IdealEqSpanCertificate' Table ![![139, -58, 253, -113, -286]] 
 ![![109, 0, 0, 0, 0], ![87, 1, 0, 0, 0], ![61, 0, 1, 0, 0], ![34, 0, 0, 1, 0], ![91, 0, 0, 0, 1]] where
  M :=![![![139, -58, 253, -113, -286], ![-60, 26, -111, 48, 116], ![20, -12, 54, 9, 44], ![26, 29, -29, -57, -370], ![-10, -15, 28, 45, 223]]]
  hmulB := by decide  
  f := ![![![-5457, -11863, 2003, -578, -2182]], ![![-4365, -9524, 1494, -413, -1624]], ![![-3033, -6600, 1093, -312, -1190]], ![![-1694, -3668, 667, -200, -728]], ![![-4563, -9924, 1661, -477, -1809]]]
  g := ![![![180, -58, 253, -113, -286], ![-71, 26, -111, 48, 116], ![-60, -12, 54, 9, 44], ![320, 29, -29, -57, -370], ![-204, -15, 28, 45, 223]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N2 : Nat.card (O ⧸ I109N2) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N2)

lemma isPrimeI109N2 : Ideal.IsPrime I109N2 := prime_ideal_of_norm_prime hp109.out _ NI109N2
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![-1019, 425, -1862, 805, 2064]] ![![-7, -15, -5, 8, 26]]
  ![![3, -70, -111, -235, -404]] where
 M := ![![![3, -70, -111, -235, -404]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![3, -70, -111, -235, -404]] ![![139, -58, 253, -113, -286]]
  ![![109, 0, 0, 0, 0]] where
 M := ![![![327, -1417, -1962, -9483, -17004]]]
 hmul := by decide  
 g := ![![![![3, -13, -18, -87, -156]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![57, 12, -405, 181, 454]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![57, 12, -405, 181, 454]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![0, 0, 113, 0, 0], ![77, 91, 104, 1, 0], ![66, 76, 47, 0, 1]] where
  M :=![![![57, 12, -405, 181, 454], ![92, 238, 101, -52, -116], ![-12, 40, 198, -87, -212], ![-38, -99, -9, -9, -50], ![16, 31, -34, 23, 71]]]
  hmulB := by decide  
  f := ![![![-15, 7, -27, 16, 38]], ![![6, 1, 17, 17, 26]], ![![-8, 23, 26, 150, 272]], ![![-13, 28, 21, 171, 312]], ![![-8, 14, 6, 81, 149]]]
  g := ![![![-388, -451, -359, 181, 454], ![104, 122, 97, -52, -116], ![183, 213, 170, -87, -212], ![35, 40, 29, -9, -50], ![-57, -66, -51, 23, 71]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [94, 95, 63, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [108, 40, 63], [55, 72, 50], [0, 1]]
 g := ![![[83, 93, 111], [45, 1], [48, 32], [46, 36], [12, 14, 14], [1]], ![[42, 50, 82, 112], [82, 50], [14, 81], [102, 22], [62, 98, 79, 32], [7, 43, 15, 91]], ![[25, 80, 0, 88], [31, 106], [4, 57], [97, 56], [24, 26, 84, 106], [6, 16, 56, 22]]]
 h' := ![![[108, 40, 63], [100, 68, 87], [6, 59, 112], [87, 25, 91], [2, 52, 107], [19, 18, 50], [0, 1]], ![[55, 72, 50], [76, 18, 39], [10, 83, 29], [99, 61, 104], [67, 57, 19], [8, 101, 101], [108, 40, 63]], ![[0, 1], [77, 27, 100], [77, 84, 85], [112, 27, 31], [90, 4, 100], [40, 107, 75], [55, 72, 50]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [83, 112], []]
 b := ![[], [46, 109, 61], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [94, 95, 63, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9934087214, 14305045810, 26722090494, 131925836249, 279683403747]
  a := ![-26, 23, 50, 230, 547]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-253339186953, -294220218917, -237510485447, 131925836249, 279683403747]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 1442897 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-15, 7, -27, 16, 38]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![-15, 7, -27, 16, 38]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![63, 9, 1, 0, 0], ![111, 95, 0, 1, 0], ![69, 32, 0, 0, 1]] where
  M :=![![![-15, 7, -27, 16, 38], ![6, 1, 17, 17, 26], ![-8, 23, 26, 150, 272], ![-28, 142, 201, 944, 1676], ![6, -37, -54, -245, -431]]]
  hmulB := by decide  
  f := ![![![57, 12, -405, 181, 454]], ![![92, 238, 101, -52, -116]], ![![39, 26, -216, 96, 242]], ![![133, 211, -313, 134, 348]], ![![61, 75, -219, 96, 245]]]
  g := ![![![-24, -22, -27, 16, 38], ![-42, -23, 17, 17, 26], ![-328, -205, 26, 150, 272], ![-2063, -1283, 201, 944, 1676], ![534, 332, -54, -245, -431]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P1 : CertificateIrreducibleZModOfList' 113 2 2 6 [85, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [81, 112], [0, 1]]
 g := ![![[15, 4], [102], [14], [82], [6, 95], [81, 1]], ![[0, 109], [102], [14], [82], [17, 18], [49, 112]]]
 h' := ![![[81, 112], [49, 111], [40, 21], [10, 63], [55, 46], [8, 35], [0, 1]], ![[0, 1], [0, 2], [46, 92], [28, 50], [52, 67], [18, 78], [81, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37]]
 b := ![[], [70, 75]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N1 : CertifiedPrimeIdeal' SI113N1 113 where
  n := 2
  hpos := by decide
  P := [85, 32, 1]
  hirr := P113P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-101714, 50572, 159172, 820296, 2048848]
  a := ![11, -6, -16, -92, -232]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2146486, -1282064, 159172, 820296, 2048848]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N1 B_one_repr
lemma NI113N1 : Nat.card (O ⧸ I113N1) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![57, 12, -405, 181, 454]] ![![-15, 7, -27, 16, 38]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, 52, 149, -41, -64]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![-5, 52, 149, -41, -64]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![0, 0, 127, 0, 0], ![1, 39, 84, 1, 0], ![55, 0, 53, 0, 1]] where
  M :=![![![-5, 52, 149, -41, -64], ![18, -46, -7, -164, -634], ![-306, -146, 96, 1009, 3890], ![1872, 703, -1009, -6091, -23752], ![-1012, -371, 556, 3299, 12871]]]
  hmulB := by decide  
  f := ![![![-111, 47, -195, 108, 260]], ![![44, -3, 111, 81, 116]], ![![-46, 125, 124, 792, 1430]], ![![-19, 88, 123, 589, 1054]], ![![-67, 71, -35, 367, 691]]]
  g := ![![![28, 13, 55, -41, -64], ![276, 50, 373, -164, -634], ![-1695, -311, -2290, 1009, 3890], ![10349, 1876, 13933, -6091, -23752], ![-5608, -1016, -7549, 3299, 12871]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [115, 103, 123, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 28, 117], [123, 98, 10], [0, 1]]
 g := ![![[43, 82, 94], [122, 26, 117], [61, 84, 42], [10, 91, 64], [48, 2, 16], [1]], ![[14, 78, 7, 44], [95, 85, 25, 76], [72, 59, 69, 18], [109, 66, 18, 72], [62, 55, 122, 100], [33, 39, 82, 16]], ![[101, 30, 99, 33], [120, 110, 93, 40], [111, 125, 8, 63], [106, 56, 83, 14], [44, 4, 75, 28], [88, 20, 126, 111]]]
 h' := ![![[8, 28, 117], [67, 76, 100], [97, 108, 25], [120, 114, 13], [68, 50, 119], [12, 24, 4], [0, 1]], ![[123, 98, 10], [114, 98, 23], [27, 40, 100], [18, 96, 7], [76, 13, 113], [19, 32, 25], [8, 28, 117]], ![[0, 1], [120, 80, 4], [40, 106, 2], [113, 44, 107], [2, 64, 22], [103, 71, 98], [123, 98, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53, 120], []]
 b := ![[], [32, 104, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [115, 103, 123, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-187729625, -67931986, 100848452, 620324624, 2407098876]
  a := ![-4, 2, 8, 24, 84]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1048807027, -191028286, -1414036696, 620324624, 2407098876]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 2048383 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, -25, -32, 15, 36]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![-7, -25, -32, 15, 36]] 
 ![![127, 0, 0, 0, 0], ![74, 1, 0, 0, 0], ![112, 0, 1, 0, 0], ![94, 0, 0, 1, 0], ![101, 0, 0, 0, 1]] where
  M :=![![![-7, -25, -32, 15, 36], ![6, 8, -16, 7, 18], ![4, 13, 11, -5, -12], ![-2, -1, 10, -2, -6], ![0, -2, -6, 2, 5]]]
  hmulB := by decide  
  f := ![![![-145, 69, -266, 119, 300]], ![![-84, 40, -154, 69, 174]], ![![-128, 61, -235, 105, 264]], ![![-108, 51, -196, 92, 234]], ![![-115, 55, -212, 93, 233]]]
  g := ![![![3, -25, -32, 15, 36], ![-10, 8, -16, 7, 18], ![-4, 13, 11, -5, -12], ![-2, -1, 10, -2, -6], ![1, -2, -6, 2, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1

def I127N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![183, -74, 337, -133, -350]] i)))

def SI127N2: IdealEqSpanCertificate' Table ![![183, -74, 337, -133, -350]] 
 ![![127, 0, 0, 0, 0], ![96, 1, 0, 0, 0], ![55, 0, 1, 0, 0], ![54, 0, 0, 1, 0], ![45, 0, 0, 0, 1]] where
  M :=![![![183, -74, 337, -133, -350], ![-84, 50, -123, 176, 364], ![12, 92, 214, 685, 1204], ![-166, 697, 943, 4635, 8302], ![54, -187, -228, -1223, -2197]]]
  hmulB := by decide  
  f := ![![![1025, 2647, 941, -502, -1106]], ![![774, 2005, 729, -387, -854]], ![![441, 1138, 407, -220, -490]], ![![430, 1120, 395, -192, -392]], ![![367, 942, 335, -189, -433]]]
  g := ![![![92, -74, 337, -133, -350], ![-189, 50, -123, 176, 364], ![-880, 92, 214, 685, 1204], ![-5849, 697, 943, 4635, 8302], ![1539, -187, -228, -1223, -2197]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N2 : Nat.card (O ⧸ I127N2) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N2)

lemma isPrimeI127N2 : Ideal.IsPrime I127N2 := prime_ideal_of_norm_prime hp127.out _ NI127N2
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![-5, 52, 149, -41, -64]] ![![-7, -25, -32, 15, 36]]
  ![![1025, 2647, 941, -502, -1106]] where
 M := ![![![1025, 2647, 941, -502, -1106]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![1025, 2647, 941, -502, -1106]] ![![183, -74, 337, -133, -350]]
  ![![127, 0, 0, 0, 0]] where
 M := ![![![127, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![721, -328, 1550, -694, -1760]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![721, -328, 1550, -694, -1760]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![0, 0, 131, 0, 0], ![12, 55, 111, 1, 0], ![32, 129, 106, 0, 1]] where
  M :=![![![721, -328, 1550, -694, -1760], ![-372, 27, -650, 312, 772], ![148, -60, 191, 22, -20], ![-64, 170, 26, 685, 1264], ![56, -66, 88, -222, -439]]]
  hmulB := by decide  
  f := ![![![427, 156, -226, -1402, -5464]], ![![-2660, -975, 1414, 8724, 34004]], ![![16556, 6064, -8807, -54302, -211660]], ![![12164, 4455, -6471, -39897, -155512]], ![![11308, 4141, -6016, -37090, -144571]]]
  g := ![![![499, 2022, 2024, -694, -1760], ![-220, -891, -894, 312, 772], ![4, 10, -1, 22, -20], ![-372, -1531, -1603, 685, 1264], ![128, 525, 544, -222, -439]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [11, 26, 67, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [80, 58, 90], [115, 72, 41], [0, 1]]
 g := ![![[88, 26, 46], [5, 40, 5], [30, 117], [81, 36], [55, 81], [64, 1], []], ![[81, 14, 42, 26], [93, 124, 16, 56], [102, 125], [73, 45], [57, 52], [83, 75], [124, 109]], ![[110, 13, 28, 41], [123, 19, 55, 60], [91, 84], [41, 123], [89, 41], [82, 89], [42, 109]]]
 h' := ![![[80, 58, 90], [76, 123, 35], [118, 120, 108], [29, 49, 95], [93, 44, 6], [82, 28, 9], [0, 0, 1], [0, 1]], ![[115, 72, 41], [25, 17, 97], [0, 49, 105], [27, 124, 115], [31, 123, 69], [93, 11, 24], [58, 10, 72], [80, 58, 90]], ![[0, 1], [68, 122, 130], [54, 93, 49], [111, 89, 52], [118, 95, 56], [7, 92, 98], [56, 121, 58], [115, 72, 41]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [103, 24], []]
 b := ![[], [71, 42, 122], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [11, 26, 67, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-62834625, 96280458, 175950648, 866558562, 1818382422]
  a := ![-4, 8, 13, 41, 97]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-524044083, -2153708190, -2204279286, 866558562, 1818382422]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 2248091 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-427, -156, 226, 1402, 5464]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![-427, -156, 226, 1402, 5464]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![43, 20, 1, 0, 0], ![57, 36, 0, 1, 0], ![43, 93, 0, 0, 1]] where
  M :=![![![-427, -156, 226, 1402, 5464], ![2660, 975, -1414, -8724, -34004], ![-16556, -6064, 8807, 54302, 211660], ![103056, 37746, -54818, -338019, -1317536], ![-55888, -20470, 29728, 183310, 714509]]]
  hmulB := by decide  
  f := ![![![-721, 328, -1550, 694, 1760]], ![![372, -27, 650, -312, -772]], ![![-181, 104, -411, 180, 460]], ![![-211, 134, -496, 211, 544]], ![![27, 89, -48, 8, 33]]]
  g := ![![![-2481, -4300, 226, 1402, 5464], ![15442, 26761, -1414, -8724, -34004], ![-96121, -166576, 8807, 54302, 211660], ![598331, 1036898, -54818, -338019, -1317536], ![-324479, -562317, 29728, 183310, 714509]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P1 : CertificateIrreducibleZModOfList' 131 2 2 7 [60, 121, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 130], [0, 1]]
 g := ![![[109, 107], [49, 113], [48], [61], [45], [100], [1]], ![[0, 24], [0, 18], [48], [61], [45], [100], [1]]]
 h' := ![![[10, 130], [73, 32], [54, 47], [107, 110], [112, 89], [89, 62], [71, 10], [0, 1]], ![[0, 1], [0, 99], [0, 84], [28, 21], [85, 42], [54, 69], [40, 121], [10, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [28, 73]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N1 : CertifiedPrimeIdeal' SI131N1 131 where
  n := 2
  hpos := by decide
  P := [60, 121, 1]
  hirr := P131P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2048, 5623, 8948, 43199, 83108]
  a := ![2, -3, -4, -20, -43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-49029, -72195, 8948, 43199, 83108]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N1 B_one_repr
lemma NI131N1 : Nat.card (O ⧸ I131N1) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![721, -328, 1550, -694, -1760]] ![![-427, -156, 226, 1402, 5464]]
  ![![131, 0, 0, 0, 0]] where
 M := ![![![-131, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-40305, 16792, -73226, 32948, 83554]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![-40305, 16792, -73226, 32948, 83554]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![30, 20, 1, 0, 0], ![85, 41, 0, 1, 0], ![107, 33, 0, 0, 1]] where
  M :=![![![-40305, 16792, -73226, 32948, 83554], ![17658, -7357, 32082, -14434, -36602], ![-7734, 3224, -14057, 6316, 16006], ![3374, -1418, 6166, -2721, -6830], ![-3186, 1334, -5808, 2584, 6515]]]
  hmulB := by decide  
  f := ![![![-665, -1924, -1238, 604, 1394]], ![![186, -61, -1506, 666, 1670]], ![![-116, -424, -489, 228, 546]], ![![-357, -1211, -1214, 569, 1354]], ![![-475, -1519, -1332, 634, 1495]]]
  g := ![![![-69959, -19174, -73226, 32948, 83554], ![30646, 8399, 32082, -14434, -36602], ![-13398, -3670, -14057, 6316, 16006], ![5697, 1549, 6166, -2721, -6830], ![-5443, -1485, -5808, 2584, 6515]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [25, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [105, 136], [0, 1]]
 g := ![![[78, 11], [15], [60], [130, 130], [103], [65], [1]], ![[0, 126], [15], [60], [80, 7], [103], [65], [1]]]
 h' := ![![[105, 136], [21, 82], [81, 17], [38, 103], [65, 33], [96, 68], [112, 105], [0, 1]], ![[0, 1], [0, 55], [85, 120], [30, 34], [105, 104], [112, 69], [40, 32], [105, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [134, 94]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [25, 32, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-15112, -761, 13983, 75913, 234090]
  a := ![-3, 3, 13, 23, 66]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-233101, -81152, 13983, 75913, 234090]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2649, -1104, 4812, -2168, -5496]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![2649, -1104, 4812, -2168, -5496]] 
 ![![137, 0, 0, 0, 0], ![27, 1, 0, 0, 0], ![93, 0, 1, 0, 0], ![92, 0, 0, 1, 0], ![92, 0, 0, 0, 1]] where
  M :=![![![2649, -1104, 4812, -2168, -5496], ![-1160, 481, -2112, 932, 2376], ![512, -228, 901, -524, -1248], ![-200, -12, -552, -519, -792], ![204, -60, 420, 12, -107]]]
  hmulB := by decide  
  f := ![![![2001, 8160, 11076, -5176, -12456]], ![![379, 1585, 2220, -1036, -2496]], ![![1349, 5508, 7489, -3500, -8424]], ![![1348, 5484, 7416, -3463, -8328]], ![![1344, 5484, 7452, -3484, -8387]]]
  g := ![![![2117, -1104, 4812, -2168, -5496], ![-891, 481, -2112, 932, 2376], ![627, -228, 901, -524, -1248], ![1256, -12, -552, -519, -792], ![-208, -60, 420, 12, -107]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1

def I137N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-169, -247, 435, -188, -486]] i)))

def SI137N2: IdealEqSpanCertificate' Table ![![-169, -247, 435, -188, -486]] 
 ![![137, 0, 0, 0, 0], ![28, 1, 0, 0, 0], ![38, 0, 1, 0, 0], ![32, 0, 0, 1, 0], ![21, 0, 0, 0, 1]] where
  M :=![![![-169, -247, 435, -188, -486], ![-110, -357, -325, 155, 366], ![56, 45, -258, 114, 288], ![60, 170, 99, -48, -108], ![-34, -75, 10, -3, -13]]]
  hmulB := by decide  
  f := ![![![21831, -9096, 39661, -17853, -45270]], ![![4392, -1830, 7979, -3592, -9108]], ![![6086, -2536, 11056, -4979, -12624]], ![![5086, -2121, 9237, -4171, -10566]], ![![3359, -1399, 6103, -2744, -6961]]]
  g := ![![![47, -247, 435, -188, -486], ![70, -357, -325, 155, 366], ![-8, 45, -258, 114, 288], ![-34, 170, 99, -48, -108], ![15, -75, 10, -3, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N2 : Nat.card (O ⧸ I137N2) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N2)

lemma isPrimeI137N2 : Ideal.IsPrime I137N2 := prime_ideal_of_norm_prime hp137.out _ NI137N2

def I137N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![63, 66, -243, 107, 272]] i)))

def SI137N3: IdealEqSpanCertificate' Table ![![63, 66, -243, 107, 272]] 
 ![![137, 0, 0, 0, 0], ![62, 1, 0, 0, 0], ![129, 0, 1, 0, 0], ![85, 0, 0, 1, 0], ![136, 0, 0, 0, 1]] where
  M :=![![![63, 66, -243, 107, 272], ![58, 170, 115, -56, -130], ![-18, 2, 132, -57, -142], ![-28, -75, -27, 15, 20], ![14, 29, -14, 7, 25]]]
  hmulB := by decide  
  f := ![![![670011, -279139, 1217271, -547714, -1388972]], ![![301074, -125433, 546989, -246119, -624144]], ![![631825, -263230, 1147895, -516498, -1309810]], ![![415289, -173017, 754494, -339486, -860918]], ![![665508, -277263, 1209090, -544033, -1379637]]]
  g := ![![![-137, 66, -243, 107, 272], ![-21, 170, 115, -56, -130], ![51, 2, 132, -57, -142], ![30, -75, -27, 15, 20], ![-29, 29, -14, 7, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N3 : Nat.card (O ⧸ I137N3) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N3)

lemma isPrimeI137N3 : Ideal.IsPrime I137N3 := prime_ideal_of_norm_prime hp137.out _ NI137N3
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![-40305, 16792, -73226, 32948, 83554]] ![![2649, -1104, 4812, -2168, -5496]]
  ![![-153282961, 63860584, -278483606, 125304444, 317765026]] where
 M := ![![![-153282961, 63860584, -278483606, 125304444, 317765026]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI137N1 : IdealMulLeCertificate' Table 
  ![![-153282961, 63860584, -278483606, 125304444, 317765026]] ![![-169, -247, 435, -188, -486]]
  ![![-670011, 279139, -1217271, 547714, 1388972]] where
 M := ![![![-670011, 279139, -1217271, 547714, 1388972]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI137N2 : IdealMulLeCertificate' Table 
  ![![-670011, 279139, -1217271, 547714, 1388972]] ![![63, 66, -243, 107, 272]]
  ![![137, 0, 0, 0, 0]] where
 M := ![![![-137, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N1, I137N2, I137N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
    exact isPrimeI137N2
    exact isPrimeI137N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0 ⊙ MulI137N1 ⊙ MulI137N2)
instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![469, 135, -139, -1424, -5498]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![469, 135, -139, -1424, -5498]] 
 ![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![0, 0, 139, 0, 0], ![96, 4, 60, 1, 0], ![49, 38, 6, 0, 1]] where
  M :=![![![469, 135, -139, -1424, -5498], ![-2650, -955, 1361, 8641, 33658], ![16376, 5991, -8690, -53690, -209264], ![-101884, -37314, 54185, 334164, 1302508], ![55254, 20235, -29382, -181221, -706363]]]
  hmulB := by decide  
  f := ![![![-65, -48, 329, -149, -374]], ![![-76, -214, -121, 40, 100]], ![![20, -36, -194, -41, -20]], ![![-38, -55, 139, -125, -274]], ![![-43, -77, 75, -42, -103]]]
  g := ![![![2925, 1545, 851, -1424, -5498], ![-17852, -9457, -5173, 8641, 33658], ![110968, 58797, 32146, -53690, -209264], ![-690680, -365966, -200077, 334164, 1302508], ![374563, 198467, 108504, -181221, -706363]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [92, 118, 15, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [70, 0, 71], [54, 138, 68], [0, 1]]
 g := ![![[105, 108, 81], [47, 100, 1], [108, 49], [60, 3, 38], [124, 51], [124, 1], []], ![[101, 6, 60, 83], [49, 118, 47, 55], [2, 121], [42, 70, 110, 47], [99, 124], [79, 1], [1, 37]], ![[70, 26, 115, 85], [42, 85, 27, 70], [4, 16], [93, 38, 80, 76], [67, 86], [], [4, 37]]]
 h' := ![![[70, 0, 71], [124, 4, 9], [4, 12, 138], [40, 49, 132], [90, 75, 90], [129, 10, 107], [0, 0, 1], [0, 1]], ![[54, 138, 68], [30, 133, 136], [67, 47, 19], [116, 51, 11], [71, 79, 92], [12, 114, 47], [82, 92, 138], [70, 0, 71]], ![[0, 1], [59, 2, 133], [50, 80, 121], [1, 39, 135], [79, 124, 96], [31, 15, 124], [46, 47], [54, 138, 68]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [128, 42], []]
 b := ![[], [80, 32, 111], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [92, 118, 15, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-327430042, 235329629, 598607174, 3040793055, 7208914436]
  a := ![-8, 5, 12, 68, 169]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4643743674, -2056594181, -1619442178, 3040793055, 7208914436]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 2685619 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-87, 37, -158, 71, 180]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![-87, 37, -158, 71, 180]] 
 ![![139, 0, 0, 0, 0], ![17, 1, 0, 0, 0], ![128, 0, 1, 0, 0], ![48, 0, 0, 1, 0], ![74, 0, 0, 0, 1]] where
  M :=![![![-87, 37, -158, 71, 180], ![38, -16, 70, -31, -78], ![-16, 7, -31, 11, 24], ![2, -5, 16, 12, 54], ![-4, 4, -14, -4, -23]]]
  hmulB := by decide  
  f := ![![![-109, -337, -280, 139, 324]], ![![-13, -41, -36, 18, 42]], ![![-100, -309, -257, 129, 300]], ![![-38, -115, -94, 56, 126]], ![![-58, -180, -150, 72, 169]]]
  g := ![![![20, 37, -158, 71, 180], ![-10, -16, 70, -31, -78], ![11, 7, -31, 11, 24], ![-47, -5, 16, 12, 54], ![26, 4, -14, -4, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1

def I139N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-603, -221, 321, 1978, 7710]] i)))

def SI139N2: IdealEqSpanCertificate' Table ![![-603, -221, 321, 1978, 7710]] 
 ![![139, 0, 0, 0, 0], ![62, 1, 0, 0, 0], ![48, 0, 1, 0, 0], ![82, 0, 0, 1, 0], ![46, 0, 0, 0, 1]] where
  M :=![![![-603, -221, 321, 1978, 7710], ![3754, 1375, -1997, -12313, -47994], ![-23368, -8559, 12430, 76646, 298752], ![145460, 53278, -77373, -477100, -1859652], ![-78884, -28893, 41960, 258735, 1008503]]]
  hmulB := by decide  
  f := ![![![919, 1822, 5249, -2405, -5910]], ![![402, 802, 2345, -1074, -2640]], ![![316, 620, 1802, -825, -2028]], ![![544, 1079, 3091, -1413, -3474]], ![![304, 603, 1742, -799, -1963]]]
  g := ![![![-3735, -221, 321, 1978, 7710], ![23250, 1375, -1997, -12313, -47994], ![-144726, -8559, 12430, 76646, 298752], ![900880, 53278, -77373, -477100, -1859652], ![-488554, -28893, 41960, 258735, 1008503]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N2 : Nat.card (O ⧸ I139N2) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N2)

lemma isPrimeI139N2 : Ideal.IsPrime I139N2 := prime_ideal_of_norm_prime hp139.out _ NI139N2
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![469, 135, -139, -1424, -5498]] ![![-87, 37, -158, 71, 180]]
  ![![-14305, -652, -6155, 32489, 120112]] where
 M := ![![![-14305, -652, -6155, 32489, 120112]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI139N1 : IdealMulLeCertificate' Table 
  ![![-14305, -652, -6155, 32489, 120112]] ![![-603, -221, 321, 1978, 7710]]
  ![![139, 0, 0, 0, 0]] where
 M := ![![![-4599056721, -1684501524, 2446331612, 15084653076, 58797260486]]]
 hmul := by decide  
 g := ![![![![-33086739, -12118716, 17599508, 108522684, 423001874]]]]
 hle2 := by decide  


def PBC139 : ContainsPrimesAboveP 139 ![I139N0, I139N1, I139N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
    exact isPrimeI139N1
    exact isPrimeI139N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 139 (by decide) (𝕀 ⊙ MulI139N0 ⊙ MulI139N1)
instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-39, -88, -16, 22, 66]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![-39, -88, -16, 22, 66]] 
 ![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![0, 0, 149, 0, 0], ![119, 123, 59, 1, 0], ![111, 57, 102, 0, 1]] where
  M :=![![![-39, -88, -16, 22, 66], ![22, -17, -88, -38, -198], ![-122, -16, 67, 454, 1770], ![862, 332, -424, -2835, -11022], ![-470, -184, 236, 1534, 5969]]]
  hmulB := by decide  
  f := ![![![-763, 320, -1384, 622, 1578]], ![![334, -141, 608, -278, -702]], ![![-146, 56, -273, 94, 258]], ![![-391, 161, -711, 303, 780]], ![![-541, 223, -986, 422, 1085]]]
  g := ![![![-67, -44, -54, 22, 66], ![178, 107, 150, -38, -198], ![-1682, -1052, -1391, 454, 1770], ![10481, 6559, 8665, -2835, -11022], ![-5675, -3551, -4692, 1534, 5969]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [26, 94, 52, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [131, 127, 111], [115, 21, 38], [0, 1]]
 g := ![![[58, 110, 33], [61, 114], [119, 101, 37], [90, 127], [93, 145, 118], [97, 1], []], ![[55, 87, 142, 52], [131, 20], [80, 144, 110, 3], [143, 145], [103, 32, 133, 55], [16, 143], [41, 103]], ![[108, 56, 128, 41], [36, 95], [131, 60, 71, 135], [69, 64], [57, 60, 101, 115], [8, 37], [114, 103]]]
 h' := ![![[131, 127, 111], [86, 124, 35], [35, 109, 76], [8, 2, 22], [115, 125, 53], [11, 94, 77], [0, 0, 1], [0, 1]], ![[115, 21, 38], [45, 55, 46], [89, 18, 136], [38, 28, 88], [110, 119, 88], [40, 121, 131], [3, 71, 21], [131, 127, 111]], ![[0, 1], [87, 119, 68], [24, 22, 86], [96, 119, 39], [20, 54, 8], [43, 83, 90], [129, 78, 127], [115, 21, 38]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57, 9], []]
 b := ![[], [74, 34, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [26, 94, 52, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-40300952, 58435424, 108887582, 537427622, 1138051258]
  a := ![-4, 4, 7, 37, 88]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1277301192, -878618012, -991144768, 537427622, 1138051258]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 3307949 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-763, 320, -1384, 622, 1578]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![-763, 320, -1384, 622, 1578]] 
 ![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![40, 90, 1, 0, 0], ![125, 135, 0, 1, 0], ![84, 89, 0, 0, 1]] where
  M :=![![![-763, 320, -1384, 622, 1578], ![334, -141, 608, -278, -702], ![-146, 56, -273, 94, 258], ![70, -52, 80, -223, -438], ![-62, 32, -100, 94, 205]]]
  hmulB := by decide  
  f := ![![![-39, -88, -16, 22, 66]], ![![22, -17, -88, -38, -198]], ![![2, -34, -57, -14, -90]], ![![-7, -87, -96, -35, -198]], ![![-12, -61, -60, 0, -41]]]
  g := ![![![-1045, -668, -1384, 622, 1578], ![468, 303, 608, -278, -702], ![-152, -74, -273, 94, 258], ![413, 415, 80, -223, -438], ![-168, -147, -100, 94, 205]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P1 : CertificateIrreducibleZModOfList' 149 2 2 7 [99, 74, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [75, 148], [0, 1]]
 g := ![![[76, 125], [80], [109, 76], [30], [80, 61], [112], [1]], ![[64, 24], [80], [147, 73], [30], [36, 88], [112], [1]]]
 h' := ![![[75, 148], [72, 42], [86, 26], [92, 134], [126, 46], [54, 106], [50, 75], [0, 1]], ![[0, 1], [93, 107], [99, 123], [10, 15], [0, 103], [107, 43], [13, 74], [75, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [16, 85]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N1 : CertifiedPrimeIdeal' SI149N1 149 where
  n := 2
  hpos := by decide
  P := [99, 74, 1]
  hirr := P149P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-78466, 68072, 155452, 793012, 1827756]
  a := ![-11, 10, -4, 98, 238]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1737950, -1903688, 155452, 793012, 1827756]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N1 B_one_repr
lemma NI149N1 : Nat.card (O ⧸ I149N1) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![-39, -88, -16, 22, 66]] ![![-763, 320, -1384, 622, 1578]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-719, -687, 2981, -1322, -3348]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![-719, -687, 2981, -1322, -3348]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![33, 111, 1, 0, 0], ![112, 94, 0, 1, 0], ![33, 75, 0, 0, 1]] where
  M :=![![![-719, -687, 2981, -1322, -3348], ![-704, -2041, -1305, 595, 1392], ![202, -109, -1648, 458, 1326], ![410, 660, -61, -1818, -3306], ![-190, -277, 280, 361, 571]]]
  hmulB := by decide  
  f := ![![![9523, -4286, 18257, -6783, -15384]], ![![-1818, 2740, -9251, -4750, -23358]], ![![653, 1034, -2732, -4642, -19224]], ![![6576, -1233, 7427, -10115, -34248]], ![![831, 293, -408, -2690, -10469]]]
  g := ![![![1056, 290, 2981, -1322, -3348], ![-465, -116, -1305, 595, 1392], ![-268, 267, -1648, 458, 1326], ![2087, 2823, -61, -1818, -3306], ![-455, -716, 280, 361, 571]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [59, 61, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [90, 150], [0, 1]]
 g := ![![[129, 64], [126, 59], [35, 8], [25], [70, 44], [97], [1]], ![[0, 87], [0, 92], [0, 143], [25], [104, 107], [97], [1]]]
 h' := ![![[90, 150], [116, 143], [49, 132], [126, 59], [98, 5], [23, 73], [92, 90], [0, 1]], ![[0, 1], [0, 8], [0, 19], [0, 92], [95, 146], [100, 78], [38, 61], [90, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50]]
 b := ![[], [83, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [59, 61, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2405, 2736, 5260, 27666, 61622]
  a := ![-2, 3, -1, 18, 43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-35153, -51678, 5260, 27666, 61622]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-23, 118, 525, -229, -572]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![-23, 118, 525, -229, -572]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![44, 144, 1, 0, 0], ![6, 146, 0, 1, 0], ![14, 45, 0, 0, 1]] where
  M :=![![![-23, 118, 525, -229, -572], ![-114, -252, 3, 64, 106], ![-22, -50, -166, 455, 886], ![-24, 433, 429, 2253, 4048], ![2, -107, -62, -613, -1117]]]
  hmulB := by decide  
  f := ![![![-60993, 25409, -110807, 49864, 126460]], ![![26732, -11129, 48541, -21879, -55532]], ![![7642, -3177, 13862, -6270, -15942]], ![![23460, -9764, 42591, -19210, -48774]], ![![2278, -948, 4135, -1866, -4739]]]
  g := ![![![-91, -108, 525, -229, -572], ![-14, -98, 3, 64, 106], ![-52, -546, -166, 455, 886], ![-590, -3791, 429, 2253, 4048], ![146, 984, -62, -613, -1117]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P1 : CertificateIrreducibleZModOfList' 151 2 2 7 [63, 49, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [102, 150], [0, 1]]
 g := ![![[135, 38], [45, 116], [26, 124], [94], [86, 10], [136], [1]], ![[85, 113], [99, 35], [141, 27], [94], [49, 141], [136], [1]]]
 h' := ![![[102, 150], [34, 76], [23, 95], [140, 107], [18, 68], [82, 114], [88, 102], [0, 1]], ![[0, 1], [85, 75], [49, 56], [31, 44], [8, 83], [83, 37], [73, 49], [102, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [125]]
 b := ![[], [59, 138]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N1 : CertifiedPrimeIdeal' SI151N1 151 where
  n := 2
  hpos := by decide
  P := [63, 49, 1]
  hirr := P151P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-15821, 32964, 54801, 266821, 532788]
  a := ![-5, 4, 10, 49, 108]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-76073, -468806, 54801, 266821, 532788]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N1 B_one_repr
lemma NI151N1 : Nat.card (O ⧸ I151N1) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N1

def I151N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113825, -47427, 206786, -93087, -236034]] i)))

def SI151N2: IdealEqSpanCertificate' Table ![![113825, -47427, 206786, -93087, -236034]] 
 ![![151, 0, 0, 0, 0], ![47, 1, 0, 0, 0], ![56, 0, 1, 0, 0], ![86, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![113825, -47427, 206786, -93087, -236034], ![-49860, 20738, -90654, 40511, 102924], ![21902, -9349, 39347, -19511, -48246], ![-9224, 2391, -19636, -2864, 720], ![8930, -3340, 16978, -4574, -13691]]]
  hmulB := by decide  
  f := ![![![12383, 24319, -12388, 4757, 13242]], ![![3879, 7683, -3688, 1408, 3954]], ![![4570, 8971, -4531, 1703, 4710]], ![![6974, 13767, -7086, 2938, 8388]], ![![374, 690, -334, 12, -83]]]
  g := ![![![-1904, -47427, 206786, -93087, -236034], ![1036, 20738, -90654, 40511, 102924], ![853, -9349, 39347, -19511, -48246], ![8089, 2391, -19636, -2864, 720], ![-2230, -3340, 16978, -4574, -13691]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N2 : Nat.card (O ⧸ I151N2) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N2)

lemma isPrimeI151N2 : Ideal.IsPrime I151N2 := prime_ideal_of_norm_prime hp151.out _ NI151N2
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![-719, -687, 2981, -1322, -3348]] ![![-23, 118, 525, -229, -572]]
  ![![54305, -274958, -1233944, 550896, 1367872]] where
 M := ![![![54305, -274958, -1233944, 550896, 1367872]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI151N1 : IdealMulLeCertificate' Table 
  ![![54305, -274958, -1233944, 550896, 1367872]] ![![113825, -47427, 206786, -93087, -236034]]
  ![![151, 0, 0, 0, 0]] where
 M := ![![![-1536727, 7040073, 9898654, 47155639, 84368230]]]
 hmul := by decide  
 g := ![![![![-10177, 46623, 65554, 312289, 558730]]]]
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


lemma PB953I3_primes (p : ℕ) :
  p ∈ Set.range ![107, 109, 113, 127, 131, 137, 139, 149, 151] ↔ Nat.Prime p ∧ 103 < p ∧ p ≤ 151 := by
  rw [← List.mem_ofFn']
  convert primes_range 103 151 (by omega)

def PB953I3 : PrimesBelowBoundCertificateInterval O 103 151 953 where
  m := 9
  g := ![2, 3, 2, 3, 2, 4, 3, 2, 3]
  P := ![107, 109, 113, 127, 131, 137, 139, 149, 151]
  hP := PB953I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1, I109N2]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1, I127N2]
    · exact ![I131N0, I131N1]
    · exact ![I137N0, I137N1, I137N2, I137N3]
    · exact ![I139N0, I139N1, I139N2]
    · exact ![I149N0, I149N1]
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
    · exact ![11449, 1225043]
    · exact ![1295029, 109, 109]
    · exact ![1442897, 12769]
    · exact ![2048383, 127, 127]
    · exact ![2248091, 17161]
    · exact ![18769, 137, 137, 137]
    · exact ![2685619, 139, 139]
    · exact ![3307949, 22201]
    · exact ![22801, 22801, 151]
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
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
      exact NI127N2
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
      exact NI137N2
      exact NI137N3
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
      exact NI139N1
      exact NI139N2
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
      exact NI151N2
  β := ![I109N1, I109N2, I127N1, I127N2, I137N1, I137N2, I137N3, I139N1, I139N2, I151N2]
  Il := ![[], [I109N1, I109N2], [], [I127N1, I127N2], [], [I137N1, I137N2, I137N3], [I139N1, I139N2], [], [I151N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
