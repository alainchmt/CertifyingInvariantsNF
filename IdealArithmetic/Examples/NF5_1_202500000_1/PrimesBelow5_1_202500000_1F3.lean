
import IdealArithmetic.Examples.NF5_1_202500000_1.RI5_1_202500000_1
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


def P107P0 : CertificateIrreducibleZModOfList' 107 5 2 6 [89, 19, 19, 34, 92, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [36, 63, 54, 21, 70], [101, 41, 35, 53, 17], [83, 88, 103, 95, 11], [9, 21, 22, 45, 9], [0, 1]]
 g := ![![[2, 83, 22, 58, 89], [79, 24, 40, 37, 105], [41, 2, 65, 49], [19, 48, 67, 62, 101], [15, 1], []], ![[1, 44, 71, 60, 34, 62, 3, 5], [103, 65, 78, 83, 80, 97, 97, 5], [86, 4, 52, 13], [18, 42, 48, 11, 63, 38, 26, 18], [8, 87, 80, 79], [44, 77, 85, 100, 105, 100, 17, 65]], ![[100, 66, 81, 82, 41, 38, 103, 82], [82, 96, 67, 98, 53, 58, 50, 95], [60, 74, 22, 44], [20, 18, 95, 99, 73, 1, 0, 58], [63, 58, 16, 30], [104, 40, 25, 53, 12, 14, 20, 98]], ![[32, 78, 22, 66, 74, 26, 56, 56], [75, 91, 37, 53, 95, 97, 46, 40], [60, 51, 99, 83], [52, 86, 26, 66, 76, 66, 15, 39], [7, 36, 73, 27], [103, 67, 55, 86, 5, 9, 94, 47]], ![[52, 24, 28, 48, 0, 11, 34, 85], [46, 47, 73, 9, 50, 36, 13, 25], [80, 72, 76, 37], [16, 49, 98, 61, 46, 75, 67, 13], [100, 51, 92, 105], [11, 90, 35, 78, 103, 20, 42, 87]]]
 h' := ![![[36, 63, 54, 21, 70], [31, 5, 25, 27, 14], [2, 48, 106, 96, 31], [21, 1, 96, 2, 100], [56, 54, 17, 6, 84], [0, 0, 0, 1], [0, 1]], ![[101, 41, 35, 53, 17], [28, 28, 71, 78, 68], [73, 41, 90, 96, 39], [39, 96, 74, 62, 86], [106, 90, 78, 49, 88], [47, 36, 8, 66, 20], [36, 63, 54, 21, 70]], ![[83, 88, 103, 95, 11], [25, 56, 73, 19, 43], [44, 78, 73, 81, 97], [81, 31, 21, 57, 77], [97, 37, 87, 74, 103], [51, 69, 19, 15, 64], [101, 41, 35, 53, 17]], ![[9, 21, 22, 45, 9], [95, 40, 10, 69, 30], [43, 1, 45, 71, 13], [56, 66, 102, 55, 46], [1, 79, 20, 67, 39], [14, 15, 59, 96, 54], [83, 88, 103, 95, 11]], ![[0, 1], [89, 85, 35, 21, 59], [21, 46, 7, 84, 34], [87, 20, 28, 38, 12], [100, 61, 12, 18, 7], [71, 94, 21, 36, 76], [9, 21, 22, 45, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29, 36, 92, 105], [], [], []]
 b := ![[], [71, 32, 73, 1, 52], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 5
  hpos := by decide
  P := [89, 19, 19, 34, 92, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![29966241714139, -58346096588240, 27905815071605, 2121204206446, -9242902880584]
  a := ![0, 6, 2, 5, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![280058333777, -545290622320, 260802010015, 19824338378, -86382269912]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-101, 54, 4, 0, -8]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![-101, 54, 4, 0, -8]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![44, 56, 1, 0, 0], ![54, 61, 0, 1, 0], ![21, 103, 0, 0, 1]] where
  M :=![![![-101, 54, 4, 0, -8], ![-80, 51, 2, 0, -8], ![-80, 72, -3, -4, -8], ![0, 2, 10, -1, -8], ![-60, 70, -6, 2, -11]]]
  hmulB := by decide  
  f := ![![![151, -238, 16, 16, 40]], ![![400, -625, 42, 40, 104]], ![![276, -432, 29, 28, 72]], ![![306, -479, 32, 31, 80]], ![![419, -655, 44, 42, 109]]]
  g := ![![![-1, 6, 4, 0, -8], ![0, 7, 2, 0, -8], ![4, 12, -3, -4, -8], ![-2, 3, 10, -1, -8], ![3, 13, -6, 2, -11]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [18, 79, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [30, 108], [0, 1]]
 g := ![![[71, 93], [104], [102, 35], [90, 15], [100], [30, 1]], ![[27, 16], [104], [62, 74], [104, 94], [100], [60, 108]]]
 h' := ![![[30, 108], [52, 86], [17, 39], [15, 12], [78, 48], [5, 10], [0, 1]], ![[0, 1], [16, 23], [97, 70], [48, 97], [101, 61], [87, 99], [30, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [34, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [18, 79, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![261104, -465272, 143624, 34636, -1372]
  a := ![3, -2, -1, -3, -56]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-72476, -96144, 143624, 34636, -1372]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, -19, 11, 28, -22]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![11, -19, 11, 28, -22]] 
 ![![109, 0, 0, 0, 0], ![39, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![64, 0, 0, 0, 1]] where
  M :=![![![11, -19, 11, 28, -22], ![-220, 401, -190, -56, 90], ![900, -1874, 897, -178, -134], ![-1120, 2749, -1317, 1097, -356], ![-1280, 2143, -1021, -806, 819]]]
  hmulB := by decide  
  f := ![![![-17721, 24123, 2293, 50, -2730]], ![![-6591, 8944, 887, 34, -1000]], ![![-1045, 1281, 306, 80, -84]], ![![-1141, 1358, 382, 109, -70]], ![![-9976, 13285, 1645, 188, -1377]]]
  g := ![![![17, -19, 11, 28, -22], ![-185, 401, -190, -56, 90], ![731, -1874, 897, -178, -134], ![-815, 2749, -1317, 1097, -356], ![-1146, 2143, -1021, -806, 819]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1

def I109N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-51, 81, -7, -6, -14]] i)))

def SI109N2: IdealEqSpanCertificate' Table ![![-51, 81, -7, -6, -14]] 
 ![![109, 0, 0, 0, 0], ![55, 1, 0, 0, 0], ![27, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![64, 0, 0, 0, 1]] where
  M :=![![![-51, 81, -7, -6, -14], ![-140, 221, -18, -16, -38], ![-380, 598, -47, -42, -102], ![-320, 501, -37, -35, -84], ![-500, 783, -57, -54, -133]]]
  hmulB := by decide  
  f := ![![![1281, -641, -53, -8, 94]], ![![655, -328, -27, -4, 48]], ![![323, -161, -14, -2, 24]], ![![83, -44, -2, -1, 6]], ![![756, -379, -31, -4, 55]]]
  g := ![![![-31, 81, -7, -6, -14], ![-85, 221, -18, -16, -38], ![-231, 598, -47, -42, -102], ![-195, 501, -37, -35, -84], ![-304, 783, -57, -54, -133]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N2 : Nat.card (O ⧸ I109N2) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N2)

lemma isPrimeI109N2 : Ideal.IsPrime I109N2 := prime_ideal_of_norm_prime hp109.out _ NI109N2

def I109N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-431, 726, -106, -72, -140]] i)))

def SI109N3: IdealEqSpanCertificate' Table ![![-431, 726, -106, -72, -140]] 
 ![![109, 0, 0, 0, 0], ![68, 1, 0, 0, 0], ![63, 0, 1, 0, 0], ![61, 0, 0, 1, 0], ![89, 0, 0, 0, 1]] where
  M :=![![![-431, 726, -106, -72, -140], ![-1400, 2301, -288, -208, -428], ![-4280, 6940, -775, -588, -1260], ![-4160, 6654, -646, -523, -1176], ![-6440, 10314, -1014, -816, -1827]]]
  hmulB := by decide  
  f := ![![![-99, 378, -198, 192, -68]], ![![-68, 245, -128, 112, -36]], ![![7, 98, -57, 124, -64]], ![![-211, 532, -264, 133, -12]], ![![-79, 272, -144, 88, -15]]]
  g := ![![![-241, 726, -106, -72, -140], ![-816, 2301, -288, -208, -428], ![-2563, 6940, -775, -588, -1260], ![-2563, 6654, -646, -523, -1176], ![-3959, 10314, -1014, -816, -1827]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N3 : Nat.card (O ⧸ I109N3) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N3)

lemma isPrimeI109N3 : Ideal.IsPrime I109N3 := prime_ideal_of_norm_prime hp109.out _ NI109N3
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![-101, 54, 4, 0, -8]] ![![11, -19, 11, 28, -22]]
  ![![849, -1067, 385, -116, -6]] where
 M := ![![![849, -1067, 385, -116, -6]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![849, -1067, 385, -116, -6]] ![![-51, 81, -7, -6, -14]]
  ![![-99, 378, -198, 192, -68]] where
 M := ![![![-99, 378, -198, 192, -68]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI109N2 : IdealMulLeCertificate' Table 
  ![![-99, 378, -198, 192, -68]] ![![-431, 726, -106, -72, -140]]
  ![![109, 0, 0, 0, 0]] where
 M := ![![![109, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 14, -5, 17, -11]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![-3, 14, -5, 17, -11]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![0, 0, 113, 0, 0], ![112, 97, 19, 1, 0], ![9, 87, 112, 0, 1]] where
  M :=![![![-3, 14, -5, 17, -11], ![-110, 189, -85, -55, 57], ![570, -1138, 558, -3, -163], ![-1100, 2404, -1138, 481, -6], ![-450, 598, -265, -585, 450]]]
  hmulB := by decide  
  f := ![![![589, -430, -11, 9, 65]], ![![650, -655, 5, 25, 101]], ![![1010, -1294, 32, 61, 201]], ![![1316, -1213, -1, 41, 186]], ![![1557, -1833, 35, 81, 284]]]
  g := ![![![-16, -6, 8, 17, -11], ![49, 5, -48, -55, 57], ![21, 118, 167, -3, -163], ![-486, -387, -85, 481, -6], ![540, 161, -350, -585, 450]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [46, 91, 60, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [55, 35, 71], [111, 77, 42], [0, 1]]
 g := ![![[16, 62, 87], [22, 8], [97, 99], [15, 88], [6, 15, 97], [1]], ![[89, 45, 61, 21], [62, 97], [43, 49], [0, 102], [97, 12, 95, 89], [95, 5, 99, 40]], ![[93, 86, 20, 73], [92, 28], [58, 44], [87, 63], [40, 81, 12, 54], [108, 14, 33, 73]]]
 h' := ![![[55, 35, 71], [7, 28, 58], [62, 105, 11], [2, 38, 72], [63, 89, 38], [67, 22, 53], [0, 1]], ![[111, 77, 42], [60, 4, 13], [55, 96, 53], [98, 21, 106], [95, 48, 92], [76, 34, 106], [55, 35, 71]], ![[0, 1], [11, 81, 42], [66, 25, 49], [94, 54, 48], [49, 89, 96], [109, 57, 67], [111, 77, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [94, 15], []]
 b := ![[], [57, 72, 73], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [46, 91, 60, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5518808, -10654639, 5491440, 1057191, -2465551]
  a := ![1, 3, 1, 2, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-802625, 896467, 2314571, 1057191, -2465551]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 1442897 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![589, -430, -11, 9, 65]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![589, -430, -11, 9, 65]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![40, 76, 1, 0, 0], ![42, 32, 0, 1, 0], ![50, 87, 0, 0, 1]] where
  M :=![![![589, -430, -11, 9, 65], ![650, -655, 5, 25, 101], ![1010, -1294, 32, 61, 201], ![500, -788, 26, 41, 122], ![970, -1346, 35, 65, 208]]]
  hmulB := by decide  
  f := ![![![-3, 14, -5, 17, -11]], ![![-110, 189, -85, -55, 57]], ![![-70, 122, -54, -31, 33]], ![![-42, 80, -36, -5, 12]], ![![-90, 157, -70, -40, 43]]]
  g := ![![![-23, -49, -11, 9, 65], ![-50, -94, 5, 25, 101], ![-114, -205, 32, 61, 201], ![-74, -130, 26, 41, 122], ![-120, -214, 35, 65, 208]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P1 : CertificateIrreducibleZModOfList' 113 2 2 6 [68, 68, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [45, 112], [0, 1]]
 g := ![![[1, 83], [63], [60], [2], [42, 53], [45, 1]], ![[7, 30], [63], [60], [2], [54, 60], [90, 112]]]
 h' := ![![[45, 112], [93, 99], [14, 96], [34, 88], [82, 62], [104, 36], [0, 1]], ![[0, 1], [28, 14], [40, 17], [39, 25], [47, 51], [29, 77], [45, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [30, 74]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N1 : CertifiedPrimeIdeal' SI113N1 113 where
  n := 2
  hpos := by decide
  P := [68, 68, 1]
  hirr := P113P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![127997, -222808, 75828, 34494, -17318]
  a := ![1, -6, -3, -7, 43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-30867, -49406, 75828, 34494, -17318]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N1 B_one_repr
lemma NI113N1 : Nat.card (O ⧸ I113N1) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![-3, 14, -5, 17, -11]] ![![589, -430, -11, 9, 65]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3521, -4969, 126, 239, 765]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![3521, -4969, 126, 239, 765]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![0, 0, 127, 0, 0], ![0, 0, 0, 127, 0], ![73, 37, 42, 122, 1]] where
  M :=![![![3521, -4969, 126, 239, 765], ![7650, -11253, 273, 539, 1721], ![17210, -25588, 528, 1189, 3877], ![10780, -16027, 181, 683, 2378], ![17550, -25995, 320, 1117, 3866]]]
  hmulB := by decide  
  f := ![![![7, -13, 6, -1, -1]], ![![-10, 27, -13, 13, -5]], ![![-50, 72, -34, -57, 47]], ![![260, -479, 229, 75, -114]], ![![233, -433, 207, 57, -96]]]
  g := ![![![-412, -262, -252, -733, 765], ![-929, -590, -567, -1649, 1721], ![-2093, -1331, -1278, -3715, 3877], ![-1282, -819, -785, -2279, 2378], ![-2084, -1331, -1276, -3705, 3866]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 4 2 6 [126, 45, 108, 69, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 13, 58, 17], [101, 90, 66, 36], [83, 23, 3, 74], [0, 1]]
 g := ![![[1, 125, 9, 47], [106, 120, 2, 50], [5, 113, 10, 113], [20, 120, 9, 19], [40, 81, 58, 1], []], ![[13, 46, 99, 105, 18, 64], [21, 86, 120, 15, 44, 31], [110, 89, 22, 100, 48, 76], [3, 36, 114, 95, 100, 31], [83, 108, 21, 67, 39, 36], [41, 96, 94, 50, 87, 87]], ![[35, 104, 124, 40, 85, 35], [30, 23, 43, 114, 21, 35], [93, 49, 11, 54, 86, 36], [107, 88, 5, 55, 123, 21], [68, 101, 86, 4, 88, 16], [29, 97, 112, 79, 0, 47]], ![[2, 75, 57, 97, 104, 4], [112, 89, 85, 81, 8, 34], [27, 108, 41, 56, 87, 41], [88, 124, 57, 18, 118, 19], [50, 23, 59, 41, 24, 9], [109, 75, 90, 62, 126, 94]]]
 h' := ![![[1, 13, 58, 17], [106, 74, 4, 89], [5, 34, 7, 47], [20, 58, 90, 85], [40, 59, 94, 107], [0, 0, 0, 1], [0, 1]], ![[101, 90, 66, 36], [56, 119, 126, 43], [17, 49, 82, 46], [65, 50, 84, 39], [69, 125, 69, 81], [42, 68, 28, 63], [1, 13, 58, 17]], ![[83, 23, 3, 74], [89, 67, 55, 24], [43, 22, 102, 24], [26, 112, 64, 126], [32, 113, 14, 102], [106, 83, 123, 43], [101, 90, 66, 36]], ![[0, 1], [68, 121, 69, 98], [1, 22, 63, 10], [26, 34, 16, 4], [56, 84, 77, 91], [15, 103, 103, 20], [83, 23, 3, 74]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [115, 92, 73], []]
 b := ![[], [], [103, 1, 10, 65], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 4
  hpos := by decide
  P := [126, 45, 108, 69, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![56601709481, -102873430647, 48929982817, 18901338217, -26123380412]
  a := ![-1, 7, 5, 9, -28]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![15461484091, 6800721611, 9024503623, 25243730303, -26123380412]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 260144641 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, -13, 6, -1, -1]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![7, -13, 6, -1, -1]] 
 ![![127, 0, 0, 0, 0], ![19, 1, 0, 0, 0], ![20, 0, 1, 0, 0], ![54, 0, 0, 1, 0], ![66, 0, 0, 0, 1]] where
  M :=![![![7, -13, 6, -1, -1], ![-10, 27, -13, 13, -5], ![-50, 72, -34, -57, 47], ![260, -479, 229, 75, -114], ![-170, 373, -178, 75, 0]]]
  hmulB := by decide  
  f := ![![![3521, -4969, 126, 239, 765]], ![![587, -832, 21, 40, 128]], ![![690, -984, 24, 47, 151]], ![![1582, -2239, 55, 107, 344]], ![![1968, -2787, 68, 133, 428]]]
  g := ![![![2, -13, 6, -1, -1], ![-5, 27, -13, 13, -5], ![-6, 72, -34, -57, 47], ![65, -479, 229, 75, -114], ![-61, 373, -178, 75, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![3521, -4969, 126, 239, 765]] ![![7, -13, 6, -1, -1]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![213211, -105102, -9092, -1088, 15230]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![213211, -105102, -9092, -1088, 15230]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![0, 0, 131, 0, 0], ![72, 82, 78, 1, 0], ![110, 103, 17, 0, 1]] where
  M :=![![![213211, -105102, -9092, -1088, 15230], ![152300, -75071, -6496, -778, 10878], ![108780, -53604, -4643, -558, 7766], ![-15560, 7694, 658, 77, -1116], ![54700, -26930, -2340, -284, 3901]]]
  hmulB := by decide  
  f := ![![![41, -62, 4, 4, 6]], ![![60, -77, -20, 6, 22]], ![![220, -364, 51, -30, 46]], ![![192, -300, 20, -11, 44]], ![![110, -159, -7, 4, 29]]]
  g := ![![![-10563, -12096, -1398, -1088, 15230], ![-7544, -8639, -998, -778, 10878], ![-5384, -6166, -711, -558, 7766], ![776, 888, 104, 77, -1116], ![-2702, -3095, -355, -284, 3901]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [45, 113, 61, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [97, 44, 63], [104, 86, 68], [0, 1]]
 g := ![![[91, 120, 117], [15, 13, 94], [26, 3], [68, 62], [90, 63], [70, 1], []], ![[10, 97, 75, 99], [19, 52, 46, 35], [97, 39], [87, 41], [30, 100], [87, 60], [21, 39]], ![[122, 77, 11, 71], [38, 41, 115, 18], [54, 101], [98, 94], [53, 53], [53, 102], [16, 39]]]
 h' := ![![[97, 44, 63], [111, 8, 36], [42, 101, 116], [66, 30, 93], [47, 56, 18], [125, 36, 71], [0, 0, 1], [0, 1]], ![[104, 86, 68], [99, 6, 63], [124, 25, 95], [67, 55, 63], [107, 64, 98], [127, 21, 121], [80, 85, 86], [97, 44, 63]], ![[0, 1], [88, 117, 32], [62, 5, 51], [93, 46, 106], [7, 11, 15], [54, 74, 70], [9, 46, 44], [104, 86, 68]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [101, 125], []]
 b := ![[], [72, 99, 50], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [45, 113, 61, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2779955, 3051420, 812218, -2481090, 19360]
  a := ![0, 4, -2, -6, -16]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1326175, 1561120, 1480978, -2481090, 19360]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 2248091 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-41, 62, -4, -4, -6]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![-41, 62, -4, -4, -6]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![14, 107, 1, 0, 0], ![30, 124, 0, 1, 0], ![43, 54, 0, 0, 1]] where
  M :=![![![-41, 62, -4, -4, -6], ![-60, 77, 20, -6, -22], ![-220, 364, -51, 30, -46], ![-120, 130, 6, -119, 60], ![20, -110, 164, 24, -91]]]
  hmulB := by decide  
  f := ![![![-213211, 105102, 9092, 1088, -15230]], ![![-152300, 75071, 6496, 778, -10878]], ![![-148014, 72959, 6313, 756, -10572]], ![![-192870, 95070, 8226, 985, -13776]], ![![-133183, 65650, 5680, 680, -9513]]]
  g := ![![![3, 10, -4, -4, -6], ![6, -1, 20, -6, -22], ![12, 35, -51, 30, -46], ![6, 84, 6, -119, 60], ![7, -120, 164, 24, -91]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P1 : CertificateIrreducibleZModOfList' 131 2 2 7 [46, 60, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [71, 130], [0, 1]]
 g := ![![[7, 94], [26, 25], [81], [44], [59], [63], [1]], ![[0, 37], [98, 106], [81], [44], [59], [63], [1]]]
 h' := ![![[71, 130], [114, 15], [74, 5], [130, 122], [53, 31], [4, 37], [85, 71], [0, 1]], ![[0, 1], [0, 116], [36, 126], [15, 9], [27, 100], [11, 94], [17, 60], [71, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52]]
 b := ![[], [125, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N1 : CertifiedPrimeIdeal' SI131N1 131 where
  n := 2
  hpos := by decide
  P := [46, 60, 1]
  hirr := P131P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![39275, -64886, 24375, 14942, -12972]
  a := ![13, 6, 4, 7, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1469, -29201, 24375, 14942, -12972]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N1 B_one_repr
lemma NI131N1 : Nat.card (O ⧸ I131N1) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![213211, -105102, -9092, -1088, 15230]] ![![-41, 62, -4, -4, -6]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7716461, 14898655, -7116433, -795724, 2521160]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![-7716461, 14898655, -7116433, -795724, 2521160]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![0, 0, 137, 0, 0], ![0, 0, 0, 137, 0], ![125, 112, 131, 108, 1]] where
  M :=![![![-7716461, 14898655, -7116433, -795724, 2521160], ![25211600, -54822777, 26226066, -10120258, -661736], ![-6617360, 47904842, -23108605, 72030912, -41142768], ![-202405160, 327579739, -156062723, -151726357, 144061824], ![263600540, -534902979, 255667039, -26538242, -54131115]]]
  hmulB := by decide  
  f := ![![![-171145757, 84371989, 7297213, 872682, -12226336]], ![![-122263360, 60281945, 5212168, 622726, -8735608]], ![![-87356080, 43090466, 3722131, 443276, -6244704]], ![![12454520, -6120223, -532869, -65135, 886552]], ![![-330140405, 162800330, 14071791, 1679466, -23592219]]]
  g := ![![![-2356653, -1952345, -2462689, -1993292, 2521160], ![787800, 140815, 824186, 447790, -661736], ![37490720, 33984634, 39172219, 32959488, -41142768], ![-132920680, -115382077, -138891691, -114674477, 144061824], ![51313795, 40348773, 53626592, 42478994, -54131115]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 4 2 7 [102, 131, 118, 39, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [58, 26, 80, 74], [59, 31, 75, 33], [118, 79, 119, 30], [0, 1]]
 g := ![![[123, 81, 113, 34], [2, 43, 11], [89, 72, 133], [124, 92, 121, 122], [65, 27, 14], [1], []], ![[58, 121, 117, 100, 39, 68], [40, 110, 17], [5, 90, 130], [127, 66, 102, 76, 53, 109], [18, 45, 65], [130, 71, 14], [45, 77, 133]], ![[63, 131, 24, 74, 45, 132], [18, 113, 8], [12, 135, 120], [118, 86, 97, 46, 19, 85], [109, 79, 61], [103, 63, 37], [25, 17, 130]], ![[5, 69, 100, 17], [62, 91, 105], [96, 22, 7], [130, 40, 31, 106, 101, 72], [45, 125, 126], [27, 12, 4], [27, 125, 78]]]
 h' := ![![[58, 26, 80, 74], [120, 60, 87, 50], [119, 128, 53, 82], [93, 136, 92, 74], [75, 111, 102, 81], [35, 6, 19, 98], [0, 0, 1], [0, 1]], ![[59, 31, 75, 33], [102, 83, 77, 89], [88, 101, 33, 47], [119, 135, 128, 33], [1, 115, 5, 92], [78, 4, 71, 105], [7, 90, 36, 98], [58, 26, 80, 74]], ![[118, 79, 119, 30], [5, 136, 47, 135], [34, 45, 117, 75], [5, 18, 72, 42], [4, 48, 78, 53], [5, 115, 12, 91], [109, 19, 5, 41], [59, 31, 75, 33]], ![[0, 1], [106, 132, 63], [111, 0, 71, 70], [54, 122, 119, 125], [30, 0, 89, 48], [109, 12, 35, 117], [73, 28, 95, 135], [118, 79, 119, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [60, 81, 10], []]
 b := ![[], [], [24, 100, 117, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 4
  hpos := by decide
  P := [102, 131, 118, 39, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![24945531, -22606128, 10516200, 55335326, -39464142]
  a := ![-1, -2, -1, -3, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![36189513, 32097648, 37812546, 31514326, -39464142]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 352275361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![171145757, -84371989, -7297213, -872682, 12226336]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![171145757, -84371989, -7297213, -872682, 12226336]] 
 ![![137, 0, 0, 0, 0], ![115, 1, 0, 0, 0], ![64, 0, 1, 0, 0], ![124, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![171145757, -84371989, -7297213, -872682, 12226336], ![122263360, -60281945, -5212168, -622726, 8735608], ![87356080, -43090466, -3722131, -443276, 6244704], ![-12454520, 6120223, 532869, 65135, -886552], ![43961220, -21701783, -1871617, -221704, 3145299]]]
  hmulB := by decide  
  f := ![![![7716461, -14898655, 7116433, 795724, -2521160]], ![![6293295, -12106004, 5782217, 741814, -2111472]], ![![3653072, -7309626, 3493141, -154048, -877456]], ![![8461652, -15876007, 7580295, 1827709, -3333472]], ![![-1867767, 3795652, -1814238, 199518, 376715]]]
  g := ![![![76181988, -84371989, -7297213, -872682, 12226336], ![54428819, -60281945, -5212168, -622726, 8735608], ![38902902, -43090466, -3722131, -443276, 6244704], ![-5529737, 6120223, 532869, 65135, -886552], ![19589750, -21701783, -1871617, -221704, 3145299]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![-7716461, 14898655, -7116433, -795724, 2521160]] ![![171145757, -84371989, -7297213, -872682, 12226336]]
  ![![137, 0, 0, 0, 0]] where
 M := ![![![-137, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-500761, 760528, -29008, -40958, -119576]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![-500761, 760528, -29008, -40958, -119576]] 
 ![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![0, 0, 139, 0, 0], ![0, 0, 0, 139, 0], ![122, 64, 49, 18, 1]] where
  M :=![![![-500761, 760528, -29008, -40958, -119576], ![-1195760, 1812141, -64554, -95676, -283408], ![-2834080, 4284668, -140593, -221164, -666112], ![-1913520, 2879272, -78476, -141903, -442328], ![-3070040, 4621992, -128924, -229030, -711029]]]
  hmulB := by decide  
  f := ![![![-419, 224, 8, 22, -40]], ![![-400, 319, -70, -68, 48]], ![![480, -1244, 653, 44, -224]], ![![-1360, 2968, -1428, 475, 88]], ![![-562, 292, 19, 60, -77]]]
  g := ![![![101349, 60528, 41944, 15190, -119576], ![240144, 143527, 99442, 36012, -283408], ![564256, 337524, 233805, 84668, -666112], ![374464, 224376, 155364, 56259, -442328], ![601982, 360632, 249723, 90428, -711029]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 4 2 7 [10, 70, 106, 57, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [84, 31, 45, 10], [134, 30, 49, 43], [3, 77, 45, 86], [0, 1]]
 g := ![![[75, 116, 49, 38], [49, 52, 123, 79], [104, 43, 42], [86, 29, 49, 46], [102, 85, 52], [1], []], ![[31, 131, 88, 55, 69, 108], [96, 21, 100, 50, 35, 43], [100, 78, 121], [108, 73, 85, 49, 76, 130], [132, 4, 1], [4, 56, 31], [16, 65, 100]], ![[104, 36, 3, 45, 57, 32], [73, 5, 3, 60, 35, 94], [55], [13, 128, 34, 80, 108, 73], [112, 55, 91], [74, 137, 100], [66, 13, 42]], ![[81, 62, 23, 22, 33, 100], [75, 88, 49, 107, 7, 83], [26, 51, 136], [98, 131, 116, 136, 93, 42], [16, 75, 24], [89, 32, 78], [87, 110, 29]]]
 h' := ![![[84, 31, 45, 10], [66, 110, 7, 49], [53, 36, 32, 94], [113, 113, 114, 43], [53, 82, 24, 18], [129, 69, 33, 82], [0, 0, 1], [0, 1]], ![[134, 30, 49, 43], [36, 20, 125, 119], [100, 104, 100, 18], [108, 106, 58, 11], [112, 84, 66, 98], [96, 98, 100, 1], [85, 102, 24, 93], [84, 31, 45, 10]], ![[3, 77, 45, 86], [79, 87, 134, 18], [127, 39, 100, 19], [128, 57, 74], [137, 16, 104, 100], [80, 23, 90, 77], [60, 93, 7, 129], [134, 30, 49, 43]], ![[0, 1], [39, 61, 12, 92], [47, 99, 46, 8], [86, 2, 32, 85], [46, 96, 84, 62], [117, 88, 55, 118], [112, 83, 107, 56], [3, 77, 45, 86]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [131, 76, 80], []]
 b := ![[], [], [95, 35, 20, 24], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 4
  hpos := by decide
  P := [10, 70, 106, 57, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![126645834, 723831160, -367621348, 1999623028, -1209094240]
  a := ![3, -3, 0, -7, 12]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1062130526, 561912680, 423582708, 170959132, -1209094240]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 373301041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![419, -224, -8, -22, 40]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![419, -224, -8, -22, 40]] 
 ![![139, 0, 0, 0, 0], ![66, 1, 0, 0, 0], ![92, 0, 1, 0, 0], ![115, 0, 0, 1, 0], ![76, 0, 0, 0, 1]] where
  M :=![![![419, -224, -8, -22, 40], ![400, -319, 70, 68, -48], ![-480, 1244, -653, -44, 224], ![1360, -2968, 1428, -475, -88], ![440, -376, 148, 698, -497]]]
  hmulB := by decide  
  f := ![![![500761, -760528, 29008, 40958, 119576]], ![![246374, -374151, 14238, 20136, 58816]], ![![351828, -534196, 20211, 28700, 83936]], ![![428065, -649928, 24564, 34907, 102112]], ![![295884, -449080, 16788, 24042, 70495]]]
  g := ![![![111, -224, -8, -22, 40], ![78, -319, 70, 68, -48], ![-248, 1244, -653, -44, 224], ![915, -2968, 1428, -475, -88], ![-222, -376, 148, 698, -497]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![-500761, 760528, -29008, -40958, -119576]] ![![419, -224, -8, -22, 40]]
  ![![139, 0, 0, 0, 0]] where
 M := ![![![-139, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1671, 3740, -1798, 866, -78]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![-1671, 3740, -1798, 866, -78]] 
 ![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![0, 0, 149, 0, 0], ![126, 5, 127, 1, 0], ![108, 126, 115, 0, 1]] where
  M :=![![![-1671, 3740, -1798, 866, -78], ![-780, -1055, 530, -5406, 3386], ![33860, -59708, 28583, 15258, -18238], ![-108120, 212416, -101316, -3423, 30516], ![30500, -80108, 38654, -40566, 15751]]]
  hmulB := by decide  
  f := ![![![3727779021, -1837628284, -158953850, -19017306, 266288358]], ![![2662883580, -1312682475, -113546322, -13584730, 190219134]], ![![1902191340, -937695236, -81110129, -9704050, 135880214]], ![![4861215974, -2396361999, -207284013, -24799547, 347253744]], ![![6428405172, -3168916162, -274109529, -32794580, 459203577]]]
  g := ![![![-687, 62, -690, 866, -78], ![2112, -2689, 1998, -5406, 3386], ![544, 14510, 1263, 15258, -18238], ![-19950, -24265, -21315, -3423, 30516], ![23092, -12496, 22679, -40566, 15751]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [13, 105, 92, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 51, 42], [45, 97, 107], [0, 1]]
 g := ![![[22, 139, 116], [119, 95], [62, 28, 22], [36, 113], [6, 63, 76], [57, 1], []], ![[122, 35, 75, 119], [53, 29], [94, 61, 75, 103], [10, 6], [45, 148, 60, 6], [125, 22], [85, 125]], ![[60, 76, 143, 69], [123, 103], [131, 102, 20, 85], [130, 73], [6, 133, 41, 132], [38, 68], [20, 125]]]
 h' := ![![[12, 51, 42], [88, 99, 99], [88, 10, 63], [103, 14, 52], [71, 57, 34], [4, 111, 15], [0, 0, 1], [0, 1]], ![[45, 97, 107], [7, 62, 53], [10, 32, 124], [65, 12, 119], [116, 64, 30], [33, 20, 8], [82, 61, 97], [12, 51, 42]], ![[0, 1], [31, 137, 146], [132, 107, 111], [133, 123, 127], [66, 28, 85], [35, 18, 126], [126, 88, 51], [45, 97, 107]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [76, 19], []]
 b := ![[], [104, 11, 145], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [13, 105, 92, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7142589, 13181560, -7021468, -2791054, 4309842]
  a := ![1, -4, -3, -5, 17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-811629, -3462438, -994560, -2791054, 4309842]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 3307949 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3727779021, -1837628284, -158953850, -19017306, 266288358]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![3727779021, -1837628284, -158953850, -19017306, 266288358]] 
 ![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![73, 45, 1, 0, 0], ![109, 119, 0, 1, 0], ![136, 100, 0, 0, 1]] where
  M :=![![![3727779021, -1837628284, -158953850, -19017306, 266288358], ![2662883580, -1312682475, -113546322, -13584730, 190219134], ![1902191340, -937695236, -81110129, -9704050, 135880214], ![-271694600, 133933280, 11585156, 1386053, -19408100], ![956901180, -471709476, -40802614, -4881642, 68354815]]]
  hmulB := by decide  
  f := ![![![-1671, 3740, -1798, 866, -78]], ![![-780, -1055, 530, -5406, 3386]], ![![-827, 1113, -529, -1106, 862]], ![![-2571, 3319, -1572, -3707, 2852]], ![![-1844, 2168, -1026, -3110, 2307]]]
  g := ![![![-126247787, -127855580, -158953850, -19017306, 266288358], ![-90183232, -91331735, -113546322, -13584730, 190219134], ![-64421053, -65241469, -81110129, -9704050, 135880214], ![9201415, 9318597, 11585156, 1386053, -19408100], ![-32407140, -32819852, -40802614, -4881642, 68354815]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P1 : CertificateIrreducibleZModOfList' 149 2 2 7 [41, 70, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [79, 148], [0, 1]]
 g := ![![[118, 133], [103], [131, 86], [69], [48, 114], [132], [1]], ![[46, 16], [103], [71, 63], [69], [114, 35], [132], [1]]]
 h' := ![![[79, 148], [147, 27], [142, 111], [69, 91], [118, 48], [143, 76], [108, 79], [0, 1]], ![[0, 1], [45, 122], [120, 38], [106, 58], [36, 101], [38, 73], [91, 70], [79, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56]]
 b := ![[], [86, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N1 : CertifiedPrimeIdeal' SI149N1 149 where
  n := 2
  hpos := by decide
  P := [41, 70, 1]
  hirr := P149P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![297, 92, -54, 95, 12]
  a := ![4, 0, 0, 1, 0]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-52, -67, -54, 95, 12]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N1 B_one_repr
lemma NI149N1 : Nat.card (O ⧸ I149N1) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![-1671, 3740, -1798, 866, -78]] ![![3727779021, -1837628284, -158953850, -19017306, 266288358]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 5, -3, -2, 2]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![1, 5, -3, -2, 2]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![98, 12, 1, 0, 0], ![118, 122, 0, 1, 0], ![39, 67, 0, 0, 1]] where
  M :=![![![1, 5, -3, -2, 2], ![20, -35, 18, 0, -6], ![-60, 134, -59, 30, -6], ![0, -55, 31, -107, 60], ![140, -261, 131, 38, -65]]]
  hmulB := by decide  
  f := ![![![631, -919, 61, 60, 154]], ![![1540, -2355, 160, 156, 394]], ![![558, -824, 55, 54, 138]], ![![1758, -2653, 179, 175, 444]], ![![879, -1333, 90, 88, 223]]]
  g := ![![![3, 1, -3, -2, 2], ![-10, 1, 18, 0, -6], ![16, -16, -59, 30, -6], ![48, 57, 31, -107, 60], ![-97, -14, 131, 38, -65]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [6, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [142, 150], [0, 1]]
 g := ![![[77, 36], [93, 76], [117, 105], [39], [15, 138], [81], [1]], ![[55, 115], [13, 75], [78, 46], [39], [132, 13], [81], [1]]]
 h' := ![![[142, 150], [46, 6], [53, 23], [14, 135], [61, 103], [3, 134], [145, 142], [0, 1]], ![[0, 1], [143, 145], [148, 128], [7, 16], [40, 48], [5, 17], [75, 9], [142, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [90]]
 b := ![[], [127, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [6, 9, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![502718, -839639, 279147, 205756, -118378]
  a := ![7, 23, -1, 23, -90]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-308054, -141459, 279147, 205756, -118378]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8581, -10983, -1971, -412, 936]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![8581, -10983, -1971, -412, 936]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![77, 119, 1, 0, 0], ![61, 71, 0, 1, 0], ![42, 82, 0, 0, 1]] where
  M :=![![![8581, -10983, -1971, -412, 936], ![9360, -8791, -5990, -2182, -712], ![-7120, 25070, -17583, -8328, -9440], ![-43640, 77749, -16341, -9811, -16656], ![-62900, 113603, -25407, -14962, -24841]]]
  hmulB := by decide  
  f := ![![![456846171, -225204723, -19480087, -2330606, 32634128]], ![![326341280, -160871655, -13915308, -1664834, 23311704]], ![![491687977, -242380178, -20965752, -2508352, 35123000]], ![![337778481, -166509681, -14402996, -1723181, 24128704]], ![![305064862, -150383331, -13008075, -1556292, 21791855]]]
  g := ![![![968, 1166, -1971, -412, 936], ![4196, 6075, -5990, -2182, -712], ![14909, 23065, -17583, -8328, -9440], ![16640, 27051, -16341, -9811, -16656], ![25493, 41300, -25407, -14962, -24841]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P1 : CertificateIrreducibleZModOfList' 151 2 2 7 [17, 51, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [100, 150], [0, 1]]
 g := ![![[3, 80], [95, 84], [0, 148], [22], [], [34], [1]], ![[0, 71], [39, 67], [2, 3], [22], [], [34], [1]]]
 h' := ![![[100, 150], [46, 69], [0, 101], [79, 86], [0, 18], [13], [134, 100], [0, 1]], ![[0, 1], [0, 82], [134, 50], [72, 65], [139, 133], [13], [17, 51], [100, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [77, 80]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N1 : CertifiedPrimeIdeal' SI151N1 151 where
  n := 2
  hpos := by decide
  P := [17, 51, 1]
  hirr := P151P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![68109, -114425, 39074, 26203, -17291]
  a := ![1, 9, 1, 8, -33]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-25250, -34482, 39074, 26203, -17291]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N1 B_one_repr
lemma NI151N1 : Nat.card (O ⧸ I151N1) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N1

def I151N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-123471651, 60866000, 5264876, 629892, -8820014]] i)))

def SI151N2: IdealEqSpanCertificate' Table ![![-123471651, 60866000, 5264876, 629892, -8820014]] 
 ![![151, 0, 0, 0, 0], ![20, 1, 0, 0, 0], ![53, 0, 1, 0, 0], ![123, 0, 0, 1, 0], ![31, 0, 0, 0, 1]] where
  M :=![![![-123471651, 60866000, 5264876, 629892, -8820014], ![-88200140, 43478723, 3760886, 449954, -6300446], ![-63004460, 31058380, 2686533, 321418, -4500630], ![8999080, -4436144, -383724, -45909, 642836], ![-31694520, 15623980, 1351466, 161690, -2264051]]]
  hmulB := by decide  
  f := ![![![-38221, 58440, -2696, -3360, -9326]], ![![-5680, 8683, -398, -498, -1386]], ![![-14923, 22812, -1047, -1306, -3636]], ![![-32193, 49208, -2252, -2829, -7850]], ![![-9541, 14572, -650, -826, -2325]]]
  g := ![![![-9429711, 60866000, 5264876, 629892, -8820014], ![-6735974, 43478723, 3760886, 449954, -6300446], ![-4811743, 31058380, 2686533, 321418, -4500630], ![687273, -4436144, -383724, -45909, 642836], ![-2420557, 15623980, 1351466, 161690, -2264051]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N2 : Nat.card (O ⧸ I151N2) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N2)

lemma isPrimeI151N2 : Ideal.IsPrime I151N2 := prime_ideal_of_norm_prime hp151.out _ NI151N2
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![1, 5, -3, -2, 2]] ![![8581, -10983, -1971, -412, 936]]
  ![![38221, -58440, 2696, 3360, 9326]] where
 M := ![![![38221, -58440, 2696, 3360, 9326]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI151N1 : IdealMulLeCertificate' Table 
  ![![38221, -58440, 2696, 3360, 9326]] ![![-123471651, 60866000, 5264876, 629892, -8820014]]
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


lemma PB886I3_primes (p : ℕ) :
  p ∈ Set.range ![107, 109, 113, 127, 131, 137, 139, 149, 151] ↔ Nat.Prime p ∧ 103 < p ∧ p ≤ 151 := by
  rw [← List.mem_ofFn']
  convert primes_range 103 151 (by omega)

def PB886I3 : PrimesBelowBoundCertificateInterval O 103 151 886 where
  m := 9
  g := ![1, 4, 2, 2, 2, 2, 2, 2, 3]
  P := ![107, 109, 113, 127, 131, 137, 139, 149, 151]
  hP := PB886I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I107N0]
    · exact ![I109N0, I109N1, I109N2, I109N3]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1]
    · exact ![I131N0, I131N1]
    · exact ![I137N0, I137N1]
    · exact ![I139N0, I139N1]
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
    · exact ![14025517307]
    · exact ![11881, 109, 109, 109]
    · exact ![1442897, 12769]
    · exact ![260144641, 127]
    · exact ![2248091, 17161]
    · exact ![352275361, 137]
    · exact ![373301041, 139]
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
      exact NI139N1
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
      exact NI151N2
  β := ![I109N1, I109N2, I109N3, I127N1, I137N1, I139N1, I151N2]
  Il := ![[], [I109N1, I109N2, I109N3], [], [I127N1], [], [I137N1], [I139N1], [], [I151N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
