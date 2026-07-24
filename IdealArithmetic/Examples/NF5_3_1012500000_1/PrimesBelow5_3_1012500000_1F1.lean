
import IdealArithmetic.Examples.NF5_3_1012500000_1.RI5_3_1012500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-65833, -110030, 34947, -15977, 13241]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![-65833, -110030, 34947, -15977, 13241]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![22, 10, 24, 24, 1]] where
  M :=![![![-65833, -110030, 34947, -15977, 13241], ![79446, 132782, -42176, 19275, -15977], ![-95862, -160209, 50887, -23295, 19275], ![67206, 112315, -35669, 16357, -13520], ![24636, 41142, -13089, 6051, -4928]]]
  hmulB := by decide  
  f := ![![![-21869, -11664, 5167, -943, 1853]], ![![11118, 5926, -2632, 477, -943]], ![![-5658, -3027, 1325, -249, 477]], ![![3306, 1763, -781, 143, -280]], ![![-14614, -7804, 3441, -635, 1236]]]
  g := ![![![-12315, -8360, -9753, -11509, 13241], ![14860, 10088, 11768, 13887, -15977], ![-17928, -12171, -14197, -16755, 19275], ![12574, 8535, 9959, 11753, -13520], ![4588, 3118, 3627, 4287, -4928]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 4 2 4 [3, 24, 28, 5, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [7, 2, 27, 3], [17, 0, 12, 28], [0, 26, 19, 27], [0, 1]]
 g := ![![[17, 28, 22, 9], [18, 3, 13], [15, 26, 24, 1], []], ![[18, 11, 26, 3, 28, 10], [14, 26, 6], [18, 10, 2, 12, 23, 21], [27, 19, 23, 18, 14, 27]], ![[24, 28, 6, 4, 28, 20], [6, 2, 9], [17, 4, 17, 1], [12, 1, 17, 0, 12, 28]], ![[0, 15, 13, 14, 8, 3], [28, 3, 6], [15, 25, 1, 24, 13, 8], [5, 16, 1, 17, 7, 21]]]
 h' := ![![[7, 2, 27, 3], [28, 3, 16, 3], [13, 26, 15, 10], [0, 0, 0, 1], [0, 1]], ![[17, 0, 12, 28], [21, 19, 6, 19], [11, 21, 18, 8], [1, 24, 17, 23], [7, 2, 27, 3]], ![[0, 26, 19, 27], [20, 26, 13, 26], [26, 19, 3, 3], [5, 28, 17], [17, 0, 12, 28]], ![[0, 1], [27, 10, 23, 10], [13, 21, 22, 8], [14, 6, 24, 5], [0, 26, 19, 27]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [14, 4, 12], []]
 b := ![[], [], [1, 12, 5, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 4
  hpos := by decide
  P := [3, 24, 28, 5, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![422306757, 1017298819, -487532610, -1503779233, 53651997]
  a := ![0, -1, -4, -1, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-26139213, 16578581, -61213122, -96256109, 53651997]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 707281 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-21869, -11664, 5167, -943, 1853]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![-21869, -11664, 5167, -943, 1853]] 
 ![![29, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![14, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![-21869, -11664, 5167, -943, 1853], ![11118, 5926, -2632, 477, -943], ![-5658, -3027, 1325, -249, 477], ![3306, 1763, -781, 143, -280], ![2580, 1368, -621, 105, -220]]]
  hmulB := by decide  
  f := ![![![-65833, -110030, 34947, -15977, 13241]], ![![-8611, -14392, 4571, -2090, 1732]], ![![-12386, -20701, 6575, -3007, 2491]], ![![-29464, -49245, 15641, -7149, 5926]], ![![-10501, -17552, 5574, -2546, 2113]]]
  g := ![![![680, -11664, 5167, -943, 1853], ![-343, 5926, -2632, 477, -943], ![182, -3027, 1325, -249, 477], ![-103, 1763, -781, 143, -280], ![-74, 1368, -621, 105, -220]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![-65833, -110030, 34947, -15977, 13241]] ![![-21869, -11664, 5167, -943, 1853]]
  ![![29, 0, 0, 0, 0]] where
 M := ![![![29, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0)
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1571, 2626, -834, 382, -316]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![1571, 2626, -834, 382, -316]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![1, 22, 12, 1, 0], ![24, 2, 4, 0, 1]] where
  M :=![![![1571, 2626, -834, 382, -316], ![-1896, -3169, 1006, -462, 382], ![2292, 3834, -1217, 546, -462], ![-1608, -2690, 856, -377, 322], ![-600, -1014, 318, -114, 127]]]
  hmulB := by decide  
  f := ![![![-163, -78, 50, -2, 16]], ![![96, 77, 10, 18, -2]], ![![-12, 66, 97, 42, 18]], ![![59, 78, 46, 29, 6]], ![![-120, -44, 54, 6, 15]]]
  g := ![![![283, -166, -134, 382, -316], ![-342, 201, 162, -462, 382], ![414, -234, -191, 546, -462], ![-289, 160, 132, -377, 322], ![-114, 40, 38, -114, 127]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 3 2 4 [1, 24, 17, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 25], [2, 5], [0, 1]]
 g := ![![[19, 24, 9], [28, 0, 14], [21, 26, 10], [1]], ![[22, 17, 14], [29, 30, 8], [6, 16, 19], [1]], ![[10, 21, 8], [22, 1, 9], [20, 20, 2], [1]]]
 h' := ![![[12, 25], [3, 17, 28], [10, 29, 18], [30, 7, 14], [0, 1]], ![[2, 5], [23, 20, 16], [5, 24, 28], [22, 19, 8], [12, 25]], ![[0, 1], [25, 25, 18], [16, 9, 16], [7, 5, 9], [2, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10], []]
 b := ![[], [7, 28, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 3
  hpos := by decide
  P := [1, 24, 17, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-256553, -542286, -55326, -275016, -183248]
  a := ![3, -64, 1, -1, 2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![142465, 189502, 128318, -275016, -183248]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 29791 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 78, -50, 2, -16]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![163, 78, -50, 2, -16]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![25, 24, 1, 0, 0], ![27, 15, 0, 1, 0], ![10, 15, 0, 0, 1]] where
  M :=![![![163, 78, -50, 2, -16], ![-96, -77, -10, -18, 2], ![12, -66, -97, -42, -18], ![-24, -10, 8, -1, 2], ![-48, -90, -66, -30, -13]]]
  hmulB := by decide  
  f := ![![![-1571, -2626, 834, -382, 316]], ![![1896, 3169, -1006, 462, -382]], ![![127, 212, -67, 32, -26]], ![![-399, -667, 212, -97, 80]], ![![430, 719, -228, 104, -87]]]
  g := ![![![49, 48, -50, 2, -16], ![20, 13, -10, -18, 2], ![121, 102, -97, -42, -18], ![-7, -7, 8, -1, 2], ![82, 69, -66, -30, -13]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P1 : CertificateIrreducibleZModOfList' 31 2 2 4 [1, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [21, 30], [0, 1]]
 g := ![![[10, 1], [21, 8], [8, 5], [21, 1]], ![[0, 30], [3, 23], [20, 26], [11, 30]]]
 h' := ![![[21, 30], [10, 1], [23, 15], [10, 6], [0, 1]], ![[0, 1], [0, 30], [28, 16], [12, 25], [21, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [7, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N1 : CertifiedPrimeIdeal' SI31N1 31 where
  n := 2
  hpos := by decide
  P := [1, 10, 1]
  hirr := P31P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![300, 550, -474, -1258, 470]
  a := ![1, -3, -2, -1, -3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1336, 766, -474, -1258, 470]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N1 B_one_repr
lemma NI31N1 : Nat.card (O ⧸ I31N1) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![1571, 2626, -834, 382, -316]] ![![163, 78, -50, 2, -16]]
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

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![49, 120, 80, 48, 12]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![49, 120, 80, 48, 12]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![2, 15, 1, 0, 0], ![31, 17, 0, 1, 0], ![24, 27, 0, 0, 1]] where
  M :=![![![49, 120, 80, 48, 12], ![72, 229, 264, 120, 48], ![288, 792, 709, 360, 120], ![-24, -48, -8, -11, 0], ![216, 624, 624, 312, 109]]]
  hmulB := by decide  
  f := ![![![-7787, -4152, 1840, -336, 660]], ![![3960, 2113, -936, 168, -336]], ![![1130, 603, -267, 48, -96]], ![![-4673, -2491, 1104, -203, 396]], ![![-2136, -1137, 504, -96, 181]]]
  g := ![![![-51, -60, 80, 48, 12], ![-144, -191, 264, 120, 48], ![-410, -519, 709, 360, 120], ![9, 7, -8, -11, 0], ![-360, -459, 624, 312, 109]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [24, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 36], [0, 1]]
 g := ![![[34, 25], [3], [24, 11], [4], [1]], ![[21, 12], [3], [2, 26], [4], [1]]]
 h' := ![![[35, 36], [36, 32], [16, 22], [36, 14], [13, 35], [0, 1]], ![[0, 1], [9, 5], [9, 15], [8, 23], [17, 2], [35, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [33, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [24, 2, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2649, 6128, -2321, -8924, 1725]
  a := ![1, 19, 3, -1, 6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![6555, 3948, -2321, -8924, 1725]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 104, -24, 96, -22]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![71, 104, -24, 96, -22]] 
 ![![37, 0, 0, 0, 0], ![13, 1, 0, 0, 0], ![16, 0, 1, 0, 0], ![19, 0, 0, 1, 0], ![11, 0, 0, 0, 1]] where
  M :=![![![71, 104, -24, 96, -22], ![-132, -259, 24, -36, 96], ![576, 1308, -535, -1476, -36], ![-324, -648, 488, 1049, -228], ![-1764, -4380, 1608, 5556, 329]]]
  hmulB := by decide  
  f := ![![![319691, 174688, -70152, 16152, -26078]], ![![108095, 59445, -23232, 5676, -8726]], ![![140864, 77860, -29767, 7620, -11276]], ![![162857, 88984, -35744, 8225, -13286]], ![![94369, 52364, -19680, 5220, -7505]]]
  g := ![![![-67, 104, -24, 96, -22], ![67, -259, 24, -36, 96], ![556, 1308, -535, -1476, -36], ![-463, -648, 488, 1049, -228], ![-2155, -4380, 1608, 5556, 329]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -2, -2, 0, -4]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![-1, -2, -2, 0, -4]] 
 ![![37, 0, 0, 0, 0], ![22, 1, 0, 0, 0], ![34, 0, 1, 0, 0], ![31, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-1, -2, -2, 0, -4], ![-24, -61, 8, 60, 0], ![0, -24, -97, -132, 60], ![60, 162, -22, -145, -52], ![-132, -258, 286, 672, -241]]]
  hmulB := by decide  
  f := ![![![56699, 97034, -30686, 14160, -11636]], ![![31826, 54511, -17236, 7956, -6536]], ![![54398, 93020, -29421, 13572, -11156]], ![![45893, 78596, -24852, 11471, -9424]], ![![-588, -990, 314, -144, 119]]]
  g := ![![![3, -2, -2, 0, -4], ![-22, -61, 8, 60, 0], ![214, -24, -97, -132, 60], ![47, 162, -22, -145, -52], ![-676, -258, 286, 672, -241]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2

def I37N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 5, 19, 6, 4]] i)))

def SI37N3: IdealEqSpanCertificate' Table ![![-1, 5, 19, 6, 4]] 
 ![![37, 0, 0, 0, 0], ![24, 1, 0, 0, 0], ![16, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![11, 0, 0, 0, 1]] where
  M :=![![![-1, 5, 19, 6, 4], ![24, 59, 40, 24, 6], ![36, 114, 131, 60, 24], ![6, 9, -7, -1, -2], ![42, 117, 107, 54, 17]]]
  hmulB := by decide  
  f := ![![![-5689, -3035, 1345, -246, 482]], ![![-3612, -1927, 854, -156, 306]], ![![-2500, -1334, 591, -108, 212]], ![![-284, -151, 67, -13, 24]], ![![-1673, -892, 396, -72, 141]]]
  g := ![![![-13, 5, 19, 6, 4], ![-58, 59, 40, 24, 6], ![-140, 114, 131, 60, 24], ![-2, 9, -7, -1, -2], ![-129, 117, 107, 54, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N3 : Nat.card (O ⧸ I37N3) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N3)

lemma isPrimeI37N3 : Ideal.IsPrime I37N3 := prime_ideal_of_norm_prime hp37.out _ NI37N3
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![49, 120, 80, 48, 12]] ![![71, 104, -24, 96, -22]]
  ![![-3001, -5008, 1624, -672, 566]] where
 M := ![![![-3001, -5008, 1624, -672, 566]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![-3001, -5008, 1624, -672, 566]] ![![-1, -2, -2, 0, -4]]
  ![![8161, 17622, -14930, -37056, 7982]] where
 M := ![![![8161, 17622, -14930, -37056, 7982]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI37N2 : IdealMulLeCertificate' Table 
  ![![8161, 17622, -14930, -37056, 7982]] ![![-1, 5, 19, 6, 4]]
  ![![37, 0, 0, 0, 0]] where
 M := ![![![-9805, -21127, 17575, 44178, -10138]]]
 hmul := by decide  
 g := ![![![![-265, -571, 475, 1194, -274]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1, I37N2, I37N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
    exact isPrimeI37N2
    exact isPrimeI37N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0 ⊙ MulI37N1 ⊙ MulI37N2)
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


def P41P0 : CertificateIrreducibleZModOfList' 41 5 2 5 [28, 25, 24, 19, 33, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 0, 23, 14, 19], [34, 24, 24, 6, 12], [4, 8, 36, 16, 22], [14, 8, 40, 5, 29], [0, 1]]
 g := ![![[25, 4, 37, 22, 31], [37, 4, 31, 4], [23, 15, 3, 23], [1], []], ![[29, 17, 29, 1, 0, 10, 33, 3], [25, 14, 8, 1], [1, 23, 7, 2], [28, 2, 24, 30, 34, 19, 16, 11], [20, 5, 17, 33]], ![[17, 40, 8, 13, 34, 19, 5, 11], [8, 25, 13, 37], [15, 27, 35, 16], [14, 12, 21, 9, 32, 34, 2, 38], [32, 3, 25, 21]], ![[33, 39, 12, 24, 29, 1, 29, 17], [22, 11, 25, 20], [18, 17, 28, 36], [0, 10, 2, 1, 6, 29, 7, 26], [20, 19, 25, 33]], ![[40, 0, 25, 14, 11, 14, 29, 26], [9, 36], [2, 6, 38, 1], [23, 23, 23, 35, 33, 17, 17, 38], [7, 34, 7, 21]]]
 h' := ![![[38, 0, 23, 14, 19], [32, 23, 32, 21, 20], [17, 36, 15, 10, 2], [13, 16, 17, 22, 8], [0, 0, 1], [0, 1]], ![[34, 24, 24, 6, 12], [28, 32, 22, 21, 30], [21, 24, 5, 0, 1], [7, 29, 0, 28, 24], [23, 16, 11, 35, 26], [38, 0, 23, 14, 19]], ![[4, 8, 36, 16, 22], [21, 25, 14, 25, 10], [32, 1, 2, 9, 23], [40, 8, 28, 14, 4], [14, 10, 9, 36, 16], [34, 24, 24, 6, 12]], ![[14, 8, 40, 5, 29], [38, 27, 31, 1, 36], [11, 16, 32, 16, 15], [33, 18, 31, 33, 6], [30, 16, 9, 0, 20], [4, 8, 36, 16, 22]], ![[0, 1], [30, 16, 24, 14, 27], [6, 5, 28, 6], [12, 11, 6, 26, 40], [0, 40, 11, 11, 20], [14, 8, 40, 5, 29]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 9, 7, 6], [], [], []]
 b := ![[], [27, 34, 8, 10, 4], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 5
  hpos := by decide
  P := [28, 25, 24, 19, 33, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-406576869410, -1066553428578, 238331952942, 1110981174948, 248806106256]
  a := ![-1, 0, -2, 2, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9916509010, -26013498258, 5812974462, 27097101828, 6068441616]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-389, -648, 206, -94, 78]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![-389, -648, 206, -94, 78]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![31, 27, 1, 0, 0], ![17, 35, 0, 1, 0], ![29, 21, 0, 0, 1]] where
  M :=![![![-389, -648, 206, -94, 78], ![468, 781, -248, 114, -94], ![-564, -942, 299, -138, 114], ![396, 662, -210, 95, -80], ![144, 240, -74, 42, -31]]]
  hmulB := by decide  
  f := ![![![-47, -16, 22, 2, 6]], ![![36, 43, 24, 18, 2]], ![![-11, 17, 33, 14, 6]], ![![11, 29, 28, 15, 4]], ![![-13, 13, 28, 10, 5]]]
  g := ![![![-173, -106, 206, -94, 78], ![208, 127, -248, 114, -94], ![-251, -153, 299, -138, 114], ![177, 109, -210, 95, -80], ![61, 33, -74, 42, -31]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [9, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 42], [0, 1]]
 g := ![![[30, 24], [33, 35], [40], [36, 15], [1]], ![[0, 19], [0, 8], [40], [28, 28], [1]]]
 h' := ![![[31, 42], [4, 29], [40, 32], [20, 30], [34, 31], [0, 1]], ![[0, 1], [0, 14], [0, 11], [4, 13], [6, 12], [31, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [19, 39]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [9, 12, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-831, -2288, 624, 2336, 1068]
  a := ![0, 0, -6, -10, -4]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2113, -2868, 624, 2336, 1068]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-434677, -231820, 102733, -18731, 36837]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-434677, -231820, 102733, -18731, 36837]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![17, 31, 1, 0, 0], ![4, 35, 0, 1, 0], ![36, 1, 0, 0, 1]] where
  M :=![![![-434677, -231820, 102733, -18731, 36837], ![221022, 117878, -52238, 9525, -18731], ![-112386, -59943, 26563, -4845, 9525], ![65718, 35053, -15533, 2833, -5570], ![51348, 27384, -12135, 2217, -4352]]]
  hmulB := by decide  
  f := ![![![-1663, -4738, -4565, -2255, -789]], ![![-4734, -13498, -13022, -6423, -2255]], ![![-4385, -12501, -12056, -5947, -2087]], ![![-4000, -11405, -11003, -5428, -1905]], ![![-1770, -5044, -4865, -2406, -841]]]
  g := ![![![-79822, -65065, 102733, -18731, 36837], ![40588, 33084, -52238, 9525, -18731], ![-20639, -16822, 26563, -4845, 9525], ![12069, 9837, -15533, 2833, -5570], ![9429, 7682, -12135, 2217, -4352]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P1 : CertificateIrreducibleZModOfList' 43 2 2 5 [34, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [42, 42], [0, 1]]
 g := ![![[19, 4], [34, 14], [13], [24, 1], [1]], ![[15, 39], [20, 29], [13], [23, 42], [1]]]
 h' := ![![[42, 42], [5, 41], [32, 33], [1, 23], [9, 42], [0, 1]], ![[0, 1], [7, 2], [42, 10], [21, 20], [10, 1], [42, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [36, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N1 : CertifiedPrimeIdeal' SI43N1 43 where
  n := 2
  hpos := by decide
  P := [34, 1, 1]
  hirr := P43P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1554, 2743, -2524, -6163, 1755]
  a := ![13, -1, -2, 1, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![138, 6859, -2524, -6163, 1755]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N1 B_one_repr
lemma NI43N1 : Nat.card (O ⧸ I43N1) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N1

def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-49, -117, 71, 208, -22]] i)))

def SI43N2: IdealEqSpanCertificate' Table ![![-49, -117, 71, 208, -22]] 
 ![![43, 0, 0, 0, 0], ![28, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![23, 0, 0, 1, 0], ![17, 0, 0, 0, 1]] where
  M :=![![![-49, -117, 71, 208, -22], ![-132, -379, -24, 198, 208], ![1248, 2988, -1481, -4482, 198], ![-426, -791, 1113, 2407, -846], ![-5106, -12501, 5383, 17424, 67]]]
  hmulB := by decide  
  f := ![![![135305, 67489, -37997, 3184, -12596]], ![![86348, 42699, -24726, 1822, -8128]], ![![104283, 51147, -30404, 1962, -9918]], ![![71899, 35868, -20184, 1695, -6692]], ![![52789, 25550, -15830, 800, -5103]]]
  g := ![![![-82, -117, 71, 208, -22], ![74, -379, -24, 198, 208], ![1539, 2988, -1481, -4482, 198], ![-1302, -791, 1113, 2407, -846], ![-5456, -12501, 5383, 17424, 67]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![-389, -648, 206, -94, 78]] ![![-434677, -231820, 102733, -18731, 36837]]
  ![![543233, 285748, -127363, 22713, -45631]] where
 M := ![![![543233, 285748, -127363, 22713, -45631]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![543233, 285748, -127363, 22713, -45631]] ![![-49, -117, 71, 208, -22]]
  ![![43, 0, 0, 0, 0]] where
 M := ![![![29971, 49751, -15910, 7181, -5891]]]
 hmul := by decide  
 g := ![![![![697, 1157, -370, 167, -137]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1, I43N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
    exact isPrimeI43N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0 ⊙ MulI43N1)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![389, -144, -1, -45, 3]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![389, -144, -1, -45, 3]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![45, 14, 31, 1, 0], ![37, 21, 26, 0, 1]] where
  M :=![![![389, -144, -1, -45, 3], ![18, 434, -114, 75, -45], ![-270, -657, 197, -99, 75], ![210, 471, -143, 71, -54], ![36, 156, -45, 15, -16]]]
  hmulB := by decide  
  f := ![![![19, 54, 53, 27, 9]], ![![54, 154, 150, 75, 27]], ![![162, 459, 421, 189, 75]], ![![141, 400, 373, 173, 66]], ![![131, 372, 350, 165, 62]]]
  g := ![![![49, 9, 28, -45, 3], ![-36, 7, -27, 75, -45], ![30, -18, 28, -99, 75], ![-21, 13, -20, 71, -54], ![-1, 6, -2, 15, -16]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [27, 5, 17, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 8, 35], [18, 38, 12], [0, 1]]
 g := ![![[10, 2, 28], [41, 12, 12], [16, 10, 12], [2, 30, 1], []], ![[39, 12, 2, 29], [12, 5, 14, 11], [29, 38, 10, 5], [14, 45, 15, 15], [39, 3]], ![[25, 20, 41, 16], [14, 46, 3, 42], [3, 25, 31, 7], [44, 13, 5, 16], [15, 3]]]
 h' := ![![[12, 8, 35], [21, 22, 13], [38, 28, 24], [40, 26, 24], [0, 0, 1], [0, 1]], ![[18, 38, 12], [30, 24, 42], [37, 41, 12], [15, 25, 36], [31, 10, 38], [12, 8, 35]], ![[0, 1], [22, 1, 39], [8, 25, 11], [21, 43, 34], [13, 37, 8], [18, 38, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37, 26], []]
 b := ![[], [3, 34, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [27, 5, 17, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![28220, 65328, -39725, -111478, 13091]
  a := ![-1, -3, 1, -1, 2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![97029, 28747, 65441, -111478, 13091]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 103823 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19, -54, -53, -27, -9]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-19, -54, -53, -27, -9]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![3, 5, 1, 0, 0], ![43, 33, 0, 1, 0], ![33, 29, 0, 0, 1]] where
  M :=![![![-19, -54, -53, -27, -9], ![-54, -154, -150, -75, -27], ![-162, -459, -421, -189, -75], ![6, 15, 5, -7, 6], ![-108, -318, -393, -267, -64]]]
  hmulB := by decide  
  f := ![![![-389, 144, 1, 45, -3]], ![![-18, -434, 114, -75, 45]], ![![-21, -23, 8, -3, 3]], ![![-373, -183, 84, -13, 30]], ![![-285, -170, 72, -15, 26]]]
  g := ![![![34, 29, -53, -27, -9], ![96, 82, -150, -75, -27], ![249, 214, -421, -189, -75], ![2, 1, 5, -7, 6], ![312, 262, -393, -267, -64]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P1 : CertificateIrreducibleZModOfList' 47 2 2 5 [6, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 46], [0, 1]]
 g := ![![[34, 8], [41, 32], [15, 25], [44, 21], [1]], ![[0, 39], [46, 15], [38, 22], [37, 26], [1]]]
 h' := ![![[31, 46], [36, 14], [4, 28], [18, 5], [41, 31], [0, 1]], ![[0, 1], [0, 33], [26, 19], [32, 42], [15, 16], [31, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [21, 32]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N1 : CertifiedPrimeIdeal' SI47N1 47 where
  n := 2
  hpos := by decide
  P := [6, 16, 1]
  hirr := P47P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![525, 1162, -233, -1514, 137]
  a := ![3, 0, 3, -4, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1315, 1028, -233, -1514, 137]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N1 B_one_repr
lemma NI47N1 : Nat.card (O ⧸ I47N1) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![389, -144, -1, -45, 3]] ![![-19, -54, -53, -27, -9]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11465, -6134, 2685, -505, 967]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-11465, -6134, 2685, -505, 967]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![51, 39, 16, 1, 0], ![27, 28, 29, 0, 1]] where
  M :=![![![-11465, -6134, 2685, -505, 967], ![5802, 3040, -1442, 219, -505], ![-3030, -1773, 515, -219, 219], ![1734, 929, -405, 77, -146], ![1296, 558, -479, -21, -142]]]
  hmulB := by decide  
  f := ![![![-37, -64, 21, 1, 7]], ![![42, 68, -30, -3, 1]], ![![6, 57, -23, -189, -3]], ![![-3, 5, -8, -55, 6]], ![![3, 25, -15, -93, 4]]]
  g := ![![![-223, -255, -326, -505, 967], ![156, 163, 183, 219, -505], ![42, 12, -44, -219, 219], ![33, 38, 49, 77, -146], ![117, 101, 75, -21, -142]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [49, 49, 17, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 17, 14], [24, 35, 39], [0, 1]]
 g := ![![[3, 40, 17], [18, 10], [28, 8, 4], [39, 24], [1]], ![[25, 0, 35, 26], [33, 37], [27, 18, 25, 31], [32, 28], [33, 29, 24, 41]], ![[1, 48], [39, 40], [8, 36, 10, 18], [26, 40], [9, 38, 24, 12]]]
 h' := ![![[12, 17, 14], [2, 52, 21], [6, 48, 13], [13, 19, 2], [4, 4, 36], [0, 1]], ![[24, 35, 39], [20, 26, 32], [10, 35, 14], [47, 52, 18], [5, 13, 44], [12, 17, 14]], ![[0, 1], [37, 28], [26, 23, 26], [38, 35, 33], [27, 36, 26], [24, 35, 39]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 24], []]
 b := ![[], [49, 49, 21], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [49, 49, 17, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![355418, 829856, -475113, -1361210, 138339]
  a := ![1, 1, 1, -1, 4]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1246075, 944218, 326272, -1361210, 138339]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 148877 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 64, -21, -1, -7]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![37, 64, -21, -1, -7]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![3, 13, 1, 0, 0], ![45, 10, 0, 1, 0], ![2, 11, 0, 0, 1]] where
  M :=![![![37, 64, -21, -1, -7], ![-42, -68, 30, 3, -1], ![-6, -57, 23, 189, 3], ![6, 35, -43, -175, 30], ![192, 504, -145, -609, -82]]]
  hmulB := by decide  
  f := ![![![11465, 6134, -2685, 505, -967]], ![![-5802, -3040, 1442, -219, 505]], ![![-717, -365, 192, -21, 65]], ![![8607, 4617, -2000, 386, -723]], ![![-796, -410, 207, -26, 71]]]
  g := ![![![3, 8, -21, -1, -7], ![-5, -9, 30, 3, -1], ![-162, -43, 23, 189, 3], ![150, 38, -43, -175, 30], ![532, 177, -145, -609, -82]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P1 : CertificateIrreducibleZModOfList' 53 2 2 5 [43, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [48, 52], [0, 1]]
 g := ![![[26, 37], [6], [4, 17], [6], [48, 1]], ![[0, 16], [6], [25, 36], [6], [43, 52]]]
 h' := ![![[48, 52], [17, 14], [40, 35], [16, 21], [3, 35], [0, 1]], ![[0, 1], [0, 39], [24, 18], [17, 32], [40, 18], [48, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [4, 44]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N1 : CertifiedPrimeIdeal' SI53N1 53 where
  n := 2
  hpos := by decide
  P := [43, 5, 1]
  hirr := P53P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![73, -14, 7, 33, -1]
  a := ![4, 0, 0, 1, 0]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-27, -8, 7, 33, -1]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N1 B_one_repr
lemma NI53N1 : Nat.card (O ⧸ I53N1) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-11465, -6134, 2685, -505, 967]] ![![37, 64, -21, -1, -7]]
  ![![53, 0, 0, 0, 0]] where
 M := ![![![-53, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0, 0, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0, 0, 0]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![0, 0, 0, 0, 59]] where
  M :=![![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![0, 0, 0, 0, 59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 5 2 5 [22, 41, 24, 14, 40, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [31, 5, 48, 32, 14], [57, 11, 46, 13, 20], [44, 9, 17, 0, 35], [5, 33, 7, 14, 49], [0, 1]]
 g := ![![[12, 35, 32, 48, 57], [9, 9, 41, 22, 41], [20, 51, 27, 41], [52, 19, 1], []], ![[57, 19, 46, 5, 24, 41, 36, 56], [50, 34, 19, 1, 48, 53, 42, 8], [58, 58, 4, 29], [51, 18, 18, 18, 34, 12, 27, 13], [47, 32, 2, 31, 41, 9, 34, 30]], ![[18, 27, 46, 2, 42, 19, 43, 27], [52, 56, 53, 6, 15, 19, 36, 3], [36, 48, 48, 16], [3, 12, 53, 52, 32, 1, 58, 4], [57, 56, 36, 9, 9, 2, 40, 35]], ![[21, 49, 42, 2, 23, 16, 12, 16], [44, 22, 6, 32, 11, 49, 24, 57], [4, 48, 32, 25], [21, 42, 33, 4, 4, 20, 49, 57], [56, 19, 3, 40, 42, 2, 12, 41]], ![[26, 55, 10, 34, 24, 25, 49, 51], [52, 8, 51, 8, 18, 2, 49, 17], [30, 40, 16, 7], [43, 32, 45, 41, 21, 58, 24, 15], [39, 41, 17, 20, 32, 7, 9, 3]]]
 h' := ![![[31, 5, 48, 32, 14], [38, 38, 1, 7, 23], [30, 13, 44, 29, 49], [36, 46, 16, 14, 49], [0, 0, 0, 1], [0, 1]], ![[57, 11, 46, 13, 20], [44, 54, 6, 8, 57], [34, 6, 3, 36, 3], [37, 8, 25, 7, 41], [24, 43, 47, 16, 9], [31, 5, 48, 32, 14]], ![[44, 9, 17, 0, 35], [55, 47, 37, 51, 9], [43, 1, 22, 49, 3], [56, 40, 28, 27, 4], [36, 44, 31, 36, 37], [57, 11, 46, 13, 20]], ![[5, 33, 7, 14, 49], [43, 47, 49, 5, 14], [33, 52, 20, 53, 8], [48, 28, 43, 56, 5], [54, 57, 36, 56, 51], [44, 9, 17, 0, 35]], ![[0, 1], [43, 50, 25, 47, 15], [5, 46, 29, 10, 55], [55, 55, 6, 14, 19], [34, 33, 4, 9, 21], [5, 33, 7, 14, 49]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44, 27, 51, 28], [], [], []]
 b := ![[], [24, 9, 27, 1, 57], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 5
  hpos := by decide
  P := [22, 41, 24, 14, 40, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-61072992195578, -158776011562124, 39320626700944, 172094212199334, 32237809149926]
  a := ![7, 2, -24, 0, -23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1035135460942, -2691118840036, 666451300016, 2916851054226, 546403544914]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 714924299 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def PBC59 : ContainsPrimesAboveP 59 ![I59N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![59, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 59 (by decide) 𝕀

instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-177983, -94920, 42065, -7669, 15083]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-177983, -94920, 42065, -7669, 15083]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![20, 15, 48, 43, 1]] where
  M :=![![![-177983, -94920, 42065, -7669, 15083], ![90498, 48262, -21388, 3903, -7669], ![-46014, -24537, 10871, -1995, 3903], ![26910, 14357, -6359, 1157, -2284], ![21012, 11184, -4947, 963, -1792]]]
  hmulB := by decide  
  f := ![![![-11, -10, 29, 5, 7]], ![![42, 94, 44, 33, 5]], ![![30, 117, 173, 75, 33]], ![![18, 29, -15, -1, -4]], ![![44, 135, 148, 69, 27]]]
  g := ![![![-7863, -5265, -11179, -10758, 15083], ![3998, 2677, 5684, 5470, -7669], ![-2034, -1362, -2893, -2784, 3903], ![1190, 797, 1693, 1629, -2284], ![932, 624, 1329, 1279, -1792]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 4 2 5 [32, 18, 28, 22, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [56, 46, 9, 4], [60, 44, 29, 40], [45, 31, 23, 17], [0, 1]]
 g := ![![[44, 21, 15, 12], [49], [11, 17, 26, 25], [21, 29, 39, 1], []], ![[54, 56, 47, 53, 34, 47], [35, 24, 52], [51, 13, 46, 15, 14, 49], [3, 46, 48, 47, 49, 5], [27, 45, 26, 46, 0, 3]], ![[25, 1, 29, 2, 48, 35], [23, 6, 5], [29, 27, 1, 46, 31, 8], [57, 41, 25, 35, 38, 6], [28, 20, 26, 41, 0, 11]], ![[59, 2, 37, 49, 24, 44], [16, 7, 49], [60, 18, 5, 13, 2, 11], [56, 54, 28, 19, 44, 21], [44, 49, 19, 45, 0, 33]]]
 h' := ![![[56, 46, 9, 4], [31, 25, 3, 16], [14, 52, 7], [60, 36, 21, 5], [0, 0, 0, 1], [0, 1]], ![[60, 44, 29, 40], [17, 38, 51, 24], [51, 38, 47, 28], [35, 18, 45, 27], [48, 60, 26, 48], [56, 46, 9, 4]], ![[45, 31, 23, 17], [58, 50, 25, 10], [1, 23, 21, 26], [48, 38, 5, 54], [18, 25, 50, 28], [60, 44, 29, 40]], ![[0, 1], [59, 9, 43, 11], [12, 9, 47, 7], [13, 30, 51, 36], [47, 37, 46, 45], [45, 31, 23, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [20, 36, 27], []]
 b := ![[], [], [29, 14, 38, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 4
  hpos := by decide
  P := [32, 18, 28, 22, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1472806205, 3552021964, -1685717820, -5224218676, 175145820]
  a := ![1, 3, -8, -1, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-33280495, 15161224, -165454380, -209106376, 175145820]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 13845841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 10, -29, -5, -7]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![11, 10, -29, -5, -7]] 
 ![![61, 0, 0, 0, 0], ![18, 1, 0, 0, 0], ![42, 0, 1, 0, 0], ![36, 0, 0, 1, 0], ![51, 0, 0, 0, 1]] where
  M :=![![![11, 10, -29, -5, -7], ![-42, -94, -44, -33, -5], ![-30, -117, -173, -75, -33], ![-18, -29, 15, 1, 4], ![-60, -162, -129, -57, -20]]]
  hmulB := by decide  
  f := ![![![177983, 94920, -42065, 7669, -15083]], ![![51036, 27218, -12062, 2199, -4325]], ![![123300, 65757, -29141, 5313, -10449]], ![![104598, 55783, -24721, 4507, -8864]], ![![148461, 79176, -35088, 6396, -12581]]]
  g := ![![![26, 10, -29, -5, -7], ![81, -94, -44, -33, -5], ![225, -117, -173, -75, -33], ![-6, -29, 15, 1, 4], ![186, -162, -129, -57, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-177983, -94920, 42065, -7669, 15083]] ![![11, 10, -29, -5, -7]]
  ![![61, 0, 0, 0, 0]] where
 M := ![![![-61, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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


lemma PB1556I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB1556I1 : PrimesBelowBoundCertificateInterval O 23 61 1556 where
  m := 9
  g := ![2, 2, 4, 1, 3, 2, 2, 1, 2]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB1556I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1]
    · exact ![I31N0, I31N1]
    · exact ![I37N0, I37N1, I37N2, I37N3]
    · exact ![I41N0]
    · exact ![I43N0, I43N1, I43N2]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0]
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
    · exact ![707281, 29]
    · exact ![29791, 961]
    · exact ![1369, 37, 37, 37]
    · exact ![115856201]
    · exact ![1849, 1849, 43]
    · exact ![103823, 2209]
    · exact ![148877, 2809]
    · exact ![714924299]
    · exact ![13845841, 61]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
      exact NI37N2
      exact NI37N3
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
      exact NI43N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
  β := ![I29N1, I31N1, I37N0, I37N1, I37N2, I37N3, I43N2, I61N1]
  Il := ![[I29N1], [I31N1], [I37N0, I37N1, I37N2, I37N3], [], [I43N2], [], [], [], [I61N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
