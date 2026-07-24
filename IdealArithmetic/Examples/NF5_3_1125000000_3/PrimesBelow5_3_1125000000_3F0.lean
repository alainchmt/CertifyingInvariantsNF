
import IdealArithmetic.Examples.NF5_3_1125000000_3.RI5_3_1125000000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1635, -524, -439, 95, 623]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![1635, -524, -439, 95, 623]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![1635, -524, -439, 95, 623], ![-1008, 443, 342, -94, -486], ![704, -160, -153, 28, 220], ![-428, 100, 91, -10, -127], ![177, -82, -65, 23, 95]]]
  hmulB := by decide  
  f := ![![![-89, -102, 134, 40, -195]], ![![287, 273, -326, 64, 355]], ![![-990, -732, 727, -944, -198]], ![![-126, -250, 390, 421, -793]], ![![-327, -122, 13, -725, 521]]]
  g := ![![![770, -524, -439, 95, 623], ![-457, 443, 342, -94, -486], ![338, -160, -153, 28, 220], ![-209, 100, 91, -10, -127], ![77, -82, -65, 23, 95]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6, -4, 2, -7, -7]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![-6, -4, 2, -7, -7]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-6, -4, 2, -7, -7], ![-30, -31, 10, -46, -42], ![-208, -206, 69, -308, -284], ![-100, -100, 33, -149, -137], ![-145, -144, 48, -215, -198]]]
  hmulB := by decide  
  f := ![![![-1, 2, 3, -1, -4]], ![![3, 3, -1, 1, 0]], ![![-2, 2, -1, -10, 8]], ![![-4, -4, 6, 2, -9]], ![![1, 4, -4, -6, 9]]]
  g := ![![![4, -4, 2, -7, -7], ![29, -31, 10, -46, -42], ![192, -206, 69, -308, -284], ![93, -100, 33, -149, -137], ![134, -144, 48, -215, -198]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![730, 1743, 989, -561, -1424]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![730, 1743, 989, -561, -1424]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![730, 1743, 989, -561, -1424], ![842, 2007, 1139, -646, -1640], ![970, 2313, 1311, -744, -1888], ![-623, -1486, -843, 478, 1214], ![-235, -561, -319, 181, 459]]]
  hmulB := by decide  
  f := ![![![-22, -19, 7, -30, -28]], ![![-78, -77, 26, -115, -106]], ![![-460, -456, 152, -681, -630]], ![![-217, -216, 71, -324, -296]], ![![-325, -322, 108, -480, -445]]]
  g := ![![![-289, 1743, 989, -561, -1424], ![-332, 2007, 1139, -646, -1640], ![-383, 2313, 1311, -744, -1888], ![246, -1486, -843, 478, 1214], ![93, -561, -319, 181, 459]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![1635, -524, -439, 95, 623]] ![![-6, -4, 2, -7, -7]]
  ![![-2613, 926, 778, -229, -1130]] where
 M := ![![![-2613, 926, 778, -229, -1130]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![-2613, 926, 778, -229, -1130]] ![![-6, -4, 2, -7, -7]]
  ![![12824, 7098, -4081, 13142, 13560]] where
 M := ![![![12824, 7098, -4081, 13142, 13560]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![12824, 7098, -4081, 13142, 13560]] ![![730, 1743, 989, -561, -1424]]
  ![![5400, 22393, 13021, -7072, -18740]] where
 M := ![![![5400, 22393, 13021, -7072, -18740]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![5400, 22393, 13021, -7072, -18740]] ![![730, 1743, 989, -561, -1424]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![44237032, 105494656, 59856514, -33955258, -86184836]]]
 hmul := by decide  
 g := ![![![![22118516, 52747328, 29928257, -16977629, -43092418]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1219, -594, -264, 232, 386]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![-1219, -594, -264, 232, 386]] 
 ![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 2, 0, 1, 0], ![2, 2, 0, 0, 1]] where
  M :=![![![-1219, -594, -264, 232, 386], ![116, -1225, -750, 384, 1084], ![-796, -1014, -593, 440, 904], ![562, 716, 364, -193, -502], ![64, 362, 180, -44, -225]]]
  hmulB := by decide  
  f := ![![![215, 390, -596, -592, 1174]], ![![-3596, -3959, 5106, 1056, -7084]], ![![6969, 6488, -7649, 2040, 7930]], ![![-3585, -3180, 3636, -1593, -3308]], ![![1602, 752, -356, 3020, -1797]]]
  g := ![![![-653, -610, -264, 232, 386], ![-562, -1387, -750, 384, 1084], ![-817, -1234, -593, 440, 904], ![465, 702, 364, -193, -502], ![126, 300, 180, -44, -225]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P0 : CertificateIrreducibleZModOfList' 3 2 2 1 [2, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 2], [0, 1]]
 g := ![![[1, 1]], ![[2, 2]]]
 h' := ![![[1, 2], [0, 1]], ![[0, 1], [1, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [2, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 2
  hpos := by decide
  P := [2, 2, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![153669195, 148503234, -22951556, 274437478, 187044311]
  a := ![-2547, -2778, 1994, -1752, -4457]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-157301783, -258153448, -22951556, 274437478, 187044311]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 9 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-12, -28, -7, 15, 6]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![-12, -28, -7, 15, 6]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![-12, -28, -7, 15, 6], ![30, 19, -76, -6, 108], ![-264, -266, 259, -60, -264], ![59, 50, -11, 68, -44], ![-141, -112, 135, -95, -99]]]
  hmulB := by decide  
  f := ![![![-652, 24, 197, -267, -420]], ![![-242, -385, 84, -510, -432]], ![![-2400, -2294, 791, -3468, -3216]], ![![-1087, -1138, 361, -1674, -1526]], ![![-2081, -1596, 675, -2597, -2513]]]
  g := ![![![-8, -28, -7, 15, 6], ![-62, 19, -76, -6, 108], ![88, -266, 259, -60, -264], ![49, 50, -11, 68, -44], ![19, -112, 135, -95, -99]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![-1219, -594, -264, 232, 386]] ![![-1219, -594, -264, 232, 386]]
  ![![1782289, 2025276, 1077796, -688824, -1556400]] where
 M := ![![![1782289, 2025276, 1077796, -688824, -1556400]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![1782289, 2025276, 1077796, -688824, -1556400]] ![![-12, -28, -7, 15, 6]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![-66355548, -158241984, -89784771, 50932887, 129277254]]]
 hmul := by decide  
 g := ![![![![-22118516, -52747328, -29928257, 16977629, 43092418]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N0, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 73, -103, -66, 176]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![53, 73, -103, -66, 176]] 
 ![![5, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![53, 73, -103, -66, 176], ![-530, -550, 689, 40, -880], ![2534, 2195, -2470, 1308, 2080], ![-258, -16, -142, -849, 804], ![1240, 895, -869, 1258, 141]]]
  hmulB := by decide  
  f := ![![![357, 1321, 763, -414, -1096]], ![![146, 284, 157, -88, -224]], ![![142, 355, 188, -84, -256]], ![![141, 583, 331, -167, -468]], ![![45, 196, 104, -40, -139]]]
  g := ![![![15, 73, -103, -66, 176], ![46, -550, 689, 40, -880], ![-694, 2195, -2470, 1308, 2080], ![297, -16, -142, -849, 804], ![-535, 895, -869, 1258, 141]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![53, 73, -103, -66, 176]] ![![53, 73, -103, -66, 176]]
  ![![-61615, -103790, 155676, 142140, -297400]] where
 M := ![![![-61615, -103790, 155676, 142140, -297400]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![-61615, -103790, 155676, 142140, -297400]] ![![53, 73, -103, -66, 176]]
  ![![40777969, 125848185, -211427965, -291266862, 476644200]] where
 M := ![![![40777969, 125848185, -211427965, -291266862, 476644200]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![40777969, 125848185, -211427965, -291266862, 476644200]] ![![53, 73, -103, -66, 176]]
  ![![65888889393, -99067264396, 231892426812, 572698772664, -710311372304]] where
 M := ![![![65888889393, -99067264396, 231892426812, 572698772664, -710311372304]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![65888889393, -99067264396, 231892426812, 572698772664, -710311372304]] ![![53, 73, -103, -66, 176]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![-384929214194955, -76591097378875, -111880838188075, -1084789027355850, 941407794697600]]]
 hmul := by decide  
 g := ![![![![-76985842838991, -15318219475775, -22376167637615, -216957805471170, 188281558939520]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6, -14, -9, 3, 14]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![-6, -14, -9, 3, 14]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![2, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![4, 1, 0, 0, 1]] where
  M :=![![![-6, -14, -9, 3, 14], ![-14, -25, 2, 10, -4], ![44, 32, -73, 12, 88], ![-9, 2, 17, -18, -12], ![35, 34, -31, 13, 27]]]
  hmulB := by decide  
  f := ![![![70, -10, -21, 21, 40]], ![![38, 89, -14, 110, 88]], ![![96, 68, -31, 114, 112]], ![![73, 30, -23, 64, 70]], ![![97, 57, -31, 103, 105]]]
  g := ![![![-8, -4, -9, 3, 14], ![-6, -3, 2, 10, -4], ![-30, -8, -73, 12, 88], ![11, 2, 17, -18, -12], ![-9, 1, -31, 13, 27]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [1, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 6], [0, 1]]
 g := ![![[4, 1], [3, 1]], ![[0, 6], [6, 6]]]
 h' := ![![[3, 6], [4, 1], [0, 1]], ![[0, 1], [0, 6], [3, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [2, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 2
  hpos := by decide
  P := [1, 4, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![461305, 447972, -74159, 814548, 572313]
  a := ![-139, -151, 107, -99, -239]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-705403, -17763, -74159, 814548, 572313]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1855, -4424, -2510, 1424, 3614]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![-1855, -4424, -2510, 1424, 3614]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![5, 2, 1, 0, 0], ![2, 4, 0, 1, 0], ![0, 5, 0, 0, 1]] where
  M :=![![![-1855, -4424, -2510, 1424, 3614], ![-2136, -5095, -2892, 1640, 4164], ![-2464, -5872, -3327, 1888, 4792], ![1582, 3772, 2140, -1213, -3082], ![596, 1424, 810, -460, -1165]]]
  hmulB := by decide  
  f := ![![![-593, 216, 174, -40, -246]], ![![392, -129, -116, 40, 172]], ![![-339, 138, 99, -8, -130]], ![![80, -16, -24, 19, 42]], ![![276, -83, -82, 36, 127]]]
  g := ![![![1121, -3310, -2510, 1424, 3614], ![1292, -3813, -2892, 1640, 4164], ![1485, -4390, -3327, 1888, 4792], ![-956, 2822, 2140, -1213, -3082], ![-362, 1067, 810, -460, -1165]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P1 : CertificateIrreducibleZModOfList' 7 2 2 2 [6, 1, 1] where
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
 g := ![![[6, 4], [6, 1]], ![[2, 3], [5, 6]]]
 h' := ![![[6, 6], [6, 2], [0, 1]], ![[0, 1], [4, 5], [6, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [4, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N1 : CertifiedPrimeIdeal' SI7N1 7 where
  n := 2
  hpos := by decide
  P := [6, 1, 1]
  hirr := P7P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![24652411, 23540051, -3010026, 45219085, 28606964]
  a := ![1030, 1133, -838, 655, 1873]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7247947, -42050151, -3010026, 45219085, 28606964]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N1 B_one_repr
lemma NI7N1 : Nat.card (O ⧸ I7N1) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N1

def I7N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-132, -173, 186, -19, -212]] i)))

def SI7N2: IdealEqSpanCertificate' Table ![![-132, -173, 186, -19, -212]] 
 ![![7, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![-132, -173, 186, -19, -212], ![616, 510, -521, 498, 272], ![-590, 275, -938, -3080, 3440], ![-1113, -1306, 1747, 644, -2634], ![715, 1241, -1882, -1793, 3651]]]
  hmulB := by decide  
  f := ![![![4508, 8969, 3942, -573, -4534]], ![![4976, 8891, 3129, 1003, -2598]], ![![10742, 13456, -194, 11463, 8074]], ![![5509, 6855, -155, 5953, 4250]], ![![7507, 9182, -404, 8370, 6171]]]
  g := ![![![124, -173, 186, -19, -212], ![-383, 510, -521, 498, 272], ![-33, 275, -938, -3080, 3440], ![878, -1306, 1747, 644, -2634], ![-774, 1241, -1882, -1793, 3651]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N2 : Nat.card (O ⧸ I7N2) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N2)

lemma isPrimeI7N2 : Ideal.IsPrime I7N2 := prime_ideal_of_norm_prime hp7.out _ NI7N2
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![-6, -14, -9, 3, 14]] ![![-1855, -4424, -2510, 1424, 3614]]
  ![![76300, 181974, 103251, -58575, -148664]] where
 M := ![![![76300, 181974, 103251, -58575, -148664]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI7N1 : IdealMulLeCertificate' Table 
  ![![76300, 181974, 103251, -58575, -148664]] ![![-132, -173, 186, -19, -212]]
  ![![7, 0, 0, 0, 0]] where
 M := ![![![5509, 7791, -10969, -7476, 19054]]]
 hmul := by decide  
 g := ![![![![787, 1113, -1567, -1068, 2722]]]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-246, -220, 253, -103, -236]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-246, -220, 253, -103, -236]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![1, 9, 4, 1, 0], ![0, 6, 10, 0, 1]] where
  M :=![![![-246, -220, 253, -103, -236], ![634, 371, -280, 942, -352], ![1384, 2650, -4101, -4292, 8240], ![-2249, -2382, 3015, 336, -3970], ![2497, 3120, -4249, -2013, 6735]]]
  hmulB := by decide  
  f := ![![![-530, 240, 181, -45, -254]], ![![398, -59, -88, 50, 148]], ![![-32, 306, 37, 228, 104]], ![![285, 85, -50, 133, 154]], ![![193, 258, -17, 251, 189]]]
  g := ![![![-13, 193, 275, -103, -236], ![-28, -545, -48, 942, -352], ![516, -742, -6303, -4292, 8240], ![-235, 1674, 3761, 336, -3970], ![410, -1743, -5777, -2013, 6735]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [2, 7, 8, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 1, 8], [8, 9, 3], [0, 1]]
 g := ![![[8, 7, 3], [2, 3, 1], []], ![[7, 4, 10, 2], [9, 2, 2, 10], [10, 9]], ![[1, 1], [1, 3, 1, 3], [4, 9]]]
 h' := ![![[6, 1, 8], [7, 2, 5], [0, 0, 1], [0, 1]], ![[8, 9, 3], [0, 7, 6], [5, 1, 9], [6, 1, 8]], ![[0, 1], [6, 2], [1, 10, 1], [8, 9, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 3], []]
 b := ![[], [4, 6, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [2, 7, 8, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-14691602900, -15084858412, 5901343002, -19957678682, -22416389006]
  a := ![-241, -275, 228, -100, -509]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![478734162, 27184780342, 28172358890, -19957678682, -22416389006]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 1331 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-530, 240, 181, -45, -254]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![-530, 240, 181, -45, -254]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![9, 7, 1, 0, 0], ![9, 9, 0, 1, 0], ![5, 6, 0, 0, 1]] where
  M :=![![![-530, 240, 181, -45, -254], ![398, -59, -88, 50, 148], ![-32, 306, 37, 228, 104], ![211, 2, -87, 146, 200], ![55, 132, -29, 181, 151]]]
  hmulB := by decide  
  f := ![![![-246, -220, 253, -103, -236]], ![![634, 371, -280, 942, -352]], ![![328, 297, -344, 125, 332]], ![![113, -93, 252, 717, -842]], ![![461, 386, -424, 284, 313]]]
  g := ![![![-44, 82, 181, -45, -254], ![0, -71, -88, 50, 148], ![-267, -239, 37, 228, 104], ![-120, -173, -87, 146, 200], ![-188, -200, -29, 181, 151]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P1 : CertificateIrreducibleZModOfList' 11 2 2 3 [4, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 10], [0, 1]]
 g := ![![[6, 3], [8, 4], [1]], ![[0, 8], [0, 7], [1]]]
 h' := ![![[9, 10], [1, 6], [7, 9], [0, 1]], ![[0, 1], [0, 5], [0, 2], [9, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [2, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N1 : CertifiedPrimeIdeal' SI11N1 11 where
  n := 2
  hpos := by decide
  P := [4, 2, 1]
  hirr := P11P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![269708, 167636, 37780, 646080, -117856]
  a := ![98, 126, -136, -32, 304]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-481432, -473128, 37780, 646080, -117856]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N1 B_one_repr
lemma NI11N1 : Nat.card (O ⧸ I11N1) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-246, -220, 253, -103, -236]] ![![-530, 240, 181, -45, -254]]
  ![![11, 0, 0, 0, 0]] where
 M := ![![![11, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC11 : ContainsPrimesAboveP 11 ![I11N0, I11N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
    exact isPrimeI11N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 11 (by decide) (𝕀 ⊙ MulI11N0)
instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-79, -82, 22, -112, -100]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-79, -82, 22, -112, -100]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![2, 8, 7, 1, 0], ![7, 2, 0, 0, 1]] where
  M :=![![![-79, -82, 22, -112, -100], ![-516, -517, 166, -760, -696], ![-3436, -3422, 1131, -5096, -4688], ![-1660, -1648, 552, -2471, -2276], ![-2396, -2382, 794, -3560, -3279]]]
  hmulB := by decide  
  f := ![![![237, -86, -70, 16, 100]], ![![-156, 51, 50, -8, -72]], ![![124, -10, -61, 8, 80]], ![![2, 14, -11, 1, 12]], ![![107, -38, -32, 8, 45]]]
  g := ![![![65, 78, 62, -112, -100], ![452, 535, 422, -760, -696], ![3044, 3594, 2831, -5096, -4688], ![1478, 1744, 1373, -2471, -2276], ![2129, 2512, 1978, -3560, -3279]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [10, 0, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 1, 3], [0, 11, 10], [0, 1]]
 g := ![![[4, 10, 12], [12, 1], [1]], ![[1, 11, 8, 4], [0, 4], [4, 8, 0, 1]], ![[0, 9, 0, 10], [1, 1], [11, 4, 12, 12]]]
 h' := ![![[12, 1, 3], [6, 3, 8], [3, 0, 12], [0, 1]], ![[0, 11, 10], [4, 8, 6], [11, 1, 2], [12, 1, 3]], ![[0, 1], [0, 2, 12], [7, 12, 12], [0, 11, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 12], []]
 b := ![[], [10, 3, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [10, 0, 1, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![59661509286, 60026812945, -22497088001, 83914937318, 85081701030]
  a := ![374, 413, -313, 219, 701]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-54133867120, -60112006743, -46915511479, 83914937318, 85081701030]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 2197 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![237, -86, -70, 16, 100]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![237, -86, -70, 16, 100]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![11, 7, 1, 0, 0], ![6, 7, 0, 1, 0], ![3, 5, 0, 0, 1]] where
  M :=![![![237, -86, -70, 16, 100], ![-156, 51, 50, -8, -72], ![124, -10, -61, 8, 80], ![-68, 16, 24, -11, -28], ![44, 6, -26, 8, 29]]]
  hmulB := by decide  
  f := ![![![-79, -82, 22, -112, -100]], ![![-516, -517, 166, -760, -696]], ![![-609, -611, 195, -896, -820]], ![![-442, -443, 142, -651, -596]], ![![-401, -401, 130, -592, -543]]]
  g := ![![![47, -16, -70, 16, 100], ![-34, 9, 50, -8, -72], ![39, -3, -61, 8, 80], ![-14, 5, 24, -11, -28], ![15, -1, -26, 8, 29]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P1 : CertificateIrreducibleZModOfList' 13 2 2 3 [6, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 12], [0, 1]]
 g := ![![[7, 9], [9], [10, 1]], ![[6, 4], [9], [7, 12]]]
 h' := ![![[10, 12], [10, 3], [5, 3], [0, 1]], ![[0, 1], [1, 10], [9, 10], [10, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [8, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N1 : CertifiedPrimeIdeal' SI13N1 13 where
  n := 2
  hpos := by decide
  P := [6, 3, 1]
  hirr := P13P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![246981, 243241, -50116, 418045, 323412]
  a := ![-100, -107, 72, -79, -161]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-206173, -303794, -50116, 418045, 323412]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N1 B_one_repr
lemma NI13N1 : Nat.card (O ⧸ I13N1) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-79, -82, 22, -112, -100]] ![![237, -86, -70, 16, 100]]
  ![![13, 0, 0, 0, 0]] where
 M := ![![![13, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1386, 3334, -5397, -6645, 11582]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![1386, 3334, -5397, -6645, 11582]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![12, 14, 12, 14, 1]] where
  M :=![![![1386, 3334, -5397, -6645, 11582], ![-35798, -40597, 53078, 14602, -76324], ![224228, 211676, -251653, 55548, 269464], ![-48177, -29950, 24617, -65514, 18132], ![131603, 110830, -122275, 78853, 92523]]]
  hmulB := by decide  
  f := ![![![1130, -26, -87, -69, 104]], ![![-590, 523, 458, -350, -760]], ![![-172, -460, 403, -1284, -1280]], ![![-759, -586, 29, -484, -378]], ![![-463, -436, 629, -1687, -1803]]]
  g := ![![![-8094, -9342, -8493, -9929, 11582], ![51770, 60467, 56998, 63714, -76324], ![-177020, -209460, -205013, -218644, 269464], ![-15633, -16694, -11351, -18786, 18132], ![-57569, -69676, -72503, -71557, 92523]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 4 2 4 [16, 2, 13, 8, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 0, 15], [9, 16, 2, 13], [0, 0, 0, 4], [0, 1]]
 g := ![![[0, 0, 15, 13], [16, 2, 13], [1], []], ![[9], [0, 15, 13], [1, 15, 4], [4]], ![[0, 0, 0, 4], [], [0, 2, 4], [4, 9, 16]], ![[0, 1, 2, 13, 8, 1], [16], [], [0, 8, 16]]]
 h' := ![![[0, 0, 15], [0, 0, 0, 9], [1, 15, 4, 9], [0, 0, 1], [0, 1]], ![[9, 16, 2, 13], [0, 15], [0, 0, 0, 8], [4, 9, 16, 2], [0, 0, 15]], ![[0, 0, 0, 4], [0, 0, 4], [0, 2], [0, 0, 0, 15], [9, 16, 2, 13]], ![[0, 1], [16, 2, 13, 8], [0, 0, 13], [0, 8], [0, 0, 0, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [2, 14, 1], []]
 b := ![[], [], [6, 10, 12, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 4
  hpos := by decide
  P := [16, 2, 13, 8, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![504854591933220, 499008736236358, -159875896175228, 762470015172172, 674957503772524]
  a := ![325, 365, -289, 164, 647]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-446743261961004, -526493900975234, -485845055379148, -510996178684892, 674957503772524]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 83521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1130, -26, -87, -69, 104]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![1130, -26, -87, -69, 104]] 
 ![![17, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![15, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![1130, -26, -87, -69, 104], ![-590, 523, 458, -350, -760], ![-172, -460, 403, -1284, -1280], ![-759, -586, 29, -484, -378], ![-481, -698, 83, -767, -607]]]
  hmulB := by decide  
  f := ![![![1386, 3334, -5397, -6645, 11582]], ![![-1372, -623, 265, -2659, 1642]], ![![13516, 13236, -16073, 1704, 18576]], ![![-1611, 1180, -3314, -9717, 11286]], ![![8149, 7500, -8780, 2684, 8849]]]
  g := ![![![131, -26, -87, -69, 104], ![113, 523, 458, -350, -760], ![1648, -460, 403, -1284, -1280], ![797, -586, 29, -484, -378], ![1177, -698, 83, -767, -607]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![1386, 3334, -5397, -6645, 11582]] ![![1130, -26, -87, -69, 104]]
  ![![17, 0, 0, 0, 0]] where
 M := ![![![17, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1043, 338, 344, -40, -504]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-1043, 338, 344, -40, -504]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![15, 8, 15, 4, 1]] where
  M :=![![![-1043, 338, 344, -40, -504], ![896, 13, -510, 16, 688], ![-1620, -902, 1325, -584, -1248], ![408, -56, -48, 409, -216], ![-724, -414, 492, -568, -199]]]
  hmulB := by decide  
  f := ![![![1519, 1506, -508, 2264, 2088]], ![![10184, 10123, -3374, 15136, 13936]], ![![68172, 67794, -22549, 101272, 93216]], ![![33016, 32840, -10912, 49035, 45128]], ![![68763, 68378, -22749, 102156, 94033]]]
  g := ![![![343, 230, 416, 104, -504], ![-496, -289, -570, -144, 688], ![900, 478, 1055, 232, -1248], ![192, 88, 168, 67, -216], ![119, 62, 183, 12, -199]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 4 2 4 [8, 16, 17, 2, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 5, 11, 1], [18, 18], [2, 14, 8, 18], [0, 1]]
 g := ![![[17, 14, 7, 9], [17, 13, 3, 4], [1], []], ![[8, 0, 18, 7, 9, 5], [4, 17, 2, 14, 4, 7], [0, 3, 1], [17, 1, 1]], ![[1, 11, 18, 10], [3, 0, 10, 15], [1], []], ![[4, 7, 1, 17, 3, 14], [10, 2, 9, 8, 7, 12], [17, 18, 1], [17, 1, 1]]]
 h' := ![![[16, 5, 11, 1], [16, 11, 1, 3], [11, 3, 2, 17], [0, 0, 1], [0, 1]], ![[18, 18], [13, 17, 17, 9], [17, 18, 7, 8], [6, 13, 7, 18], [16, 5, 11, 1]], ![[2, 14, 8, 18], [3, 1, 11, 16], [12, 7, 8, 2], [1, 2, 1], [18, 18]], ![[0, 1], [4, 9, 9, 10], [17, 10, 2, 11], [1, 4, 10, 1], [2, 14, 8, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [2], []]
 b := ![[], [], [15, 2, 11, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 4
  hpos := by decide
  P := [8, 16, 17, 2, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![62827695365108, 62023193005716, -19826194085220, 95031721185408, 83626572576474]
  a := ![194, 219, -176, 93, 393]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-62714257541158, -31946809874004, -67064462249070, -12603924690552, 83626572576474]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 130321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1519, 1506, -508, 2264, 2088]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![1519, 1506, -508, 2264, 2088]] 
 ![![19, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![12, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![1519, 1506, -508, 2264, 2088], ![10184, 10123, -3374, 15136, 13936], ![68172, 67794, -22549, 101272, 93216], ![33016, 32840, -10912, 49035, 45128], ![47596, 47338, -15736, 70696, 65067]]]
  hmulB := by decide  
  f := ![![![-1043, 338, 344, -40, -504]], ![![-392, 143, 118, -16, -176]], ![![-744, 166, 287, -56, -384]], ![![-253, 86, 88, 11, -144]], ![![-93, -4, 44, -32, -37]]]
  g := ![![![-939, 1506, -508, 2264, 2088], ![-6312, 10123, -3374, 15136, 13936], ![-42272, 67794, -22549, 101272, 93216], ![-20477, 32840, -10912, 49035, 45128], ![-29517, 47338, -15736, 70696, 65067]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-1043, 338, 344, -40, -504]] ![![1519, 1506, -508, 2264, 2088]]
  ![![19, 0, 0, 0, 0]] where
 M := ![![![19, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0)
instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10, -11, 12, 1, -16]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![-10, -11, 12, 1, -16]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![20, 5, 16, 1, 0], ![22, 1, 6, 0, 1]] where
  M :=![![![-10, -11, 12, 1, -16], ![44, 38, -47, 18, 40], ![-130, -79, 46, -208, 64], ![-49, -66, 87, 46, -158], ![-21, 15, -52, -141, 145]]]
  hmulB := by decide  
  f := ![![![-2750, 991, 804, -193, -1142]], ![![1768, -644, -521, 126, 740]], ![![-1142, 407, 332, -80, -472]], ![![-2771, 994, 808, -194, -1148]], ![![-2865, 1031, 837, -201, -1189]]]
  g := ![![![14, 0, 4, 1, -16], ![-52, -4, -25, 18, 40], ![114, 39, 130, -208, 64], ![109, -6, 13, 46, -158], ![-17, 25, 58, -141, 145]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [18, 15, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 21, 17], [6, 1, 6], [0, 1]]
 g := ![![[3, 10, 2], [13, 17, 6], [12, 21, 1], []], ![[13, 20, 4, 7], [15, 6, 7, 17], [22, 9, 4, 17], [21, 13]], ![[6, 21, 4, 8], [19, 3, 3, 13], [1, 7, 14, 1], [9, 13]]]
 h' := ![![[15, 21, 17], [19, 17, 18], [14, 17, 11], [0, 0, 1], [0, 1]], ![[6, 1, 6], [4, 21, 8], [12, 6, 1], [8, 12, 1], [15, 21, 17]], ![[0, 1], [15, 8, 20], [18, 0, 11], [12, 11, 21], [6, 1, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 10], []]
 b := ![[], [21, 3, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [18, 15, 2, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3920209732, 3945182156, -1481770738, 5507785992, 5595409688]
  a := ![151, 167, -127, 88, 284]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9971066228, -1269093804, -5355600206, 5507785992, 5595409688]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 12167 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![330, 299, -348, 121, 340]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![330, 299, -348, 121, 340]] 
 ![![23, 0, 0, 0, 0], ![16, 1, 0, 0, 0], ![20, 0, 1, 0, 0], ![17, 0, 0, 1, 0], ![16, 0, 0, 0, 1]] where
  M :=![![![330, 299, -348, 121, 340], ![-924, -586, 495, -1214, 288], ![-1310, -3017, 4846, 5816, -10288], ![2867, 3086, -3937, -598, 5302], ![-3001, -3875, 5344, 2851, -8707]]]
  hmulB := by decide  
  f := ![![![774, 3033, 2520, -2593, -4426]], ![![360, 2048, 1951, -2254, -3596]], ![![-974, 1131, 2896, -4916, -6416]], ![![-333, 1257, 2059, -3123, -4306]], ![![-701, 845, 2124, -3593, -4697]]]
  g := ![![![-217, 299, -348, 121, 340], ![634, -586, 495, -1214, 288], ![686, -3017, 4846, 5816, -10288], ![-1845, 3086, -3937, -598, 5302], ![1868, -3875, 5344, 2851, -8707]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1

def I23N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3479, -542, -90, 370, 178]] i)))

def SI23N2: IdealEqSpanCertificate' Table ![![-3479, -542, -90, 370, 178]] 
 ![![23, 0, 0, 0, 0], ![22, 1, 0, 0, 0], ![22, 0, 1, 0, 0], ![20, 0, 0, 1, 0], ![21, 0, 0, 0, 1]] where
  M :=![![![-3479, -542, -90, 370, 178], ![1296, -2271, -1666, 1084, 2604], ![-452, -94, -1399, 3008, 3464], ![2080, 1888, 306, 775, 254], ![1026, 1758, 14, 1490, 989]]]
  hmulB := by decide  
  f := ![![![42027, 32338, -33254, 35722, 14590]], ![![39006, 32377, -35346, 25000, 25112]], ![![4610, -13470, 28625, 62628, -81708]], ![![59888, 50544, -55850, 35507, 42638]], ![![3935, -7656, 17148, 40204, -50937]]]
  g := ![![![-31, -542, -90, 370, 178], ![502, -2271, -1666, 1084, 2604], ![-4370, -94, -1399, 3008, 3464], ![-2914, 1888, 306, 775, 254], ![-3849, 1758, 14, 1490, 989]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N2 : Nat.card (O ⧸ I23N2) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N2)

lemma isPrimeI23N2 : Ideal.IsPrime I23N2 := prime_ideal_of_norm_prime hp23.out _ NI23N2
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![-10, -11, 12, 1, -16]] ![![330, 299, -348, 121, 340]]
  ![![42027, 32338, -33254, 35722, 14590]] where
 M := ![![![42027, 32338, -33254, 35722, 14590]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI23N1 : IdealMulLeCertificate' Table 
  ![![42027, 32338, -33254, 35722, 14590]] ![![-3479, -542, -90, 370, 178]]
  ![![23, 0, 0, 0, 0]] where
 M := ![![![23, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC23 : ContainsPrimesAboveP 23 ![I23N0, I23N1, I23N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N1
    exact isPrimeI23N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 23 (by decide) (𝕀 ⊙ MulI23N0 ⊙ MulI23N1)


lemma PB1640I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB1640I0 : PrimesBelowBoundCertificateInterval O 1 23 1640 where
  m := 9
  g := ![5, 3, 5, 3, 2, 2, 2, 2, 3]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB1640I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N0, I3N1]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1, I7N2]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1]
    · exact ![I17N0, I17N1]
    · exact ![I19N0, I19N1]
    · exact ![I23N0, I23N1, I23N2]
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
    · exact ![9, 9, 3]
    · exact ![5, 5, 5, 5, 5]
    · exact ![49, 49, 7]
    · exact ![1331, 121]
    · exact ![2197, 169]
    · exact ![83521, 17]
    · exact ![130321, 19]
    · exact ![12167, 23, 23]
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
      exact NI11N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
      exact NI23N2
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I5N0, I7N0, I7N1, I7N2, I11N0, I11N1, I13N1, I17N1, I19N1, I23N1, I23N2]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N0, I3N1], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N0, I7N1, I7N2], [I11N0, I11N1], [I13N1], [I17N1], [I19N1], [I23N1, I23N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
