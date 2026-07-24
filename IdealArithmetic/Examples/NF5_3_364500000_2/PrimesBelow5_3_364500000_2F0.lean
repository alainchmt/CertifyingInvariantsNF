
import IdealArithmetic.Examples.NF5_3_364500000_2.RI5_3_364500000_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9590, 5647, 1662, -2570, -2041]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![9590, 5647, 1662, -2570, -2041]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![9590, 5647, 1662, -2570, -2041], ![48984, 28563, 8270, -13004, -10280], ![123360, 72163, 21007, -32850, -26008], ![287604, 168096, 48862, -76523, -60560], ![400548, 234195, 68118, -106612, -84387]]]
  hmulB := by decide  
  f := ![![![-119, -110, 44, 86, -59]], ![![708, 373, -314, -192, 172]], ![![-2064, -941, 909, 374, -384]], ![![4254, 1722, -1926, -531, 662]], ![![-5358, -2161, 2400, 644, -809]]]
  g := ![![![4795, 5647, 1662, -2570, -2041], ![24492, 28563, 8270, -13004, -10280], ![61680, 72163, 21007, -32850, -26008], ![143802, 168096, 48862, -76523, -60560], ![200274, 234195, 68118, -106612, -84387]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1063, -830, -377, 131, 149]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![-1063, -830, -377, 131, 149]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-1063, -830, -377, 131, 149], ![-3576, -2817, -1326, 438, 524], ![-6288, -4895, -2207, 770, 876], ![-8724, -6887, -3250, 1078, 1278], ![-9024, -7008, -3145, 1097, 1254]]]
  hmulB := by decide  
  f := ![![![-1370, -277, 176, 135, 18]], ![![-216, -561, -376, 248, 270]], ![![-3240, -1533, -269, 704, 496]], ![![-5844, -3498, -1057, 1591, 1273]], ![![-9835, -5055, -1130, 2313, 1713]]]
  g := ![![![-606, -830, -377, 131, 149], ![-2050, -2817, -1326, 438, 524], ![-3582, -4895, -2207, 770, 876], ![-5001, -6887, -3250, 1078, 1278], ![-5139, -7008, -3145, 1097, 1254]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, -9, -5, 4, 4]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![-7, -9, -5, 4, 4]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-7, -9, -5, 4, 4], ![-96, -48, -10, 22, 16], ![-192, -119, -38, 54, 44], ![-480, -279, -80, 127, 100], ![-648, -387, -117, 176, 141]]]
  hmulB := by decide  
  f := ![![![-14, -9, 0, 2, 0]], ![![0, -5, -11, 0, 4]], ![![-55, -32, 3, 6, 0]], ![![0, -15, -27, 3, 8]], ![![-79, -43, 6, 6, 1]]]
  g := ![![![-3, -9, -5, 4, 4], ![-51, -48, -10, 22, 16], ![-99, -119, -38, 54, 44], ![-250, -279, -80, 127, 100], ![-336, -387, -117, 176, 141]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![9590, 5647, 1662, -2570, -2041]] ![![-1063, -830, -377, 131, 149]]
  ![![166, 129, 59, -21, -24]] where
 M := ![![![166, 129, 59, -21, -24]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![166, 129, 59, -21, -24]] ![![-1063, -830, -377, 131, 149]]
  ![![-608974, -477159, -220119, 74712, 87080]] where
 M := ![![![-608974, -477159, -220119, 74712, 87080]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![-608974, -477159, -220119, 74712, 87080]] ![![-7, -9, -5, 4, 4]]
  ![![43330, 33951, 15662, -5316, -6196]] where
 M := ![![![43330, 33951, 15662, -5316, -6196]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![43330, 33951, 15662, -5316, -6196]] ![![-7, -9, -5, 4, 4]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![-3022, -2380, -1104, 362, 428]]]
 hmul := by decide  
 g := ![![![![-1511, -1190, -552, 181, 214]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![27, 9, -14, -2, 4]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![27, 9, -14, -2, 4]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![27, 9, -14, -2, 4], ![-96, -35, 38, 4, -8], ![96, 19, -55, 6, 8], ![-48, 0, 10, -25, 16], ![0, -39, -18, 38, -17]]]
  hmulB := by decide  
  f := ![![![-711, -25, 184, 18, -52]], ![![416, 27, -98, -16, 24]], ![![-288, 11, 91, -2, -32]], ![![176, 62, -2, -29, -16]], ![![-256, 65, 124, -26, -57]]]
  g := ![![![9, 9, -14, -2, 4], ![-32, -35, 38, 4, -8], ![32, 19, -55, 6, 8], ![-16, 0, 10, -25, 16], ![0, -39, -18, 38, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-55, -33, -10, 15, 12]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![-55, -33, -10, 15, 12]] 
 ![![3, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![-55, -33, -10, 15, 12], ![-288, -167, -48, 76, 60], ![-720, -422, -123, 192, 152], ![-1680, -982, -286, 447, 354], ![-2340, -1369, -398, 623, 493]]]
  hmulB := by decide  
  f := ![![![3, -1, -4, -1, 2]], ![![-14, -9, 0, 2, 0]], ![![17, 3, -15, -3, 6]], ![![-55, -27, 14, 6, -4]], ![![46, 11, -32, -5, 11]]]
  g := ![![![-6, -33, -10, 15, 12], ![-34, -167, -48, 76, 60], ![-83, -422, -123, 192, 152], ![-195, -982, -286, 447, 354], ![-271, -1369, -398, 623, 493]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![27, 9, -14, -2, 4]] ![![27, 9, -14, -2, 4]]
  ![![-1383, -494, 642, 100, -176]] where
 M := ![![![-1383, -494, 642, 100, -176]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![-1383, -494, 642, 100, -176]] ![![-55, -33, -10, 15, 12]]
  ![![-63, -43, 24, 27, -20]] where
 M := ![![![-63, -43, 24, 27, -20]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![-63, -43, 24, 27, -20]] ![![-55, -33, -10, 15, 12]]
  ![![9, -2, -20, 4, 10]] where
 M := ![![![9, -2, -20, 4, 10]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N3 : IdealMulLeCertificate' Table 
  ![![9, -2, -20, 4, 10]] ![![-55, -33, -10, 15, 12]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![-15639, -9141, -2658, 4161, 3294]]]
 hmul := by decide  
 g := ![![![![-5213, -3047, -886, 1387, 1098]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-485, -283, -82, 129, 102]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![-485, -283, -82, 129, 102]] 
 ![![5, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-485, -283, -82, 129, 102], ![-2448, -1431, -416, 652, 516], ![-6192, -3618, -1051, 1648, 1304], ![-14424, -8430, -2450, 3839, 3038], ![-20100, -11747, -3414, 5349, 4233]]]
  hmulB := by decide  
  f := ![![![-121, -41, 52, 11, -16]], ![![-20, -7, 8, 4, -4]], ![![-154, -48, 69, 6, -16]], ![![-20, -20, 6, 21, -14]], ![![-84, -9, 40, -17, 3]]]
  g := ![![![59, -283, -82, 129, 102], ![300, -1431, -416, 652, 516], ![758, -3618, -1051, 1648, 1304], ![1768, -8430, -2450, 3839, 3038], ![2464, -11747, -3414, 5349, 4233]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![-485, -283, -82, 129, 102]] ![![-485, -283, -82, 129, 102]]
  ![![-2475143, -1446760, -420598, 658612, 521242]] where
 M := ![![![-2475143, -1446760, -420598, 658612, 521242]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![-2475143, -1446760, -420598, 658612, 521242]] ![![-485, -283, -82, 129, 102]]
  ![![-12630328037, -7382626341, -2146257204, 3360808455, 2659828104]] where
 M := ![![![-12630328037, -7382626341, -2146257204, 3360808455, 2659828104]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![-12630328037, -7382626341, -2146257204, 3360808455, 2659828104]] ![![-485, -283, -82, 129, 102]]
  ![![-64450843057439, -37672536320824, -10952058083512, 17149747623744, 13572740404776]] where
 M := ![![![-64450843057439, -37672536320824, -10952058083512, 17149747623744, 13572740404776]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![-64450843057439, -37672536320824, -10952058083512, 17149747623744, 13572740404776]] ![![-485, -283, -82, 129, 102]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![-328883870411539685, -192237819796564795, -55886860134134170, 87512825395485385, 69259844940047470]]]
 hmul := by decide  
 g := ![![![![-65776774082307937, -38447563959312959, -11177372026826834, 17502565079097077, 13851968988009494]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-131, 31, 68, -83, 38]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![-131, 31, 68, -83, 38]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![3, 1, 4, 5, 1]] where
  M :=![![![-131, 31, 68, -83, 38], ![-912, -647, 380, 440, -332], ![3984, 2000, -1751, -948, 880], ![-10104, -4348, 4518, 1549, -1730], ![12828, 5459, -5744, -1895, 2155]]]
  hmulB := by decide  
  f := ![![![-149, -21, 26, 9, -4]], ![![96, -61, -76, 20, 36]], ![![-432, -168, -9, 68, 40]], ![![-528, -342, -118, 141, 118]], ![![-813, -425, -102, 175, 131]]]
  g := ![![![-35, -1, -12, -39, 38], ![12, -45, 244, 300, -332], ![192, 160, -753, -764, 880], ![-702, -374, 1634, 1457, -1730], ![909, 472, -2052, -1810, 2155]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 4 2 2 [4, 2, 1, 1, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 2, 5, 6], [6, 3, 3, 3], [3, 1, 6, 5], [0, 1]]
 g := ![![[6, 0, 6, 1], []], ![[6, 1, 1, 5, 4, 6], [6, 4, 0, 0, 2, 6]], ![[6, 4, 1, 3], [0, 6, 1, 4, 5, 6]], ![[6, 3, 5, 4, 2, 6], [0, 6, 0, 4, 3, 6]]]
 h' := ![![[4, 2, 5, 6], [0, 0, 0, 1], [0, 1]], ![[6, 3, 3, 3], [5, 5, 1, 1], [4, 2, 5, 6]], ![[3, 1, 6, 5], [6, 6, 1], [6, 3, 3, 3]], ![[0, 1], [6, 3, 5, 5], [3, 1, 6, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [0, 3, 1], []]
 b := ![[], [], [6, 3, 6, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 4
  hpos := by decide
  P := [4, 2, 1, 1, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5961500288, -3471373727, -999186914, 1593862276, 1258612611]
  a := ![0, -7, 2, -4, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1391048303, -675712334, -861948194, -671314397, 1258612611]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 2401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 21, -26, -9, 4]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![149, 21, -26, -9, 4]] 
 ![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![149, 21, -26, -9, 4], ![-96, 61, 76, -20, -36], ![432, 168, 9, -68, -40], ![528, 342, 118, -141, -118], ![972, 469, 90, -201, -143]]]
  hmulB := by decide  
  f := ![![![131, -31, -68, 83, -38]], ![![149, 88, -64, -51, 42]], ![![-513, -299, 221, 171, -142]], ![![1537, 599, -694, -162, 220]], ![![-1739, -802, 772, 330, -335]]]
  g := ![![![33, 21, -26, -9, 4], ![-15, 61, 76, -20, -36], ![111, 168, 9, -68, -40], ![161, 342, 118, -141, -118], ![279, 469, 90, -201, -143]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![-131, 31, 68, -83, 38]] ![![149, 21, -26, -9, 4]]
  ![![7, 0, 0, 0, 0]] where
 M := ![![![-7, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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


def P11P0 : CertificateIrreducibleZModOfList' 11 5 2 3 [4, 0, 3, 2, 4, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 1, 9, 9, 1], [3, 3, 9, 2, 2], [4, 10, 1, 9, 2], [1, 7, 3, 2, 6], [0, 1]]
 g := ![![[3, 1, 1, 7, 5], [1], []], ![[8, 4, 3, 3, 9, 5, 0, 4], [9, 0, 9, 0, 4, 3, 5, 4], [2, 8, 3, 1]], ![[2, 9, 1, 10, 6, 2, 7, 2], [5, 8, 10, 1, 7, 2, 3, 7], [5, 9, 3, 4]], ![[6, 10, 5, 7, 10, 5, 3, 8], [10, 7, 1, 7, 0, 10, 4, 6], [7, 8, 9, 4]], ![[3, 3, 0, 3, 10, 4, 6, 7], [9, 5, 2, 8, 7, 4, 4, 7], [9, 8, 1, 3]]]
 h' := ![![[10, 1, 9, 9, 1], [7, 0, 8, 9, 7], [0, 0, 1], [0, 1]], ![[3, 3, 9, 2, 2], [3, 2, 0, 5, 9], [4, 10, 9, 1, 9], [10, 1, 9, 9, 1]], ![[4, 10, 1, 9, 2], [2, 1, 4, 5, 10], [0, 4, 3, 2, 3], [3, 3, 9, 2, 2]], ![[1, 7, 3, 2, 6], [8, 5, 5, 4, 2], [10, 4, 7, 5, 5], [4, 10, 1, 9, 2]], ![[0, 1], [1, 3, 5, 10, 5], [9, 4, 2, 3, 5], [1, 7, 3, 2, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 1, 1], [], [], []]
 b := ![[], [5, 4, 4, 10], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 5
  hpos := by decide
  P := [4, 0, 3, 2, 4, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3110975538361636, 1832234684129553, 681592615360932, -845780583684828, -772413929309418]
  a := ![3, -62, -1, -65, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![282815958032876, 166566789466323, 61962965032812, -76889143971348, -70219448119038]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-37, -23, -6, 10, 8]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-37, -23, -6, 10, 8]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![3, 2, 11, 1, 0], ![3, 6, 5, 0, 1]] where
  M :=![![![-37, -23, -6, 10, 8], ![-192, -111, -34, 52, 40], ![-480, -281, -83, 126, 104], ![-1152, -672, -182, 307, 232], ![-1536, -903, -282, 410, 339]]]
  hmulB := by decide  
  f := ![![![119, 89, 40, -14, -16]], ![![384, 307, 142, -48, -56]], ![![672, 523, 243, -82, -96]], ![![729, 568, 263, -89, -104]], ![![537, 421, 195, -66, -77]]]
  g := ![![![-7, -7, -12, 10, 8], ![-36, -35, -62, 52, 40], ![-90, -89, -153, 126, 104], ![-213, -206, -363, 307, 232], ![-291, -289, -499, 410, 339]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [5, 12, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 3, 2], [11, 9, 11], [0, 1]]
 g := ![![[8, 6, 3], [6, 9], [1]], ![[8, 2, 3, 6], [3, 1], [12, 1, 12, 8]], ![[10, 8, 5, 2], [11, 4], [11, 9, 2, 5]]]
 h' := ![![[12, 3, 2], [8, 3, 9], [8, 1, 10], [0, 1]], ![[11, 9, 11], [1, 9, 9], [4, 3, 1], [12, 3, 2]], ![[0, 1], [1, 1, 8], [2, 9, 2], [11, 9, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 12], []]
 b := ![[], [8, 4, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [5, 12, 3, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3222813, 1847475, 513468, -887637, -692016]
  a := ![1, -6, 1, -5, -4]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![612444, 598065, 1056735, -887637, -692016]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 2197 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-119, -89, -40, 14, 16]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![-119, -89, -40, 14, 16]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![3, 2, 1, 0, 0], ![7, 11, 0, 1, 0], ![11, 2, 0, 0, 1]] where
  M :=![![![-119, -89, -40, 14, 16], ![-384, -307, -142, 48, 56], ![-672, -523, -243, 82, 96], ![-960, -750, -342, 117, 136], ![-960, -749, -348, 118, 137]]]
  hmulB := by decide  
  f := ![![![37, 23, 6, -10, -8]], ![![192, 111, 34, -52, -40]], ![![75, 44, 13, -20, -16]], ![![271, 158, 46, -73, -56]], ![![179, 106, 32, -48, -39]]]
  g := ![![![-21, -15, -40, 14, 16], ![-70, -51, -142, 48, 56], ![-121, -87, -243, 82, 96], ![-173, -125, -342, 117, 136], ![-173, -125, -348, 118, 137]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P1 : CertificateIrreducibleZModOfList' 13 2 2 3 [4, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [7, 12], [0, 1]]
 g := ![![[8, 10], [10], [7, 1]], ![[0, 3], [10], [1, 12]]]
 h' := ![![[7, 12], [3, 7], [11, 6], [0, 1]], ![[0, 1], [0, 6], [1, 7], [7, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [1, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N1 : CertifiedPrimeIdeal' SI13N1 13 where
  n := 2
  hpos := by decide
  P := [4, 6, 1]
  hirr := P13P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-100729, -51854, -9505, 30042, 22941]
  a := ![1, 25, -3, 18, 13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-41143, -31476, -9505, 30042, 22941]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N1 B_one_repr
lemma NI13N1 : Nat.card (O ⧸ I13N1) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-37, -23, -6, 10, 8]] ![![-119, -89, -40, 14, 16]]
  ![![13, 0, 0, 0, 0]] where
 M := ![![![-13, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0, 0]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0, 0, 0]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]] where
  M :=![![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 5 2 4 [3, 9, 5, 15, 12, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 9, 11, 7, 2], [2, 4, 7, 11, 2], [9, 5, 11, 6, 10], [0, 15, 5, 10, 3], [0, 1]]
 g := ![![[2, 5, 13, 1, 2], [4, 10, 5, 1], [], []], ![[7, 5, 15, 2, 14, 9, 1, 4], [2, 15], [16, 8, 10, 8], [16, 1, 14, 4]], ![[9, 9, 0, 15, 16, 16], [11, 16, 1, 16], [14, 1, 12, 1], [11, 1, 13, 4]], ![[14, 9, 8, 0, 3, 5, 2, 6], [3, 6, 11, 2], [8, 8, 16, 15], [1, 3, 8, 15]], ![[0, 0, 13, 11, 2, 2, 3, 12], [11, 16, 16, 9], [5, 1, 15, 16], [14, 10, 3, 9]]]
 h' := ![![[11, 9, 11, 7, 2], [5, 2, 11, 12, 6], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[2, 4, 7, 11, 2], [13, 15, 15, 12, 11], [11, 2, 4, 10], [5, 0, 5, 3, 12], [11, 9, 11, 7, 2]], ![[9, 5, 11, 6, 10], [1, 6, 11, 12], [0, 14, 10, 12, 13], [5, 16, 9, 5, 16], [2, 4, 7, 11, 2]], ![[0, 15, 5, 10, 3], [4, 5, 1, 14, 2], [8, 1, 0, 10, 6], [10, 4, 14, 3, 10], [9, 5, 11, 6, 10]], ![[0, 1], [5, 6, 13, 1, 15], [15, 0, 3, 2, 14], [9, 14, 5, 6, 13], [0, 15, 5, 10, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14, 4, 6, 8], [], [], []]
 b := ![[], [4, 0, 11, 14, 13], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 5
  hpos := by decide
  P := [3, 9, 5, 15, 12, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8503859134759, 4810624413407, 1094710065614, -2114059499533, -1630912823650]
  a := ![-1, -7, 5, 5, -19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![500227007927, 282977906671, 64394709742, -124356441149, -95936048450]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-107, -7, 28, 4, -8]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-107, -7, 28, 4, -8]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![8, 11, 1, 0, 0], ![7, 7, 0, 1, 0], ![14, 12, 0, 0, 1]] where
  M :=![![![-107, -7, 28, 4, -8], ![192, 17, -54, -8, 16], ![-192, -27, 57, 10, -16], ![96, 22, -42, -3, 12], ![-264, -43, 80, 12, -19]]]
  hmulB := by decide  
  f := ![![![391, 307, 142, -48, -56]], ![![1344, 1053, 486, -164, -192]], ![![1064, 834, 385, -130, -152]], ![![811, 636, 294, -99, -116]], ![![1310, 1027, 474, -160, -187]]]
  g := ![![![-13, -13, 28, 4, -8], ![24, 25, -54, -8, 16], ![-26, -28, 57, 10, -16], ![15, 19, -42, -3, 12], ![-38, -41, 80, 12, -19]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [13, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 18], [0, 1]]
 g := ![![[14, 16], [], [7], [1]], ![[9, 3], [], [7], [1]]]
 h' := ![![[8, 18], [0, 4], [2], [6, 8], [0, 1]], ![[0, 1], [13, 15], [2], [13, 11], [8, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [7, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [13, 11, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![59677, 25708, -26226, -8878, 10506]
  a := ![0, -4, -2, -18, 10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![9713, 13172, -26226, -8878, 10506]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5293, -227, 1338, 152, -366]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![-5293, -227, 1338, 152, -366]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![12, 17, 1, 0, 0], ![5, 12, 0, 1, 0], ![10, 8, 0, 0, 1]] where
  M :=![![![-5293, -227, 1338, 152, -366], ![8784, 375, -2222, -252, 608], ![-7296, -315, 1843, 210, -504], ![1656, 68, -422, -47, 116], ![-8736, -379, 2206, 252, -603]]]
  hmulB := by decide  
  f := ![![![17, 7, -12, -4, 6]], ![![-144, -69, 46, 24, -16]], ![![-108, -54, 27, 18, -8]], ![![-113, -53, 34, 17, -10]], ![![-34, -21, 0, 8, 1]]]
  g := ![![![-971, -1151, 1338, 152, -366], ![1612, 1911, -2222, -252, 608], ![-1338, -1586, 1843, 210, -504], ![305, 362, -422, -47, 116], ![-1602, -1899, 2206, 252, -603]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P1 : CertificateIrreducibleZModOfList' 19 2 2 4 [10, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 18], [0, 1]]
 g := ![![[1, 16], [7, 4], [5], [1]], ![[12, 3], [5, 15], [5], [1]]]
 h' := ![![[9, 18], [6, 15], [12, 17], [9, 9], [0, 1]], ![[0, 1], [8, 4], [13, 2], [14, 10], [9, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [3, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N1 : CertifiedPrimeIdeal' SI19N1 19 where
  n := 2
  hpos := by decide
  P := [10, 10, 1]
  hirr := P19P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2799, -5614, -13322, 4814, 8141]
  a := ![13, -7, 4, 2, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2715, 5156, -13322, 4814, 8141]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N1 B_one_repr
lemma NI19N1 : Nat.card (O ⧸ I19N1) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N1

def I19N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 88, -64, -51, 42]] i)))

def SI19N2: IdealEqSpanCertificate' Table ![![149, 88, -64, -51, 42]] 
 ![![19, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![14, 0, 0, 1, 0], ![10, 0, 0, 0, 1]] where
  M :=![![![149, 88, -64, -51, 42], ![-1008, -479, 446, 208, -204], ![2448, 1049, -1095, -370, 416], ![-4488, -1742, 2028, 465, -638], ![5556, 2136, -2512, -551, 775]]]
  hmulB := by decide  
  f := ![![![-3505, -98, 928, 85, -264]], ![![149, 21, -26, -9, 4]], ![![-1875, -29, 515, 37, -152]], ![![-2426, -10, 688, 37, -210]], ![![-2026, 14, 592, 21, -187]]]
  g := ![![![49, 88, -64, -51, 42], ![-285, -479, 446, 208, -204], ![646, 1049, -1095, -370, 416], ![-1112, -1742, 2028, 465, -638], ![1368, 2136, -2512, -551, 775]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N2 : Nat.card (O ⧸ I19N2) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N2)

lemma isPrimeI19N2 : Ideal.IsPrime I19N2 := prime_ideal_of_norm_prime hp19.out _ NI19N2
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-107, -7, 28, 4, -8]] ![![-5293, -227, 1338, 152, -366]]
  ![![377087, 16148, -95344, -10824, 26082]] where
 M := ![![![377087, 16148, -95344, -10824, 26082]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI19N1 : IdealMulLeCertificate' Table 
  ![![377087, 16148, -95344, -10824, 26082]] ![![149, 88, -64, -51, 42]]
  ![![19, 0, 0, 0, 0]] where
 M := ![![![-3629, -532, 1064, 285, -380]]]
 hmul := by decide  
 g := ![![![![-191, -28, 56, 15, -20]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-47, -43, -28, 7, 10]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![-47, -43, -28, 7, 10]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![13, 0, 0, 1, 0], ![0, 21, 11, 0, 1]] where
  M :=![![![-47, -43, -28, 7, 10], ![-240, -171, -60, 24, 28], ![-336, -280, -139, 52, 48], ![-456, -364, -206, 41, 90], ![-588, -447, -152, 91, 51]]]
  hmulB := by decide  
  f := ![![![335, 13, -86, -9, 24]], ![![-576, -33, 140, 20, -36]], ![![432, 0, -125, -4, 40]], ![![181, 5, -48, -4, 14]], ![![-300, -32, 61, 17, -11]]]
  g := ![![![-6, -11, -6, 7, 10], ![-24, -33, -16, 24, 28], ![-44, -56, -29, 52, 48], ![-43, -98, -52, 41, 90], ![-77, -66, -31, 91, 51]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [7, 15, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 7, 14], [0, 15, 9], [0, 1]]
 g := ![![[4, 18, 12], [7, 13, 2], [10, 18, 1], []], ![[22, 17, 18, 17], [17, 21, 16, 21], [16, 7, 8, 22], [21, 12]], ![[0, 22, 4, 3], [11, 21, 18, 8], [18, 6, 9, 4], [3, 12]]]
 h' := ![![[18, 7, 14], [20, 12, 9], [22, 0, 18], [0, 0, 1], [0, 1]], ![[0, 15, 9], [12, 3, 4], [11, 22, 17], [16, 14, 15], [18, 7, 14]], ![[0, 1], [15, 8, 10], [12, 1, 11], [2, 9, 7], [0, 15, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 7], []]
 b := ![[], [17, 2, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [7, 15, 5, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![519152, 151672, -260093, 2098, 56299]
  a := ![-1, -1, -1, -4, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![21386, -44809, -38234, 2098, 56299]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 12167 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-335, -13, 86, 9, -24]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![-335, -13, 86, 9, -24]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![9, 0, 1, 0, 0], ![0, 5, 0, 1, 0], ![5, 12, 0, 0, 1]] where
  M :=![![![-335, -13, 86, 9, -24], ![576, 33, -140, -20, 36], ![-432, 0, 125, 4, -40], ![192, 54, -14, -25, -10], ![-444, 43, 162, -15, -63]]]
  hmulB := by decide  
  f := ![![![47, 43, 28, -7, -10]], ![![240, 171, 60, -24, -28]], ![![33, 29, 17, -5, -6]], ![![72, 53, 22, -7, -10]], ![![161, 118, 44, -18, -19]]]
  g := ![![![-43, 10, 86, 9, -24], ![72, -13, -140, -20, 36], ![-59, 20, 125, 4, -40], ![16, 13, -14, -25, -10], ![-69, 38, 162, -15, -63]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P1 : CertificateIrreducibleZModOfList' 23 2 2 4 [20, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 22], [0, 1]]
 g := ![![[17, 12], [9, 18], [17, 2], [1]], ![[8, 11], [7, 5], [4, 21], [1]]]
 h' := ![![[5, 22], [4, 9], [5, 8], [3, 5], [0, 1]], ![[0, 1], [3, 14], [22, 15], [5, 18], [5, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [2, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N1 : CertifiedPrimeIdeal' SI23N1 23 where
  n := 2
  hpos := by decide
  P := [20, 18, 1]
  hirr := P23P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-169, -940, -3506, 1022, 2459]
  a := ![3, 3, 0, -1, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![830, -1546, -3506, 1022, 2459]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N1 B_one_repr
lemma NI23N1 : Nat.card (O ⧸ I23N1) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![-47, -43, -28, 7, 10]] ![![-335, -13, 86, 9, -24]]
  ![![23, 0, 0, 0, 0]] where
 M := ![![![-23, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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


lemma PB934I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB934I0 : PrimesBelowBoundCertificateInterval O 1 23 934 where
  m := 9
  g := ![5, 5, 5, 2, 1, 2, 1, 3, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB934I0_primes
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
    · exact ![I17N0]
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
    · exact ![2401, 7]
    · exact ![161051]
    · exact ![2197, 169]
    · exact ![1419857]
    · exact ![361, 361, 19]
    · exact ![12167, 529]
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
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
      exact NI19N2
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I5N0, I7N1, I13N1, I19N0, I19N1, I19N2, I23N1]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N0, I3N1, I3N1, I3N1], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N1], [], [I13N1], [], [I19N0, I19N1, I19N2], [I23N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
