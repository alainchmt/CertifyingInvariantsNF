
import IdealArithmetic.Examples.NF5_3_1687500000_3.RI5_3_1687500000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-15, 10, 2, 6, -11]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![-15, 10, 2, 6, -11]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-15, 10, 2, 6, -11], ![32, 10, -37, -38, 76], ![-76, -157, 200, 78, -228], ![-658, 249, 357, 711, -1244], ![-276, 67, 183, 302, -546]]]
  hmulB := by decide  
  f := ![![![-144258, 161819, 53293, 82810, -185497]], ![![-115960, 130076, 42839, 66566, -149110]], ![![-186428, 209121, 68872, 107018, -239724]], ![![-91882, 103064, 33944, 52745, -118151]], ![![-163203, 183068, 60292, 93686, -209860]]]
  g := ![![![-2, 10, 2, 6, -11], ![-22, 10, -37, -38, 76], ![76, -157, 200, 78, -228], ![293, 249, 357, 711, -1244], ![135, 67, 183, 302, -546]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 0, -1, -1, 2]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![1, 0, -1, -1, 2]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![1, 0, -1, -1, 2], ![-2, -4, 5, 2, -6], ![-36, 13, 20, 38, -68], ![119, 66, -159, -129, 277], ![40, 30, -60, -44, 97]]]
  hmulB := by decide  
  f := ![![![631, -374, -104, -159, 345]], ![![111, -68, -19, -29, 63]], ![![42, -29, -8, -12, 26]], ![![268, -161, -44, -67, 145]], ![![-160, 92, 26, 40, -87]]]
  g := ![![![1, 0, -1, -1, 2], ![-2, -4, 5, 2, -6], ![-37, 13, 20, 38, -68], ![124, 66, -159, -129, 277], ![42, 30, -60, -44, 97]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-685300, 402243, 111544, 170525, -369779]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![-685300, 402243, 111544, 170525, -369779]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-685300, 402243, 111544, 170525, -369779], ![-233530, 137073, 38011, 58110, -126010], ![-79580, 46711, 12953, 19802, -42940], ![103207, -60578, -16799, -25682, 55691], ![352436, -206865, -57365, -87698, 190171]]]
  hmulB := by decide  
  f := ![![![-16, 5, 11, 16, -30]], ![![28, 31, -49, -31, 73]], ![![114, -182, 59, -125, 151]], ![![-1159, -140, 1123, 1247, -2458]], ![![-440, -95, 462, 474, -953]]]
  g := ![![![-684806, 402243, 111544, 170525, -369779], ![-233362, 137073, 38011, 58110, -126010], ![-79523, 46711, 12953, 19802, -42940], ![103133, -60578, -16799, -25682, 55691], ![352182, -206865, -57365, -87698, 190171]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![-15, 10, 2, 6, -11]] ![![1, 0, -1, -1, 2]]
  ![![167, 52, -189, -179, 369]] where
 M := ![![![167, 52, -189, -179, 369]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![167, 52, -189, -179, 369]] ![![1, 0, -1, -1, 2]]
  ![![326, -3409, 2634, -390, -916]] where
 M := ![![![326, -3409, 2634, -390, -916]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![326, -3409, 2634, -390, -916]] ![![-685300, 402243, 111544, 170525, -369779]]
  ![![144, -105, -3, -24, 50]] where
 M := ![![![144, -105, -3, -24, 50]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![144, -105, -3, -24, 50]] ![![-685300, 402243, 111544, 170525, -369779]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![-58778978, 34500816, 9567248, 14626112, -31716340]]]
 hmul := by decide  
 g := ![![![![-29389489, 17250408, 4783624, 7313056, -15858170]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5303, -5961, -1965, -3054, 6842]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![5303, -5961, -1965, -3054, 6842]] 
 ![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 1, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![5303, -5961, -1965, -3054, 6842], ![8572, -9612, -3169, -4926, 11036], ![13828, -15485, -5110, -7946, 17804], ![6888, -7683, -2545, -3963, 8884], ![6816, -7606, -2516, -3916, 8777]]]
  hmulB := by decide  
  f := ![![![13, 23, -31, -14, 38]], ![![172, -84, -77, -186, 316]], ![![-493, -190, 589, 528, -1106]], ![![28, 1129, -990, -17, 584]], ![![-105, 437, -283, 118, -13]]]
  g := ![![![142, -969, -1965, -3054, 6842], ![235, -1562, -3169, -4926, 11036], ![378, -2513, -5110, -7946, 17804], ![183, -1240, -2545, -3963, 8884], ![185, -1230, -2516, -3916, 8777]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P0 : CertificateIrreducibleZModOfList' 3 2 2 1 [2, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 2], [0, 1]]
 g := ![![[2, 1]], ![[1, 2]]]
 h' := ![![[2, 2], [0, 1]], ![[0, 1], [2, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [1, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 2
  hpos := by decide
  P := [2, 1, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![312203, -299667, -17243, -327675, 500563]
  a := ![-189, -11, 173, 177, -387]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-57039, 9336, -17243, -327675, 500563]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 9 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13, 8, 2, 4, -8]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![-13, 8, 2, 4, -8]] 
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![-13, 8, 2, 4, -8], ![8, 5, -12, -12, 24], ![-24, -52, 65, 24, -72], ![-220, 78, 124, 239, -420], ![-88, 18, 62, 100, -181]]]
  hmulB := by decide  
  f := ![![![-335, 296, 126, 212, -488]], ![![-397, 333, 150, 256, -592]], ![![-1026, 820, 389, 672, -1560]], ![![-1060, 782, 404, 711, -1660]], ![![-1058, 818, 402, 700, -1629]]]
  g := ![![![-3, 8, 2, 4, -8], ![-7, 5, -12, -12, 24], ![14, -52, 65, 24, -72], ![98, 78, 124, 239, -420], ![44, 18, 62, 100, -181]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![5303, -5961, -1965, -3054, 6842]] ![![-13, 8, 2, 4, -8]]
  ![![317, -257, -79, -122, 270]] where
 M := ![![![317, -257, -79, -122, 270]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N1 : IdealMulLeCertificate' Table 
  ![![317, -257, -79, -122, 270]] ![![-13, 8, 2, 4, -8]]
  ![![-1201, 703, 195, 298, -646]] where
 M := ![![![-1201, 703, 195, 298, -646]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![-1201, 703, 195, 298, -646]] ![![-13, 8, 2, 4, -8]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![7845, -4617, -1263, -1938, 4206]]]
 hmul := by decide  
 g := ![![![![2615, -1539, -421, -646, 1402]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N1, I3N1, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N1
    exact isPrimeI3N1
    exact isPrimeI3N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1 ⊙ MulI3N2)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-685, 493, 267, 474, -1110]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![-685, 493, 267, 474, -1110]] 
 ![![5, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![-685, 493, 267, 474, -1110], ![-2292, 1640, 877, 1554, -3636], ![-7452, 5329, 2846, 5042, -11796], ![-10932, 7817, 4173, 7393, -17296], ![-8488, 6068, 3238, 5736, -13419]]]
  hmulB := by decide  
  f := ![![![159, -181, -57, -90, 202]], ![![52, -56, -21, -30, 68]], ![![100, -97, -42, -66, 140]], ![![-12, -79, 59, 33, -72]], ![![86, -132, -10, -40, 89]]]
  g := ![![![307, 493, 267, 474, -1110], ![996, 1640, 877, 1554, -3636], ![3228, 5329, 2846, 5042, -11796], ![4732, 7817, 4173, 7393, -17296], ![3670, 6068, 3238, 5736, -13419]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![-685, 493, 267, 474, -1110]] ![![-685, 493, 267, 474, -1110]]
  ![![1589497, -1136564, -606830, -1075032, 2515056]] where
 M := ![![![1589497, -1136564, -606830, -1075032, 2515056]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![1589497, -1136564, -606830, -1075032, 2515056]] ![![-685, 493, 267, 474, -1110]]
  ![![-3557249101, 2543694655, 1358233683, 2406213902, -5629411278]] where
 M := ![![![-3557249101, 2543694655, 1358233683, 2406213902, -5629411278]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![-3557249101, 2543694655, 1358233683, 2406213902, -5629411278]] ![![-685, 493, 267, 474, -1110]]
  ![![7962722630209, -5693930838856, -3040335340832, -5386184063440, 12601142502352]] where
 M := ![![![7962722630209, -5693930838856, -3040335340832, -5386184063440, 12601142502352]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![7962722630209, -5693930838856, -3040335340832, -5386184063440, 12601142502352]] ![![-685, 493, 267, 474, -1110]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![-17824129937592845, 12745560530036925, 6805628542461875, 12056685827141050, -28206985586800550]]]
 hmul := by decide  
 g := ![![![![-3564825987518569, 2549112106007385, 1361125708492375, 2411337165428210, -5641397117360110]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-23, 13, 15, 18, -38]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![-23, 13, 15, 18, -38]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![3, 3, 6, 1, 0], ![0, 2, 3, 0, 1]] where
  M :=![![![-23, 13, 15, 18, -38], ![-4, 66, -43, -6, 28], ![308, -87, -176, -350, 604], ![-1308, -619, 1669, 1391, -2984], ![-472, -264, 642, 496, -1093]]]
  hmulB := by decide  
  f := ![![![3543, -2083, -583, -894, 1942]], ![![1292, -770, -231, -362, 796]], ![![716, -459, -184, -310, 708]], ![![2675, -1618, -519, -829, 1842]], ![![468, -301, -122, -206, 471]]]
  g := ![![![-11, 5, 3, 18, -38], ![2, 4, -13, -6, 28], ![194, -35, 16, -350, 604], ![-783, 168, 325, 1391, -2984], ![-280, 62, 135, 496, -1093]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 3 2 2 [2, 2, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 4, 3], [6, 2, 4], [0, 1]]
 g := ![![[1, 6, 2], [1]], ![[4, 2, 3, 5], [3, 4, 6, 6]], ![[3, 5, 0, 4], [6, 6, 2, 1]]]
 h' := ![![[5, 4, 3], [5, 5, 4], [0, 1]], ![[6, 2, 4], [0, 6, 2], [5, 4, 3]], ![[0, 1], [1, 3, 1], [6, 2, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 3], []]
 b := ![[], [5, 2, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 3
  hpos := by decide
  P := [2, 2, 3, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![29052725974, 26798194918, -48026635468, -31043077014, 72495203658]
  a := ![171, -54, -156, -226, 350]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![17454565288, -3580425908, -11321969194, -31043077014, 72495203658]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 343 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3543, 2083, 583, 894, -1942]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![-3543, 2083, 583, 894, -1942]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![3, 2, 1, 0, 0], ![4, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![-3543, 2083, 583, 894, -1942], ![-1292, 770, 231, 362, -796], ![-716, 459, 184, 310, -708], ![76, 13, 87, 175, -432], ![1456, -810, -160, -212, 419]]]
  hmulB := by decide  
  f := ![![![23, -13, -15, -18, 38]], ![![4, -66, 43, 6, -28]], ![![-33, -12, 31, 44, -78]], ![![200, 81, -247, -209, 448]], ![![74, 34, -96, -76, 167]]]
  g := ![![![-712, 131, 583, 894, -1942], ![-263, 44, 231, 362, -796], ![-156, 13, 184, 310, -708], ![-3, -23, 87, 175, -432], ![278, -70, -160, -212, 419]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P1 : CertificateIrreducibleZModOfList' 7 2 2 2 [6, 4, 1] where
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
 g := ![![[3, 2], [3, 1]], ![[2, 5], [6, 6]]]
 h' := ![![[3, 6], [3, 3], [0, 1]], ![[0, 1], [5, 4], [3, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [4, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N1 : CertifiedPrimeIdeal' SI7N1 7 where
  n := 2
  hpos := by decide
  P := [6, 4, 1]
  hirr := P7P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![60011, -12178, -42335, -61850, 117164]
  a := ![-62, -6, 57, 55, -127]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![28584, 10356, -42335, -61850, 117164]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N1 B_one_repr
lemma NI7N1 : Nat.card (O ⧸ I7N1) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![-23, 13, 15, 18, -38]] ![![-3543, 2083, 583, 894, -1942]]
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


def P11P0 : CertificateIrreducibleZModOfList' 11 5 2 3 [9, 4, 3, 8, 9, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 0, 2, 2, 3], [3, 2, 3, 1, 10], [5, 9, 6, 0, 1], [1, 10, 0, 8, 8], [0, 1]]
 g := ![![[2, 2, 5, 9, 4], [1], []], ![[1, 3, 7, 0, 0, 3], [6, 1, 7, 3, 1, 6, 1, 9], [2, 4, 8, 9]], ![[2, 3, 7, 9, 5, 4, 4, 7], [5, 1, 3, 5, 9, 7, 7, 7], [6, 9, 0, 1]], ![[9, 4, 7, 0, 0, 6, 0, 9], [5, 8, 4, 9, 10, 3, 5, 4], [4, 8, 2, 1]], ![[5, 5, 4, 2, 8, 4, 1, 6], [3, 10, 1, 2, 4, 4, 1, 2], [6, 9, 3, 9]]]
 h' := ![![[4, 0, 2, 2, 3], [2, 7, 8, 3, 2], [0, 0, 1], [0, 1]], ![[3, 2, 3, 1, 10], [6, 0, 5, 10], [9, 0, 10, 7, 6], [4, 0, 2, 2, 3]], ![[5, 9, 6, 0, 1], [2, 3, 2, 2, 9], [10, 6, 1, 0, 9], [3, 2, 3, 1, 10]], ![[1, 10, 0, 8, 8], [10, 7, 3, 3, 8], [0, 2, 2, 2, 2], [5, 9, 6, 0, 1]], ![[0, 1], [10, 5, 4, 4, 3], [2, 3, 8, 2, 5], [1, 10, 0, 8, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 2, 2, 3], [], [], []]
 b := ![[], [6, 2, 3, 2, 10], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 5
  hpos := by decide
  P := [9, 4, 3, 8, 9, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-217360554943238993, 163672445609659767, 48040587927087668, 235689674175623778, -372369780630722941]
  a := ![295, 33, -270, -263, 604]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-19760050449385363, 14879313237241797, 4367326175189788, 21426334015965798, -33851798239156631]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![722, -589, -271, -465, 1077]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![722, -589, -271, -465, 1077]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![4, 5, 0, 1, 0], ![9, 3, 12, 0, 1]] where
  M :=![![![722, -589, -271, -465, 1077], ![2010, -1556, -763, -1328, 3090], ![6024, -4499, -2294, -4026, 9392], ![8369, -6079, -3193, -5638, 13177], ![6536, -4768, -2494, -4400, 10281]]]
  hmulB := by decide  
  f := ![![![4, -9, 5, -1, -1]], ![![-62, 8, 47, 68, -126]], ![![336, 247, -502, -358, 808]], ![![23, -65, 36, -24, 15]], ![![322, 201, -450, -341, 754]]]
  g := ![![![-547, -115, -1015, -465, 1077], ![-1576, -322, -2911, -1328, 3090], ![-4800, -965, -8846, -4026, 9392], ![-6744, -1340, -12409, -5638, 13177], ![-5261, -1047, -9682, -4400, 10281]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [11, 1, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 3], [11, 9], [0, 1]]
 g := ![![[3, 9, 3], [4, 3], [1]], ![[9, 5, 1], [9, 9], [1]], ![[10, 12, 9], [11, 1], [1]]]
 h' := ![![[6, 3], [12, 11, 4], [2, 12, 4], [0, 1]], ![[11, 9], [1, 8, 10], [10, 11, 10], [6, 3]], ![[0, 1], [6, 7, 12], [7, 3, 12], [11, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4], []]
 b := ![[], [8, 1, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [11, 1, 9, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![32492900042, 8234126369, -35150068450, -34867756234, 70911184100]
  a := ![-421, -19, 386, 404, -862]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-35864363994, -2320049597, -68160329050, -34867756234, 70911184100]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 2197 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 12, -16, -8, 20]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![7, 12, -16, -8, 20]] 
 ![![13, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![8, 0, 0, 0, 1]] where
  M :=![![![7, 12, -16, -8, 20], ![64, -45, -16, -72, 112], ![-784, -208, 859, 832, -1712], ![320, 1748, -1768, -337, 1480], ![-32, 672, -544, 32, 251]]]
  hmulB := by decide  
  f := ![![![-391477, 439220, 144656, 224776, -503508]], ![![-229110, 257043, 84656, 131544, -294664]], ![![-168203, 188700, 62147, 96568, -216316]], ![![-68489, 76832, 25304, 39319, -88076]], ![![-278952, 312960, 103072, 160160, -358765]]]
  g := ![![![-13, 12, -16, -8, 20], ![-34, -45, -16, -72, 112], ![827, -208, 859, 832, -1712], ![-1259, 1748, -1768, -337, 1480], ![-344, 672, -544, 32, 251]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1

def I13N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2508, -2799, -921, -1431, 3205]] i)))

def SI13N2: IdealEqSpanCertificate' Table ![![2508, -2799, -921, -1431, 3205]] 
 ![![13, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![2508, -2799, -921, -1431, 3205], ![3998, -4480, -1475, -2292, 5134], ![6416, -7195, -2370, -3682, 8248], ![3159, -3543, -1169, -1816, 4067], ![3120, -3506, -1156, -1796, 4023]]]
  hmulB := by decide  
  f := ![![![-3442, 2461, 1315, 2329, -5449]], ![![-2712, 1939, 1036, 1835, -4293]], ![![-3574, 2558, 1363, 2417, -5655]], ![![-7253, 5183, 2773, 4906, -11481]], ![![-3426, 2449, 1309, 2317, -5422]]]
  g := ![![![2987, -2799, -921, -1431, 3205], ![4781, -4480, -1475, -2292, 5134], ![7679, -7195, -2370, -3682, 8248], ![3784, -3543, -1169, -1816, 4067], ![3743, -3506, -1156, -1796, 4023]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N2 : Nat.card (O ⧸ I13N2) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N2)

lemma isPrimeI13N2 : Ideal.IsPrime I13N2 := prime_ideal_of_norm_prime hp13.out _ NI13N2
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![722, -589, -271, -465, 1077]] ![![7, 12, -16, -8, 20]]
  ![![-3442, 2461, 1315, 2329, -5449]] where
 M := ![![![-3442, 2461, 1315, 2329, -5449]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI13N1 : IdealMulLeCertificate' Table 
  ![![-3442, 2461, 1315, 2329, -5449]] ![![2508, -2799, -921, -1431, 3205]]
  ![![13, 0, 0, 0, 0]] where
 M := ![![![13, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N1, I13N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
    exact isPrimeI13N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0 ⊙ MulI13N1)
instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-37157, 41704, 13736, 21344, -47812]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![-37157, 41704, 13736, 21344, -47812]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![3, 1, 6, 1, 0], ![7, 5, 11, 0, 1]] where
  M :=![![![-37157, 41704, 13736, 21344, -47812], ![-59792, 67079, 22092, 34328, -76896], ![-96144, 107852, 35519, 55192, -123632], ![-47392, 53156, 17508, 27203, -60936], ![-46992, 52700, 17356, 26968, -60409]]]
  hmulB := by decide  
  f := ![![![-189, 136, 72, 128, -300]], ![![-624, 439, 244, 424, -992]], ![![-2032, 1460, 767, 1384, -3216]], ![![-951, 691, 354, 643, -1500]], ![![-1707, 1227, 645, 1160, -2701]]]
  g := ![![![13735, 15260, 24212, 21344, -47812], ![22088, 24543, 38940, 34328, -76896], ![35512, 39460, 62607, 55192, -123632], ![17503, 19449, 30858, 27203, -60936], ![17351, 19281, 30591, 26968, -60409]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [12, 12, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 5, 16], [8, 11, 1], [0, 1]]
 g := ![![[10, 13, 4], [14, 9], [7, 1], []], ![[2, 10, 8, 1], [15, 15], [16, 2], [14, 1]], ![[7, 9, 16, 4], [15, 16], [1, 8], [12, 1]]]
 h' := ![![[16, 5, 16], [3, 8, 15], [1, 6, 3], [0, 0, 1], [0, 1]], ![[8, 11, 1], [6, 12, 4], [4, 4, 10], [3, 14, 11], [16, 5, 16]], ![[0, 1], [6, 14, 15], [13, 7, 4], [5, 3, 5], [8, 11, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 4], []]
 b := ![[], [0, 15, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [12, 12, 10, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5456653708, 4159680120, 1162762216, 5916683760, -9324090760]
  a := ![210, 0, -192, -220, 430]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2474231196, 2639026480, 4013391648, 5916683760, -9324090760]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 4913 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11260, 6623, 1853, 2841, -6171]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![-11260, 6623, 1853, 2841, -6171]] 
 ![![17, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-11260, 6623, 1853, 2841, -6171], ![-4098, 2446, 731, 1144, -2514], ![-2232, 1435, 568, 954, -2176], ![323, -13, 245, 500, -1241], ![4688, -2614, -532, -716, 1431]]]
  hmulB := by decide  
  f := ![![![230, -105, -107, -251, 427]], ![![4, -103, 86, -7, -39]], ![![40, 517, -476, -38, 324]], ![![2777, -318, -2130, -2991, 5584]], ![![1118, -21, -949, -1203, 2298]]]
  g := ![![![-4743, 6623, 1853, 2841, -6171], ![-1762, 2446, 731, 1144, -2514], ![-1065, 1435, 568, 954, -2176], ![-47, -13, 245, 500, -1241], ![1827, -2614, -532, -716, 1431]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1

def I17N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4125, -4526, -1536, -2412, 5424]] i)))

def SI17N2: IdealEqSpanCertificate' Table ![![4125, -4526, -1536, -2412, 5424]] 
 ![![17, 0, 0, 0, 0], ![13, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![10, 0, 0, 0, 1]] where
  M :=![![![4125, -4526, -1536, -2412, 5424], ![7176, -7659, -2666, -4224, 9528], ![13152, -13466, -4899, -7876, 17856], ![9576, -8848, -3594, -5971, 13688], ![8504, -8062, -3182, -5244, 11989]]]
  hmulB := by decide  
  f := ![![![693, 566, -1084, -740, 1696]], ![![697, 223, -794, -748, 1544]], ![![-2667, -376, 2629, 2864, -5680]], ![![3340, 6028, -8046, -3523, 9704]], ![![1162, 2638, -3262, -1220, 3629]]]
  g := ![![![1171, -4526, -1536, -2412, 5424], ![1825, -7659, -2666, -4224, 9528], ![2709, -13466, -4899, -7876, 17856], ![894, -8848, -3594, -5971, 13688], ![1034, -8062, -3182, -5244, 11989]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N2 : Nat.card (O ⧸ I17N2) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N2)

lemma isPrimeI17N2 : Ideal.IsPrime I17N2 := prime_ideal_of_norm_prime hp17.out _ NI17N2
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![-37157, 41704, 13736, 21344, -47812]] ![![-11260, 6623, 1853, 2841, -6171]]
  ![![-422468, 331429, 101015, 155875, -344421]] where
 M := ![![![-422468, 331429, 101015, 155875, -344421]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI17N1 : IdealMulLeCertificate' Table 
  ![![-422468, 331429, 101015, 155875, -344421]] ![![4125, -4526, -1536, -2412, 5424]]
  ![![17, 0, 0, 0, 0]] where
 M := ![![![527906100, -589052431, -193818479, -301143321, 674466551]]]
 hmul := by decide  
 g := ![![![![31053300, -34650143, -11401087, -17714313, 39674503]]]]
 hle2 := by decide  


def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N1, I17N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N1
    exact isPrimeI17N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 17 (by decide) (𝕀 ⊙ MulI17N0 ⊙ MulI17N1)
instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1359, -342, 1490, 1548, -3100]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-1359, -342, 1490, 1548, -3100]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![16, 0, 10, 16, 1]] where
  M :=![![![-1359, -342, 1490, 1548, -3100], ![3016, 6327, -8014, -3140, 9128], ![50680, -20406, -26389, -54732, 95080], ![-200080, -93290, 252898, 214101, -456440], ![-71072, -41724, 97168, 75912, -166075]]]
  hmulB := by decide  
  f := ![![![-2678973, 3005130, 989690, 1537836, -3444796]], ![![-4306808, 4831185, 1591058, 2472268, -5537944]], ![![-6923624, 7766730, 2557781, 3974388, -8902712]], ![![-3411568, 3827230, 1260322, 1958295, -4386584]], ![![-8950880, 10040992, 3306702, 5138064, -11509347]]]
  g := ![![![2539, -18, 1710, 2692, -3100], ![-7528, 333, -5226, -7852, 9128], ![-77400, -1074, -51431, -82948, 95080], ![373840, -4910, 253542, 395639, -456440], ![136112, -2196, 92522, 143848, -166075]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 4 2 4 [13, 11, 17, 0, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 6, 11, 3], [6, 9, 10, 10], [4, 3, 17, 6], [0, 1]]
 g := ![![[11, 11, 4, 1], [13, 4], [1], []], ![[0, 7, 11, 3, 13, 10], [1, 7, 3, 4, 2, 13], [6, 7, 5], [4, 9, 9]], ![[6, 2, 7, 15, 9, 8], [0, 11, 5, 9, 2, 2], [8, 4, 1], [5, 10, 5]], ![[18, 4, 6, 18, 4, 6], [6, 4, 8, 0, 14, 4], [5, 13, 5], [17, 14, 17]]]
 h' := ![![[9, 6, 11, 3], [2, 12, 2, 1], [6, 8, 2], [0, 0, 1], [0, 1]], ![[6, 9, 10, 10], [11, 12, 13, 4], [3, 18, 7, 6], [10, 4, 7, 10], [9, 6, 11, 3]], ![[4, 3, 17, 6], [1, 4, 14, 15], [15, 13, 0, 2], [9, 18, 17, 18], [6, 9, 10, 10]], ![[0, 1], [7, 10, 9, 18], [8, 18, 10, 11], [4, 16, 13, 10], [4, 3, 17, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [9, 3], []]
 b := ![[], [], [6, 7, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 4
  hpos := by decide
  P := [13, 11, 17, 0, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2823536312, -527588010931, 448745216053, -8784245161, -240199414780]
  a := ![-29, 11, 29, 41, -60]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![202421798568, -27767790049, 150038913887, 201810862701, -240199414780]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 130321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2678973, -3005130, -989690, -1537836, 3444796]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![2678973, -3005130, -989690, -1537836, 3444796]] 
 ![![19, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![14, 0, 1, 0, 0], ![18, 0, 0, 1, 0], ![14, 0, 0, 0, 1]] where
  M :=![![![2678973, -3005130, -989690, -1537836, 3444796], ![4306808, -4831185, -1591058, -2472268, 5537944], ![6923624, -7766730, -2557781, -3974388, 8902712], ![3411568, -3827230, -1260322, -1958295, 4386584], ![3381824, -3793788, -1249336, -1941240, 4348393]]]
  hmulB := by decide  
  f := ![![![1359, 342, -1490, -1548, 3100]], ![![485, -171, -284, -568, 988]], ![![-1666, 1326, 291, 1740, -2720]], ![![11818, 5234, -14722, -12735, 26960]], ![![4742, 2448, -6212, -5136, 11025]]]
  g := ![![![1212353, -3005130, -989690, -1537836, 3444796], ![1949047, -4831185, -1591058, -2472268, 5537944], ![3133376, -7766730, -2557781, -3974388, 8902712], ![1544120, -3827230, -1260322, -1958295, 4386584], ![1530602, -3793788, -1249336, -1941240, 4348393]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-1359, -342, 1490, 1548, -3100]] ![![2678973, -3005130, -989690, -1537836, 3444796]]
  ![![19, 0, 0, 0, 0]] where
 M := ![![![-19, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1603, 1146, 612, 1084, -2536]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![-1603, 1146, 612, 1084, -2536]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![5, 13, 1, 0, 0], ![2, 22, 0, 1, 0], ![0, 19, 0, 0, 1]] where
  M :=![![![-1603, 1146, 612, 1084, -2536], ![-5192, 3713, 1982, 3512, -8216], ![-16816, 12030, 6417, 11372, -26608], ![-24672, 17620, 9438, 16693, -39056], ![-19128, 13670, 7310, 12940, -30275]]]
  hmulB := by decide  
  f := ![![![-3085, 3410, 1120, 1740, -3896]], ![![-4840, 5411, 1782, 2768, -6200]], ![![-3743, 4177, 1375, 2136, -4784]], ![![-5062, 5658, 1862, 2893, -6480]], ![![-4160, 4653, 1532, 2380, -5331]]]
  g := ![![![-297, 762, 612, 1084, -2536], ![-962, 2469, 1982, 3512, -8216], ![-3115, 7999, 6417, 11372, -26608], ![-4576, 11728, 9438, 16693, -39056], ![-3546, 9095, 7310, 12940, -30275]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [14, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 22], [0, 1]]
 g := ![![[15, 1], [22, 12], [11, 9], [1]], ![[12, 22], [9, 11], [7, 14], [1]]]
 h' := ![![[20, 22], [14, 22], [7, 14], [9, 20], [0, 1]], ![[0, 1], [17, 1], [11, 9], [18, 3], [20, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [3, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [14, 3, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-62459, -116398, 153640, 65819, -183183]
  a := ![83, -1, -76, -85, 170]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-41839, -3533, 153640, 65819, -183183]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17, -6, 20, 18, -38]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![-17, -6, 20, 18, -38]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![16, 11, 1, 0, 0], ![4, 17, 0, 1, 0], ![15, 14, 0, 0, 1]] where
  M :=![![![-17, -6, 20, 18, -38], ![-4, 77, -62, 4, 28], ![728, -86, -555, -788, 1464], ![-1906, -1472, 2910, 2027, -4618], ![-632, -610, 1070, 668, -1587]]]
  hmulB := by decide  
  f := ![![![6237, -6790, -2224, -3454, 7730]], ![![9532, -10625, -3494, -5428, 12156]], ![![9556, -10543, -3461, -5376, 12036]], ![![8450, -9395, -3088, -4797, 10742]], ![![10181, -11250, -3694, -5738, 12847]]]
  g := ![![![7, 0, 20, 18, -38], ![24, 13, -62, 4, 28], ![-400, -47, -555, -788, 1464], ![552, -143, 2910, 2027, -4618], ![147, -66, 1070, 668, -1587]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P1 : CertificateIrreducibleZModOfList' 23 2 2 4 [15, 18, 1] where
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
 g := ![![[15, 12], [19, 1], [21, 2], [1]], ![[6, 11], [1, 22], [8, 21], [1]]]
 h' := ![![[5, 22], [14, 14], [7, 1], [8, 5], [0, 1]], ![[0, 1], [15, 9], [12, 22], [10, 18], [5, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [13, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N1 : CertifiedPrimeIdeal' SI23N1 23 where
  n := 2
  hpos := by decide
  P := [15, 18, 1]
  hirr := P23P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![48598, -563010, 437704, -52308, -164468]
  a := ![213, 9, -193, -208, 436]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-186018, -95042, 437704, -52308, -164468]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N1 B_one_repr
lemma NI23N1 : Nat.card (O ⧸ I23N1) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N1

def I23N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-44, -26, 60, 47, -103]] i)))

def SI23N2: IdealEqSpanCertificate' Table ![![-44, -26, 60, 47, -103]] 
 ![![23, 0, 0, 0, 0], ![22, 1, 0, 0, 0], ![22, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![-44, -26, 60, 47, -103], ![-86, 213, -108, 94, -78], ![2388, 72, -2127, -2572, 4964], ![-4329, -5030, 8050, 4590, -11277], ![-1288, -2018, 2842, 1356, -3597]]]
  hmulB := by decide  
  f := ![![![-23909502, 14033868, 3891660, 5949449, -12901223]], ![![-23224202, 13631625, 3780116, 5778924, -12531444]], ![![-22990672, 13494552, 3742105, 5720814, -12405434]], ![![156555, -91892, -25482, -38956, 84475]], ![![-2584014, 1516706, 420590, 642985, -1394296]]]
  g := ![![![-21, -26, 60, 47, -103], ![-94, 213, -108, 94, -78], ![1422, 72, -2127, -2572, 4964], ![-1606, -5030, 8050, 4590, -11277], ![-375, -2018, 2842, 1356, -3597]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N2 : Nat.card (O ⧸ I23N2) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N2)

lemma isPrimeI23N2 : Ideal.IsPrime I23N2 := prime_ideal_of_norm_prime hp23.out _ NI23N2
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![-1603, 1146, 612, 1084, -2536]] ![![-17, -6, 20, 18, -38]]
  ![![4851, -3460, -1852, -3306, 7690]] where
 M := ![![![4851, -3460, -1852, -3306, 7690]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI23N1 : IdealMulLeCertificate' Table 
  ![![4851, -3460, -1852, -3306, 7690]] ![![-44, -26, 60, 47, -103]]
  ![![23, 0, 0, 0, 0]] where
 M := ![![![68494, 114310, -154376, -80799, 197731]]]
 hmul := by decide  
 g := ![![![![2978, 4970, -6712, -3513, 8597]]]]
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


lemma PB2009I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB2009I0 : PrimesBelowBoundCertificateInterval O 1 23 2009 where
  m := 9
  g := ![5, 4, 5, 2, 1, 3, 3, 2, 3]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB2009I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N1, I3N1, I3N1]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1]
    · exact ![I11N0]
    · exact ![I13N0, I13N1, I13N2]
    · exact ![I17N0, I17N1, I17N2]
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
    · exact ![9, 3, 3, 3]
    · exact ![5, 5, 5, 5, 5]
    · exact ![343, 49]
    · exact ![161051]
    · exact ![2197, 13, 13]
    · exact ![4913, 17, 17]
    · exact ![130321, 19]
    · exact ![529, 529, 23]
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
      exact NI13N2
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
      exact NI17N2
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
      exact NI23N2
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I5N0, I7N0, I7N1, I13N1, I13N2, I17N1, I17N2, I19N1, I23N0, I23N1, I23N2]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N1, I3N1, I3N1], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N0, I7N1], [], [I13N1, I13N2], [I17N1, I17N2], [I19N1], [I23N0, I23N1, I23N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
