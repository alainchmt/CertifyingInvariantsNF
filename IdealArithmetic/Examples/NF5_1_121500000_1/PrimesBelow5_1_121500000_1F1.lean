
import IdealArithmetic.Examples.NF5_1_121500000_1.RI5_1_121500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-126015, 56573, -1787, -15396, -27214]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![-126015, 56573, -1787, -15396, -27214]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![22, 21, 24, 1, 0], ![16, 13, 22, 0, 1]] where
  M :=![![![-126015, 56573, -1787, -15396, -27214], ![-163284, 47300, 13963, 4666, -10734], ![-64404, -69517, 41232, 63392, 60198], ![262236, -214233, 20055, 73789, 105246], ![12076, 47379, -25093, -39740, -39701]]]
  hmulB := by decide  
  f := ![![![-260971, 314061, -56687, 49778, 139982]], ![![839892, -1247754, 503821, -244004, -121278]], ![![-727668, 1948655, -1613036, 518186, -1100190]], ![![-320282, 1070259, -998218, 303239, -779528]], ![![-143400, 878711, -988704, 277038, -904019]]]
  g := ![![![22349, 25299, 33325, -15396, -27214], ![-3248, 3064, 4763, 4666, -10734], ![-83524, -75287, -96708, 63392, 60198], ![-105002, -108000, -140217, 73789, 105246], ![52468, 48208, 62141, -39740, -39701]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [9, 24, 15, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 25, 23], [4, 3, 6], [0, 1]]
 g := ![![[15, 7, 20], [21, 23], [7, 13, 22], [1]], ![[21, 2, 5, 25], [10, 6], [4, 6, 21, 6], [23, 19, 24, 16]], ![[6, 13], [18, 1], [4, 4, 28, 25], [1, 0, 13, 13]]]
 h' := ![![[10, 25, 23], [10, 24, 7], [24, 28, 20], [20, 5, 14], [0, 1]], ![[4, 3, 6], [17, 11, 22], [7, 28, 8], [10, 20, 12], [10, 25, 23]], ![[0, 1], [12, 23], [0, 2, 1], [26, 4, 3], [4, 3, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26, 2], []]
 b := ![[], [26, 1, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 3
  hpos := by decide
  P := [9, 24, 15, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4996763, -6540262, 1969131, -1182440, -1539279]
  a := ![0, -8, -10, -22, -37]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1918583, 1320745, 2214201, -1182440, -1539279]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 24389 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2313, -603, 202, 412, 523]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![2313, -603, 202, 412, 523]] 
 ![![29, 0, 0, 0, 0], ![18, 1, 0, 0, 0], ![24, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![12, 0, 0, 0, 1]] where
  M :=![![![2313, -603, 202, 412, 523], ![3138, -734, 332, 594, 903], ![5418, -2257, 763, 640, 855], ![996, 785, -547, 571, 186], ![-1738, 59, 348, -450, 92]]]
  hmulB := by decide  
  f := ![![![133249, -96063, 7958, 31884, 46969]], ![![92424, -64994, 4346, 20398, 30891]], ![![120702, -81933, 3563, 23548, 37305]], ![![22607, -12740, -1201, 1677, 4301]], ![![49522, -38581, 5022, 14870, 20424]]]
  g := ![![![-29, -603, 202, 412, 523], ![-228, -734, 332, 594, 903], ![448, -2257, 763, 640, 855], ![-215, 785, -547, 571, 186], ![-314, 59, 348, -450, 92]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1

def I29N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![273889, -74113, 27146, 47814, 64885]] i)))

def SI29N2: IdealEqSpanCertificate' Table ![![273889, -74113, 27146, 47814, 64885]] 
 ![![29, 0, 0, 0, 0], ![21, 1, 0, 0, 0], ![23, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![273889, -74113, 27146, 47814, 64885], ![389310, -105346, 38586, 67964, 92229], ![553374, -149743, 54847, 96606, 131097], ![198636, -53753, 19687, 34677, 47058], ![-209374, 56657, -20752, -36552, -49602]]]
  hmulB := by decide  
  f := ![![![-255, 267, 6, 34, 211]], ![![-141, 135, 22, 14, 138]], ![![-291, 366, -79, 60, 148]], ![![-159, 110, 77, 1, 201]], ![![139, -144, 0, -18, -103]]]
  g := ![![![15557, -74113, 27146, 47814, 64885], ![22113, -105346, 38586, 67964, 92229], ![31433, -149743, 54847, 96606, 131097], ![11285, -53753, 19687, 34677, 47058], ![-11893, 56657, -20752, -36552, -49602]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N2 : Nat.card (O ⧸ I29N2) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N2)

lemma isPrimeI29N2 : Ideal.IsPrime I29N2 := prime_ideal_of_norm_prime hp29.out _ NI29N2
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![-126015, 56573, -1787, -15396, -27214]] ![![2313, -603, 202, 412, 523]]
  ![![-91665071, 24804236, -9085135, -16002314, -21715655]] where
 M := ![![![-91665071, 24804236, -9085135, -16002314, -21715655]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI29N1 : IdealMulLeCertificate' Table 
  ![![-91665071, 24804236, -9085135, -16002314, -21715655]] ![![273889, -74113, 27146, 47814, 64885]]
  ![![29, 0, 0, 0, 0]] where
 M := ![![![-19108937103183, 5170810250779, -1893930449573, -3335918782118, -4526949165788]]]
 hmul := by decide  
 g := ![![![![-658928865627, 178303801751, -65307946537, -115031682142, -156101695372]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N1, I29N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N1
    exact isPrimeI29N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0 ⊙ MulI29N1)
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-32961, 9452, -3408, -6042, -8126]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![-32961, 9452, -3408, -6042, -8126]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![12, 19, 1, 0, 0], ![10, 12, 0, 1, 0], ![0, 27, 0, 0, 1]] where
  M :=![![![-32961, 9452, -3408, -6042, -8126], ![-48756, 14471, -4716, -8690, -11874], ![-71244, 20956, -6093, -11754, -16518], ![-25176, 6032, -1300, -2861, -4548], ![28040, -8504, 2222, 4490, 6419]]]
  hmulB := by decide  
  f := ![![![-3103, 11116, -10684, 3202, -8590]], ![![-51540, 49545, 5728, 5418, 44982]], ![![-24084, 23209, 2599, 2552, 20940]], ![![-30034, 38492, -9708, 6559, 12848]], ![![-43316, 36669, 11554, 2796, 44709]]]
  g := ![![![2205, 11810, -3408, -6042, -8126], ![3056, 17063, -4716, -8690, -11874], ![3852, 23347, -6093, -11754, -16518], ![614, 6060, -1300, -2861, -4548], ![-1404, -8965, 2222, 4490, 6419]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [13, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 30], [0, 1]]
 g := ![![[4, 25], [10, 14], [29, 5], [10, 1]], ![[6, 6], [26, 17], [17, 26], [20, 30]]]
 h' := ![![[10, 30], [25, 5], [26, 13], [25, 25], [0, 1]], ![[0, 1], [13, 26], [1, 18], [27, 6], [10, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [17, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [13, 21, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11375, -11879, 2506, -2778, -3249]
  a := ![1, -9, -9, -23, -33]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![293, 1986, 2506, -2778, -3249]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-53493, 623503, -422603, -626410, -621832]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![-53493, 623503, -422603, -626410, -621832]] 
 ![![31, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![29, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![-53493, 623503, -422603, -626410, -621832], ![-3730992, 3250318, -624739, -1480772, -1892964], ![-11357784, 7414245, -123418, -1905866, -3205740], ![-7751724, 2901397, 1463689, 963909, 37494], ![6428152, -4159223, 43315, 1039838, 1776199]]]
  hmulB := by decide  
  f := ![![![-389195, 93181, -37457, -72708, -103016]], ![![-120376, 31200, -12329, -21570, -30688]], ![![-388705, 90484, -34797, -73556, -100900]], ![![-53840, 9345, -6879, -11513, -21062]], ![![-23642, 13371, -3087, -1392, 431]]]
  g := ![![![353654, 623503, -422603, -626410, -621832], ![-61519, 3250318, -624739, -1480772, -1892964], ![-1711538, 7414245, -123418, -1905866, -3205740], ![-2494855, 2901397, 1463689, 963909, 37494], ![991421, -4159223, 43315, 1039838, 1776199]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1

def I31N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, -308, 46, 126, 156]] i)))

def SI31N2: IdealEqSpanCertificate' Table ![![137, -308, 46, 126, 156]] 
 ![![31, 0, 0, 0, 0], ![13, 1, 0, 0, 0], ![17, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![28, 0, 0, 0, 1]] where
  M :=![![![137, -308, 46, 126, 156], ![936, -783, -26, 158, 288], ![1728, -948, -337, -154, 84], ![-216, 716, -496, -731, -732], ![-1068, 544, 184, 78, -61]]]
  hmulB := by decide  
  f := ![![![1703, -3908, 2890, -982, 1668]], ![![1037, -1899, 1108, -428, 348]], ![![-1175, 520, 957, -92, 1872]], ![![3095, -5248, 2738, -1129, 456]], ![![560, -1192, 824, -290, 419]]]
  g := ![![![-61, -308, 46, 126, 156], ![77, -783, -26, 158, 288], ![597, -948, -337, -154, 84], ![791, 716, -496, -731, -732], ![-326, 544, 184, 78, -61]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N2 : Nat.card (O ⧸ I31N2) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N2)

lemma isPrimeI31N2 : Ideal.IsPrime I31N2 := prime_ideal_of_norm_prime hp31.out _ NI31N2

def I31N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-69, 26, -7, -14, -19]] i)))

def SI31N3: IdealEqSpanCertificate' Table ![![-69, 26, -7, -14, -19]] 
 ![![31, 0, 0, 0, 0], ![22, 1, 0, 0, 0], ![12, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![27, 0, 0, 0, 1]] where
  M :=![![![-69, 26, -7, -14, -19], ![-114, 43, -7, -18, -27], ![-162, 50, -2, -14, -27], ![-24, -16, 8, 13, 12], ![70, -22, -1, 4, 10]]]
  hmulB := by decide  
  f := ![![![49, -54, 3, -8, -35]], ![![28, -29, -1, -4, -23]], ![![30, -42, 14, -8, -9]], ![![36, -32, -8, -3, -36]], ![![11, -12, 0, -2, -9]]]
  g := ![![![4, 26, -7, -14, -19], ![-1, 43, -7, -18, -27], ![-11, 50, -2, -14, -27], ![-8, -16, 8, 13, 12], ![8, -22, -1, 4, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N3 : Nat.card (O ⧸ I31N3) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N3)

lemma isPrimeI31N3 : Ideal.IsPrime I31N3 := prime_ideal_of_norm_prime hp31.out _ NI31N3
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![-32961, 9452, -3408, -6042, -8126]] ![![-53493, 623503, -422603, -626410, -621832]]
  ![![-194072483, 1170581817, -750593629, -1127627372, -1130861078]] where
 M := ![![![-194072483, 1170581817, -750593629, -1127627372, -1130861078]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI31N1 : IdealMulLeCertificate' Table 
  ![![-194072483, 1170581817, -750593629, -1127627372, -1130861078]] ![![137, -308, 46, 126, 156]]
  ![![1223378003285, -1567798102439, 564812329673, 1012178657942, 1138208153174]] where
 M := ![![![1223378003285, -1567798102439, 564812329673, 1012178657942, 1138208153174]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI31N2 : IdealMulLeCertificate' Table 
  ![![1223378003285, -1567798102439, 564812329673, 1012178657942, 1138208153174]] ![![-69, 26, -7, -14, -19]]
  ![![31, 0, 0, 0, 0]] where
 M := ![![![58198586975927, -48602311732717, 8240537145094, 20896856348432, 27364659229311]]]
 hmul := by decide  
 g := ![![![![1877373773417, -1567816507507, 265823778874, 674092140272, 882730942881]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N1, I31N2, I31N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
    exact isPrimeI31N2
    exact isPrimeI31N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0 ⊙ MulI31N1 ⊙ MulI31N2)
instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![949657, -1228407, 322302, -211392, -390531]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![949657, -1228407, 322302, -211392, -390531]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![34, 36, 1, 0, 0], ![17, 17, 0, 1, 0], ![19, 16, 0, 0, 1]] where
  M :=![![![949657, -1228407, 322302, -211392, -390531], ![-2343186, 3794284, -1830330, 791490, -96759], ![-580554, -2704713, 4489015, -1092672, 5039217], ![16289244, -18126507, 1536081, -2584955, -10788462], ![-18445794, 24008259, -6461142, 4158378, 7379764]]]
  hmulB := by decide  
  f := ![![![-424631, -34347, 219570, 256464, 202071]], ![![1212426, -1363094, 424188, 804390, 932571]], ![![940684, -1468275, 624595, 1056060, 1147881]], ![![510059, -716008, 281103, 488437, 539700]], ![![219901, -544598, 290838, 458610, 476341]]]
  g := ![![![27166, -80787, 322302, -211392, -390531], ![1304625, 1561594, -1830330, 791490, -96759], ![-6226399, -6117873, 4489015, -1092672, 5039217], ![5756419, 3868492, 1536081, -2584955, -10788462], ![-261484, 1833533, -6461142, 4158378, 7379764]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [23, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [36, 36], [0, 1]]
 g := ![![[29, 7], [1], [3, 27], [1], [1]], ![[22, 30], [1], [13, 10], [1], [1]]]
 h' := ![![[36, 36], [2, 9], [5, 1], [25, 8], [14, 36], [0, 1]], ![[0, 1], [30, 28], [4, 36], [17, 29], [15, 1], [36, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22]]
 b := ![[], [24, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [23, 1, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![319617, -332496, 67643, -62732, -97297]
  a := ![1, 44, 49, 114, 175]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![25266, -3904, 67643, -62732, -97297]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-37, 6, -2, -8, -10]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-37, 6, -2, -8, -10]] 
 ![![37, 0, 0, 0, 0], ![21, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![32, 0, 0, 1, 0], ![16, 0, 0, 0, 1]] where
  M :=![![![-37, 6, -2, -8, -10], ![-60, 23, -12, -8, -18], ![-108, 46, -3, -12, 6], ![48, -94, 26, -23, -36], ![-32, 86, -36, 24, 15]]]
  hmulB := by decide  
  f := ![![![-1185, 858, -74, -288, -422]], ![![-741, 525, -38, -168, -252]], ![![-171, 88, 15, -4, -24]], ![![-960, 670, -42, -207, -316]], ![![-472, 362, -44, -136, -189]]]
  g := ![![![7, 6, -2, -8, -10], ![1, 23, -12, -8, -18], ![-21, 46, -3, -12, 6], ![88, -94, 26, -23, -36], ![-74, 86, -36, 24, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1287, -1640, 459, -276, -463]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![1287, -1640, 459, -276, -463]] 
 ![![37, 0, 0, 0, 0], ![24, 1, 0, 0, 0], ![16, 0, 1, 0, 0], ![18, 0, 0, 1, 0], ![11, 0, 0, 0, 1]] where
  M :=![![![1287, -1640, 459, -276, -463], ![-2778, 4711, -2379, 1016, -267], ![-1602, -2272, 5460, -1176, 6897], ![22080, -25154, 2914, -3709, -13740], ![-24050, 31748, -9071, 5578, 8926]]]
  hmulB := by decide  
  f := ![![![252271, -245584, 60751, 127202, 154603]], ![![188706, -176649, 40385, 87750, 108375]], ![![157642, -131552, 22252, 56502, 74023]], ![![131694, -112870, 20720, 50319, 64902]], ![![47935, -59072, 20440, 37186, 42167]]]
  g := ![![![1172, -1640, 459, -276, -463], ![-2517, 4711, -2379, 1016, -267], ![-2409, -2272, 5460, -1176, 6897], ![21542, -25154, 2914, -3709, -13740], ![-22688, 31748, -9071, 5578, 8926]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2

def I37N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11, 24, -17, 6, -9]] i)))

def SI37N3: IdealEqSpanCertificate' Table ![![-11, 24, -17, 6, -9]] 
 ![![37, 0, 0, 0, 0], ![30, 1, 0, 0, 0], ![25, 0, 1, 0, 0], ![17, 0, 0, 1, 0], ![33, 0, 0, 0, 1]] where
  M :=![![![-11, 24, -17, 6, -9], ![-54, 41, 21, 2, 63], ![378, -472, 106, -78, -177], ![-504, 802, -374, 165, 0], ![198, -448, 327, -112, 184]]]
  hmulB := by decide  
  f := ![![![-25763, 6936, -2549, -4484, -6087]], ![![-21876, 5889, -2165, -3808, -5169]], ![![-18809, 5064, -1863, -3276, -4446]], ![![-12343, 3326, -1223, -2151, -2919]], ![![-22449, 6044, -2220, -3906, -5303]]]
  g := ![![![-3, 24, -17, 6, -9], ![-106, 41, 21, 2, 63], ![515, -472, 106, -78, -177], ![-487, 802, -374, 165, 0], ![35, -448, 327, -112, 184]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N3 : Nat.card (O ⧸ I37N3) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N3)

lemma isPrimeI37N3 : Ideal.IsPrime I37N3 := prime_ideal_of_norm_prime hp37.out _ NI37N3
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![949657, -1228407, 322302, -211392, -390531]] ![![-37, 6, -2, -8, -10]]
  ![![6108671, -21444345, 20437588, -6148352, 16300715]] where
 M := ![![![6108671, -21444345, 20437588, -6148352, 16300715]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![6108671, -21444345, 20437588, -6148352, 16300715]] ![![1287, -1640, 459, -276, -463]]
  ![![-493094573899, 514694016357, -370876269, 66221574634, 373833908448]] where
 M := ![![![-493094573899, 514694016357, -370876269, 66221574634, 373833908448]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI37N2 : IdealMulLeCertificate' Table 
  ![![-493094573899, 514694016357, -370876269, 66221574634, 373833908448]] ![![-11, 24, -17, 6, -9]]
  ![![37, 0, 0, 0, 0]] where
 M := ![![![18133812457097, -104924649632207, 116628688364646, -32843088993264, 105714658449627]]]
 hmul := by decide  
 g := ![![![![490103039381, -2835801341411, 3152126712558, -887651053872, 2857152931071]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4796577, -1297976, 475372, 837340, 1136228]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![4796577, -1297976, 475372, 837340, 1136228]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![25, 21, 30, 1, 0], ![4, 28, 3, 0, 1]] where
  M :=![![![4796577, -1297976, 475372, 837340, 1136228], ![6817368, -1844307, 675592, 1190308, 1615356], ![9692136, -2624224, 961357, 1691396, 2295780], ![3478656, -940632, 343680, 607517, 822840], ![-3668072, 993400, -363044, -640004, -867179]]]
  hmulB := by decide  
  f := ![![![-274039, 237592, -45068, -107564, -137860]], ![![-827160, 538349, -7832, -137108, -231804]], ![![-1390824, 650528, 169437, 36620, -127236]], ![![-1607663, 886457, 99410, -98771, -285728]], ![![-674604, 429812, 243, -102120, -179519]]]
  g := ![![![-504435, -1236500, -684232, 837340, 1136228], ![-717116, -1757823, -972676, 1190308, 1615356], ![-1018924, -2498180, -1382143, 1691396, 2295780], ![-365869, -896049, -496350, 607517, 822840], ![385384, 944256, 522893, -640004, -867179]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [28, 15, 7, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 0, 39], [10, 40, 2], [0, 1]]
 g := ![![[5, 28, 9], [34, 2], [21, 9], [34, 34, 1], []], ![[24, 22, 7, 10], [15, 20], [27, 18], [12, 31, 16, 39], [13, 4]], ![[15, 16, 34, 18], [2, 4], [40, 5], [3, 21], [9, 4]]]
 h' := ![![[24, 0, 39], [11, 19, 38], [26, 1, 24], [32, 14, 3], [0, 0, 1], [0, 1]], ![[10, 40, 2], [36, 19, 6], [13, 12, 15], [20, 22, 10], [7, 21, 40], [24, 0, 39]], ![[0, 1], [1, 3, 38], [37, 28, 2], [3, 5, 28], [12, 20], [10, 40, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28, 28], []]
 b := ![[], [34, 23, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [28, 15, 7, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![23283343, -27100935, 3799299, -4222087, -13896420]
  a := ![-1, -7, -13, -23, -54]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![4498078, 10991772, 4198809, -4222087, -13896420]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 68921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![274039, -237592, 45068, 107564, 137860]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![274039, -237592, 45068, 107564, 137860]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![33, 22, 1, 0, 0], ![6, 21, 0, 1, 0], ![40, 33, 0, 0, 1]] where
  M :=![![![274039, -237592, 45068, 107564, 137860], ![827160, -538349, 7832, 137108, 231804], ![1390824, -650528, -169437, -36620, 127236], ![-31872, 416232, -283872, -420157, -416616], ![-770344, 353432, 98780, 27500, -63381]]]
  hmulB := by decide  
  f := ![![![-4796577, 1297976, -475372, -837340, -1136228]], ![![-6817368, 1844307, -675592, -1190308, -1615356]], ![![-7755153, 2098346, -768577, -1353912, -1837296]], ![![-4278606, 1157535, -423984, -747025, -1013724]], ![![-10077272, 2726531, -998692, -1759360, -2387529]]]
  g := ![![![-179829, -196032, 45068, 107564, 137860], ![-232344, -274133, 7832, 137108, 231804], ![51525, -8602, -169437, -36620, 127236], ![695646, 713001, -283872, -420157, -416616], ![-40484, -7455, 98780, 27500, -63381]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P1 : CertificateIrreducibleZModOfList' 41 2 2 5 [34, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 40], [0, 1]]
 g := ![![[8, 18], [2], [23], [18, 20], [1]], ![[32, 23], [2], [23], [31, 21], [1]]]
 h' := ![![[15, 40], [9, 31], [6, 24], [3, 8], [7, 15], [0, 1]], ![[0, 1], [23, 10], [38, 17], [0, 33], [27, 26], [15, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [8, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N1 : CertifiedPrimeIdeal' SI41N1 41 where
  n := 2
  hpos := by decide
  P := [34, 26, 1]
  hirr := P41P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11554, -952, -14432, 3240, -21552]
  a := ![0, -4, 10, -2, 36]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![32450, 23408, -14432, 3240, -21552]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N1 B_one_repr
lemma NI41N1 : Nat.card (O ⧸ I41N1) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![4796577, -1297976, 475372, 837340, 1136228]] ![![274039, -237592, 45068, 107564, 137860]]
  ![![41, 0, 0, 0, 0]] where
 M := ![![![-41, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0, 0, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0, 0, 0]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![0, 0, 0, 0, 43]] where
  M :=![![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![0, 0, 0, 0, 43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 5 2 5 [34, 17, 39, 9, 28, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 30, 2, 34, 3], [40, 25, 20, 20, 1], [19, 28, 24, 29, 1], [40, 2, 40, 3, 38], [0, 1]]
 g := ![![[5, 7, 31, 8, 4], [29, 38, 12, 27, 4], [14, 31, 9, 10], [1], []], ![[9, 22, 28, 20, 26, 18, 3, 33], [28, 31, 12, 34, 8, 36, 39, 5], [2, 36, 32, 6], [29, 2, 41, 36, 20, 6, 14, 20], [11, 23, 38, 9]], ![[20, 37, 31, 32, 11, 19, 12, 23], [28, 23, 25, 20, 29, 26, 37, 11], [21, 0, 20, 41], [18, 27, 4, 20, 42, 16, 14, 23], [21, 9, 12, 1]], ![[24, 19, 6, 37, 22, 6], [8, 14, 42, 9, 26, 37, 24, 6], [0, 20, 7, 21], [40, 17, 32, 29, 24, 0, 23, 40], [19, 40, 30, 1]], ![[33, 38, 30, 9, 39, 11, 35, 35], [36, 1, 22, 27, 5, 37, 16, 25], [27, 4, 22, 24], [2, 22, 12, 41, 37, 35, 9, 6], [25, 1, 1, 25]]]
 h' := ![![[2, 30, 2, 34, 3], [3, 42, 34, 13, 41], [35, 36, 14, 24, 2], [9, 26, 4, 34, 15], [0, 0, 1], [0, 1]], ![[40, 25, 20, 20, 1], [42, 34, 42, 2, 21], [29, 31, 7, 26, 4], [22, 42, 21, 2, 7], [17, 11, 0, 28, 35], [2, 30, 2, 34, 3]], ![[19, 28, 24, 29, 1], [5, 34, 37, 15, 18], [5, 5, 27, 4, 21], [26, 2, 21, 28, 27], [26, 4, 28, 16, 25], [40, 25, 20, 20, 1]], ![[40, 2, 40, 3, 38], [6, 7, 5, 36], [11, 5, 29, 32, 7], [21, 3, 4, 13, 8], [16, 26, 29, 42, 30], [19, 28, 24, 29, 1]], ![[0, 1], [20, 12, 11, 20, 6], [42, 9, 9, 0, 9], [10, 13, 36, 9, 29], [19, 2, 28, 0, 39], [40, 2, 40, 3, 38]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 1, 38, 34], [], [], []]
 b := ![[], [24, 23, 40, 23, 3], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 5
  hpos := by decide
  P := [34, 17, 39, 9, 28, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5824635530664, -8091151340062, 2733752780451, -1494675857552, -1618019443493]
  a := ![13, -8, -12, -24, -49]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![135456640248, -188166310234, 63575646057, -34759903664, -37628359151]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 147008443 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def PBC43 : ContainsPrimesAboveP 43 ![I43N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![43, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 43 (by decide) 𝕀

instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0, 0, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0, 0, 0]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![0, 0, 0, 0, 47]] where
  M :=![![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![0, 0, 0, 0, 47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 5 2 5 [17, 7, 1, 32, 31, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 31, 25, 34, 19], [18, 22, 34, 25, 16], [36, 39, 38, 17, 15], [32, 1, 44, 18, 44], [0, 1]]
 g := ![![[29, 23, 44, 34, 9], [7, 17, 23, 3, 7], [6, 5, 28, 17, 21], [1], []], ![[12, 3, 12, 24, 10, 35, 39, 20], [4, 38, 28, 34, 24, 32, 13, 39], [35, 1, 9, 3, 2, 22, 7, 23], [32, 40, 11, 20, 9, 15, 37, 31], [32, 7, 18, 32]], ![[0, 45, 38, 18, 23, 35, 25, 42], [6, 18, 40, 13, 14, 33, 33, 2], [39, 18, 14, 38, 25, 2, 16, 34], [33, 31, 22, 5, 30, 11, 36, 6], [10, 41, 8, 21]], ![[35, 28, 25, 1, 40, 38, 2, 15], [25, 36, 26, 23, 14, 32, 0, 22], [0, 3, 0, 15, 18, 16, 33, 40], [33, 44, 9, 34, 34, 12, 27, 45], [4, 17, 21, 37]], ![[17, 37, 31, 3, 23, 30, 25, 5], [2, 15, 16, 4, 21, 28, 17, 38], [27, 6, 42, 28, 13, 19, 0, 11], [35, 12, 38, 46, 9, 17, 29, 10], [16, 19, 36, 9]]]
 h' := ![![[24, 31, 25, 34, 19], [22, 8, 40, 34, 44], [39, 21, 3, 12, 17], [30, 40, 46, 15, 16], [0, 0, 1], [0, 1]], ![[18, 22, 34, 25, 16], [16, 22, 15, 8, 10], [11, 0, 42, 35, 30], [15, 35, 4, 2, 31], [32, 17, 35, 24, 25], [24, 31, 25, 34, 19]], ![[36, 39, 38, 17, 15], [40, 41, 34, 28, 19], [9, 6, 37, 20, 37], [37, 43, 16, 16, 14], [13, 25, 6, 24, 21], [18, 22, 34, 25, 16]], ![[32, 1, 44, 18, 44], [15, 16, 19, 32, 46], [17, 30, 7, 34, 22], [30, 2, 40, 40, 9], [6, 0, 17, 24, 35], [36, 39, 38, 17, 15]], ![[0, 1], [38, 7, 33, 39, 22], [25, 37, 5, 40, 35], [16, 21, 35, 21, 24], [0, 5, 35, 22, 13], [32, 1, 44, 18, 44]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25, 33, 18, 8], [], [], []]
 b := ![[], [45, 11, 8, 18, 7], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 5
  hpos := by decide
  P := [17, 7, 1, 32, 31, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-641677887, 1097485908, -604040334, 246927378, -161416800]
  a := ![-1, -4, -1, -8, -3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-13652721, 23350764, -12851922, 5253774, -3434400]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 229345007 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def PBC47 : ContainsPrimesAboveP 47 ![I47N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![47, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 47 (by decide) 𝕀

instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![187, -310, 146, -66, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![187, -310, 146, -66, 0]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![6, 32, 1, 1, 0], ![48, 10, 40, 0, 1]] where
  M :=![![![187, -310, 146, -66, 0], ![0, 267, -376, 94, -396], ![-2376, 2490, -35, 322, 1752], ![5256, -7310, 2470, -1351, -1464], ![-3696, 5966, -2854, 1242, -113]]]
  hmulB := by decide  
  f := ![![![527, -506, 118, 254, 312]], ![![1872, -1285, 60, 374, 588]], ![![3528, -1810, -323, 66, 480]], ![![1266, -856, 31, 239, 384]], ![![3456, -2048, -122, 350, 751]]]
  g := ![![![11, 34, 4, -66, 0], ![348, 23, 290, 94, -396], ![-1668, -478, -1329, 322, 1752], ![1578, 954, 1177, -1351, -1464], ![-108, -616, 8, 1242, -113]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [7, 5, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 15, 11], [50, 37, 42], [0, 1]]
 g := ![![[0, 2, 43], [11, 37], [25, 27, 10], [3, 9], [1]], ![[8, 14, 19, 24], [8, 24], [40, 5, 42, 24], [31, 49], [47, 18, 21, 6]], ![[19, 19, 16, 7], [12, 7], [40, 18, 25, 40], [24, 47], [47, 19, 40, 47]]]
 h' := ![![[0, 15, 11], [20, 16, 19], [37, 46, 14], [28, 45, 13], [46, 48, 50], [0, 1]], ![[50, 37, 42], [10, 2, 31], [38, 46, 17], [10, 24, 22], [42, 10, 46], [0, 15, 11]], ![[0, 1], [16, 35, 3], [43, 14, 22], [4, 37, 18], [15, 48, 10], [50, 37, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38, 26], []]
 b := ![[], [34, 24, 41], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [7, 5, 3, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9408992, 7581664, 3036121, 485863, 10270992]
  a := ![3, 3, 14, 13, 42]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9534562, -2088224, -7703574, 485863, 10270992]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 148877 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, 9, -6, 2, -3]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-5, 9, -6, 2, -3]] 
 ![![53, 0, 0, 0, 0], ![21, 1, 0, 0, 0], ![36, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![34, 0, 0, 0, 1]] where
  M :=![![![-5, 9, -6, 2, -3], ![-18, 12, 8, 0, 21], ![126, -157, 33, -26, -63], ![-180, 281, -127, 57, 6], ![78, -165, 114, -40, 58]]]
  hmulB := by decide  
  f := ![![![11, -187, 86, 142, 147]], ![![21, -89, 36, 62, 66]], ![![54, -157, 57, 102, 111]], ![![27, -38, 7, 17, 21]], ![![-20, -103, 56, 88, 88]]]
  g := ![![![2, 9, -6, 2, -3], ![-24, 12, 8, 0, 21], ![87, -157, 33, -26, -63], ![-42, 281, -127, 57, 6], ![-41, -165, 114, -40, 58]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1

def I53N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4879, -5851, 1958, 3608, 4119]] i)))

def SI53N2: IdealEqSpanCertificate' Table ![![4879, -5851, 1958, 3608, 4119]] 
 ![![53, 0, 0, 0, 0], ![30, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![23, 0, 0, 1, 0], ![45, 0, 0, 0, 1]] where
  M :=![![![4879, -5851, 1958, 3608, 4119], ![24714, -18388, 1876, 6502, 9291], ![55746, -31945, -2595, 4676, 11139], ![21060, -879, -9003, -9971, -7326], ![-31266, 17723, 1592, -2422, -6050]]]
  hmulB := by decide  
  f := ![![![-34921, 43505, -9598, 7184, 16665]], ![![-17880, 21720, -4162, 3482, 9303]], ![![-1439, 4304, -3801, 1184, -2802]], ![![-25447, 29564, -4093, 4479, 15117]], ![![-16803, 20824, -4472, 3418, 8167]]]
  g := ![![![-1696, -5851, 1958, 3608, 4119], ![129, -18388, 1876, 6502, 9291], ![7696, -31945, -2595, 4676, 11139], ![11612, -879, -9003, -9971, -7326], ![-4464, 17723, 1592, -2422, -6050]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N2 : Nat.card (O ⧸ I53N2) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N2)

lemma isPrimeI53N2 : Ideal.IsPrime I53N2 := prime_ideal_of_norm_prime hp53.out _ NI53N2
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![187, -310, 146, -66, 0]] ![![-5, 9, -6, 2, -3]]
  ![![34921, -43505, 9598, -7184, -16665]] where
 M := ![![![34921, -43505, 9598, -7184, -16665]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![34921, -43505, 9598, -7184, -16665]] ![![4879, -5851, 1958, 3608, 4119]]
  ![![53, 0, 0, 0, 0]] where
 M := ![![![-53, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1, I53N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
    exact isPrimeI53N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0 ⊙ MulI53N1)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-864195, 228192, -85533, -149362, -202687]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-864195, 228192, -85533, -149362, -202687]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![1, 17, 18, 31, 1]] where
  M :=![![![-864195, 228192, -85533, -149362, -202687], ![-1216122, 319719, -123857, -213778, -288111], ![-1728666, 463020, -182170, -312826, -418335], ![-646944, 192482, -72142, -126185, -166920], ![647350, -172836, 70305, 119360, 158476]]]
  hmulB := by decide  
  f := ![![![-4837, 904, 5617, -816, 9425]], ![![56550, -66011, 9513, -10064, -33171]], ![![-199026, 288196, -109246, 55176, 39129]], ![![89112, -230494, 186494, -60579, 123420]], ![![4053, -52695, 65723, -17681, 64252]]]
  g := ![![![-11212, 62269, 60387, 103965, -202687], ![-15729, 88434, 85799, 147757, -288111], ![-22209, 128385, 124540, 214501, -418335], ![-8136, 51358, 49702, 85565, -166920], ![8286, -48592, -47157, -81244, 158476]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 4 2 5 [4, 30, 2, 2, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [20, 11, 55, 35], [32, 52, 13, 25], [5, 54, 50, 58], [0, 1]]
 g := ![![[54, 45, 57, 3], [27, 30, 10, 57], [8, 9, 36], [29, 2, 57, 1], []], ![[54, 31, 26, 11, 58, 4], [7, 32, 30, 48, 52, 46], [51, 32, 57], [52, 45, 26, 11, 24, 20], [15, 6, 37, 20, 27, 41]], ![[17, 54, 56, 44, 33, 20], [6, 39, 5, 16, 16, 12], [19, 26, 21], [28, 3, 8, 6, 4, 5], [37, 47, 26, 45, 28, 49]], ![[9, 9, 27, 30, 36, 50], [9, 49, 51, 20, 37, 50], [6, 43, 4], [52, 15, 1, 22, 9, 30], [30, 9, 39, 30, 34, 58]]]
 h' := ![![[20, 11, 55, 35], [10, 31, 32, 48], [31, 47, 5, 36], [2, 7, 8, 53], [0, 0, 0, 1], [0, 1]], ![[32, 52, 13, 25], [53, 4, 51, 52], [19, 38, 7, 48], [20, 7, 43, 36], [34, 41, 37, 3], [20, 11, 55, 35]], ![[5, 54, 50, 58], [49, 53, 22, 15], [49, 3, 44, 31], [40, 21, 10, 27], [52, 31, 41, 37], [32, 52, 13, 25]], ![[0, 1], [45, 30, 13, 3], [21, 30, 3, 3], [35, 24, 57, 2], [5, 46, 40, 18], [5, 54, 50, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [20, 43, 55], []]
 b := ![[], [], [51, 55, 46, 45], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 4
  hpos := by decide
  P := [4, 30, 2, 2, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2913405439, -3842339160, 1091187516, -676263528, -1090941140]
  a := ![1, 6, 9, 18, 37]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![67870281, 249214580, 351324204, 561744268, -1090941140]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 12117361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4837, -904, -5617, 816, -9425]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![4837, -904, -5617, 816, -9425]] 
 ![![59, 0, 0, 0, 0], ![53, 1, 0, 0, 0], ![23, 0, 1, 0, 0], ![13, 0, 0, 1, 0], ![43, 0, 0, 0, 1]] where
  M :=![![![4837, -904, -5617, 816, -9425], ![-56550, 66011, -9513, 10064, 33171], ![199026, -288196, 109246, -55176, -39129], ![-89112, 230494, -186494, 60579, -123420], ![-102610, 29936, 104567, -13506, 184992]]]
  hmulB := by decide  
  f := ![![![864195, -228192, 85533, 149362, 202687]], ![![796923, -210405, 78934, 137796, 186958]], ![![366189, -96804, 36431, 63528, 86104]], ![![201381, -53542, 20069, 35049, 47489]], ![![618865, -163380, 61146, 106834, 145035]]]
  g := ![![![9773, -904, -5617, 816, -9425], ![-82941, 66011, -9513, 10064, 33171], ![260349, -288196, 109246, -55176, -39129], ![-59261, 230494, -186494, 60579, -123420], ![-201243, 29936, 104567, -13506, 184992]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-864195, 228192, -85533, -149362, -202687]] ![![4837, -904, -5617, 816, -9425]]
  ![![59, 0, 0, 0, 0]] where
 M := ![![![-59, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![28917, -33913, 5079, -5202, -16742]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![28917, -33913, 5079, -5202, -16742]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![50, 50, 43, 42, 1]] where
  M :=![![![28917, -33913, 5079, -5202, -16742], ![-100452, 145988, -55857, 28036, 19014], ![114084, -261371, 193038, -65634, 111174], ![383748, -341359, -79987, -30605, -373170], ![-567316, 670801, -107059, 103994, 320867]]]
  hmulB := by decide  
  f := ![![![-294223, 79591, -29149, -51344, -69682]], ![![-418092, 113058, -41435, -72966, -99018]], ![![-594108, 160633, -58926, -103732, -140742]], ![![-213180, 57685, -21203, -37299, -50574]], ![![-1145758, 309864, -113627, -200054, -271439]]]
  g := ![![![14197, 13167, 11885, 11442, -16742], ![-17232, -13192, -14319, -12632, 19014], ![-89256, -95411, -75204, -77622, 111174], ![312168, 300281, 261743, 256435, -373170], ![-272306, -252009, -227940, -219220, 320867]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 4 2 5 [43, 41, 0, 1, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [14, 7, 45, 17], [35, 37, 22, 2], [11, 16, 55, 42], [0, 1]]
 g := ![![[55, 31, 21, 34], [24, 47, 57], [35, 39, 24, 14], [19, 1, 60, 1], []], ![[53, 55, 36, 3, 29, 33], [23, 41, 14], [7, 46, 7, 58, 34, 17], [35, 39, 45, 55, 12, 43], [37, 22, 55, 29, 3, 33]], ![[24, 30, 19, 2, 31, 10], [1, 22, 14], [49, 59, 33, 38, 41, 53], [27, 32, 50, 0, 46, 8], [46, 39, 31, 42, 12, 8]], ![[42, 11, 47, 60, 22, 14], [28, 30, 57], [24, 39, 21, 6, 53, 46], [23, 53, 41, 26, 53, 58], [40, 3, 49, 31, 56, 34]]]
 h' := ![![[14, 7, 45, 17], [39, 48, 52, 41], [20, 26, 42, 39], [37, 32, 2, 40], [0, 0, 0, 1], [0, 1]], ![[35, 37, 22, 2], [33, 7, 48, 17], [31, 29, 26, 21], [36, 36, 54, 1], [55, 6, 58, 15], [14, 7, 45, 17]], ![[11, 16, 55, 42], [15, 5, 14, 26], [34, 11, 34, 40], [15, 48, 9, 22], [27, 42, 50, 59], [35, 37, 22, 2]], ![[0, 1], [52, 1, 8, 38], [55, 56, 20, 22], [11, 6, 57, 59], [38, 13, 14, 47], [11, 16, 55, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [24, 26, 38], []]
 b := ![[], [], [42, 17, 55, 42], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 4
  hpos := by decide
  P := [43, 41, 0, 1, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1848119, 744934, -3626480, 697117, -5121294]
  a := ![4, 0, -2, -1, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![4228079, 4209994, 3550642, 3537565, -5121294]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 13845841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![294223, -79591, 29149, 51344, 69682]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![294223, -79591, 29149, 51344, 69682]] 
 ![![61, 0, 0, 0, 0], ![56, 1, 0, 0, 0], ![36, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![46, 0, 0, 0, 1]] where
  M :=![![![294223, -79591, 29149, 51344, 69682], ![418092, -113058, 41435, 72966, 99018], ![594108, -160633, 58926, 103732, 140742], ![213180, -57685, 21203, 37299, 50574], ![-224716, 60735, -22297, -39240, -53235]]]
  hmulB := by decide  
  f := ![![![-28917, 33913, -5079, 5202, 16742]], ![![-24900, 28740, -3747, 4316, 15058]], ![![-18936, 24299, -6162, 4146, 8058]], ![![-6765, 6152, 1228, 587, 6392]], ![![-12506, 14577, -2075, 2218, 7365]]]
  g := ![![![7299, -79591, 29149, 51344, 69682], ![10326, -113058, 41435, 72966, 99018], ![14596, -160633, 58926, 103732, 140742], ![5189, -57685, 21203, 37299, 50574], ![-5494, 60735, -22297, -39240, -53235]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![28917, -33913, 5079, -5202, -16742]] ![![294223, -79591, 29149, 51344, 69682]]
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


lemma PB687I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB687I1 : PrimesBelowBoundCertificateInterval O 23 61 687 where
  m := 9
  g := ![3, 4, 4, 2, 1, 1, 3, 2, 2]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB687I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1, I29N2]
    · exact ![I31N0, I31N1, I31N2, I31N3]
    · exact ![I37N0, I37N1, I37N2, I37N3]
    · exact ![I41N0, I41N1]
    · exact ![I43N0]
    · exact ![I47N0]
    · exact ![I53N0, I53N1, I53N2]
    · exact ![I59N0, I59N1]
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
    · exact ![24389, 29, 29]
    · exact ![961, 31, 31, 31]
    · exact ![1369, 37, 37, 37]
    · exact ![68921, 1681]
    · exact ![147008443]
    · exact ![229345007]
    · exact ![148877, 53, 53]
    · exact ![12117361, 59]
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
      exact NI29N2
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
      exact NI31N2
      exact NI31N3
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
      exact NI37N2
      exact NI37N3
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
      exact NI53N2
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
  β := ![I29N1, I29N2, I31N1, I31N2, I31N3, I37N1, I37N2, I37N3, I53N1, I53N2, I59N1, I61N1]
  Il := ![[I29N1, I29N2], [I31N1, I31N2, I31N3], [I37N1, I37N2, I37N3], [], [], [], [I53N1, I53N2], [I59N1], [I61N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
