
import IdealArithmetic.Examples.NF5_3_379687500_2.RI5_3_379687500_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-38, 245, 27, -69, -362]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![-38, 245, 27, -69, -362]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-38, 245, 27, -69, -362], ![1594, 1004, 221, -518, -3208], ![-1764, -4314, -629, 1542, 8772], ![-7380, -819, -564, 1240, 8610], ![1866, 569, 186, -423, -2767]]]
  hmulB := by decide  
  f := ![![![216, 431, 23, -134, -872]], ![![-818, -1246, -76, 397, 2546]], ![![3798, 6156, 361, -1956, -12576]], ![![-11703, -18807, -1116, 5959, 38340]], ![![1949, 3178, 187, -1006, -6477]]]
  g := ![![![-19, 245, 27, -69, -362], ![797, 1004, 221, -518, -3208], ![-882, -4314, -629, 1542, 8772], ![-3690, -819, -564, 1240, 8610], ![933, 569, 186, -423, -2767]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2653, -1496, -166, 579, 3357]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![-2653, -1496, -166, 579, 3357]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-2653, -1496, -166, 579, 3357], ![-4434, -2455, -276, 955, 5523], ![-7706, -4500, -487, 1725, 10049], ![-2086, -642, -114, 306, 1609], ![-2900, -1718, -184, 656, 3829]]]
  hmulB := by decide  
  f := ![![![348, 232, 14, -113, -629]], ![![973, 637, 34, -312, -1730]], ![![3975, 2672, 141, -1295, -7165]], ![![7639, 5150, 298, -2496, -13859]], ![![-606, -418, -26, 201, 1118]]]
  g := ![![![-785, -1496, -166, 579, 3357], ![-1329, -2455, -276, 955, 5523], ![-2222, -4500, -487, 1725, 10049], ![-818, -642, -114, 306, 1609], ![-827, -1718, -184, 656, 3829]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 30, 3, -11, -63]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![53, 30, 3, -11, -63]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![53, 30, 3, -11, -63], ![106, 71, 9, -27, -157], ![194, 84, 14, -37, -227], ![-130, -126, -21, 60, 355], ![94, 66, 9, -27, -158]]]
  hmulB := by decide  
  f := ![![![-1296, -2076, -123, 659, 4237]], ![![2655, 4253, 252, -1350, -8680]], ![![-17491, -28014, -1660, 8893, 57177]], ![![50695, 81204, 4812, -25777, -165734]], ![![-9387, -15036, -891, 4773, 30688]]]
  g := ![![![47, 30, 3, -11, -63], ![105, 71, 9, -27, -157], ![180, 84, 14, -37, -227], ![-199, -126, -21, 60, 355], ![102, 66, 9, -27, -158]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![-38, 245, 27, -69, -362]] ![![-38, 245, 27, -69, -362]]
  ![![178074, -29275, 7720, -15088, -127796]] where
 M := ![![![178074, -29275, 7720, -15088, -127796]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI2N1 : IdealMulLeCertificate' Table 
  ![![178074, -29275, 7720, -15088, -127796]] ![![-38, 245, 27, -69, -362]]
  ![![-194167138, -79426902, -21778081, 50130172, 320875104]] where
 M := ![![![-194167138, -79426902, -21778081, 50130172, 320875104]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI2N2 : IdealMulLeCertificate' Table 
  ![![-194167138, -79426902, -21778081, 50130172, 320875104]] ![![-2653, -1496, -166, 579, 3357]]
  ![![16852376, 21448262, 3636563, -8753181, -51578017]] where
 M := ![![![16852376, 21448262, 3636563, -8753181, -51578017]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![16852376, 21448262, 3636563, -8753181, -51578017]] ![![53, 30, 3, -11, -63]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![161764854, 32620858, 14118016, -31616442, -212629192]]]
 hmul := by decide  
 g := ![![![![80882427, 16310429, 7059008, -15808221, -106314596]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N0, I2N0, I2N1, I2N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N0
    exact isPrimeI2N0
    exact isPrimeI2N1
    exact isPrimeI2N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1 ⊙ MulI2N2 ⊙ MulI2N3)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1173, 784, 43, -381, -2112]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![1173, 784, 43, -381, -2112]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![1173, 784, 43, -381, -2112], ![5634, 3759, 206, -1828, -10134], ![27008, 18018, 983, -8762, -48566], ![51342, 34293, 1875, -16669, -92394], ![-4082, -2729, -149, 1326, 7349]]]
  hmulB := by decide  
  f := ![![![935, 509, 58, -199, -1148]], ![![562, 343, 36, -130, -762]], ![![764, 286, 43, -126, -686]], ![![724, 841, 59, -279, -1750]], ![![890, 415, 53, -170, -959]]]
  g := ![![![1799, 784, 43, -381, -2112], ![8634, 3759, 206, -1828, -10134], ![41380, 18018, 983, -8762, -48566], ![78710, 34293, 1875, -16669, -92394], ![-6260, -2729, -149, 1326, 7349]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25, 22, 4, -10, -60]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![25, 22, 4, -10, -60]] 
 ![![3, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![25, 22, 4, -10, -60], ![20, -35, -4, 8, 40], ![-240, -156, -39, 80, 504], ![376, 534, 78, -211, -1216], ![-48, -98, -14, 36, 205]]]
  hmulB := by decide  
  f := ![![![-29, 42, 0, -10, -76]], ![![-162, -151, -12, 52, 320]], ![![386, 760, 41, -236, -1536]], ![![-1504, -2382, -142, 757, 4864]], ![![202, 414, 22, -128, -835]]]
  g := ![![![31, 22, 4, -10, -60], ![6, -35, -4, 8, 40], ![-286, -156, -39, 80, 504], ![528, 534, 78, -211, -1216], ![-78, -98, -14, 36, 205]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![1173, 784, 43, -381, -2112]] ![![1173, 784, 43, -381, -2112]]
  ![![-3985789, -2660523, -145475, 1293546, 7170256]] where
 M := ![![![-3985789, -2660523, -145475, 1293546, 7170256]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![-3985789, -2660523, -145475, 1293546, 7170256]] ![![25, 22, 4, -10, -60]]
  ![![24259823, 16193523, 885465, -7873284, -43642436]] where
 M := ![![![24259823, 16193523, 885465, -7873284, -43642436]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![24259823, 16193523, 885465, -7873284, -43642436]] ![![25, 22, 4, -10, -60]]
  ![![-147663421, -98564667, -5389983, 47922382, 265639864]] where
 M := ![![![-147663421, -98564667, -5389983, 47922382, 265639864]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N3 : IdealMulLeCertificate' Table 
  ![![-147663421, -98564667, -5389983, 47922382, 265639864]] ![![25, 22, 4, -10, -60]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![898819215, 599850747, 32802021, -291669264, -1616777244]]]
 hmul := by decide  
 g := ![![![![299606405, 199950249, 10934007, -97223088, -538925748]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![51, -135, -13, 34, 170]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![51, -135, -13, 34, 170]] 
 ![![5, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![51, -135, -13, 34, 170], ![-1020, -697, -148, 348, 2142], ![816, 2580, 361, -890, -5010], ![5102, 1068, 450, -1009, -6770], ![-1254, -474, -136, 312, 2009]]]
  hmulB := by decide  
  f := ![![![39, 87, 7, -20, -146]], ![![-122, -127, -6, 52, 306]], ![![11, 363, 24, -70, -564]], ![![-1871, -2295, -133, 815, 5020]], ![![280, 390, 24, -128, -811]]]
  g := ![![![-8, -135, -13, 34, 170], ![-822, -697, -148, 348, 2142], ![1241, 2580, 361, -890, -5010], ![3413, 1068, 450, -1009, -6770], ![-900, -474, -136, 312, 2009]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![51, -135, -13, 34, 170]] ![![51, -135, -13, 34, 170]]
  ![![89981, 9402, 6804, -14942, -104020]] where
 M := ![![![89981, 9402, 6804, -14942, -104020]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![89981, 9402, 6804, -14942, -104020]] ![![51, -135, -13, 34, 170]]
  ![![54758051, 32201115, 7317815, -17102072, -106471026]] where
 M := ![![![54758051, 32201115, 7317815, -17102072, -106471026]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![54758051, 32201115, 7317815, -17102072, -106471026]] ![![51, -135, -13, 34, 170]]
  ![![22178755601, 21245702088, 3948238668, -9408063060, -56497859944]] where
 M := ![![![22178755601, 21245702088, 3948238668, -9408063060, -56497859944]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![22178755601, 21245702088, 3948238668, -9408063060, -56497859944]] ![![51, -135, -13, 34, 170]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![5530641796635, 9116243667345, 1442707002695, -3500947072450, -20313607113310]]]
 hmul := by decide  
 g := ![![![![1106128359327, 1823248733469, 288541400539, -700189414490, -4062721422662]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0, 0]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0, 0, 0]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]] where
  M :=![![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 5 2 2 [3, 5, 6, 2, 1, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 1, 1, 3, 4], [4, 2, 6, 1, 1], [0, 6, 4, 0, 2], [6, 4, 3, 3], [0, 1]]
 g := ![![[6, 6, 1], []], ![[5, 2, 3, 1, 5, 0, 6, 4], [5, 4, 5, 2, 5, 4, 3, 1]], ![[3, 3, 2, 4, 3, 3, 3, 4], [2, 4, 1, 6, 2, 3, 2, 1]], ![[5, 4, 5, 6, 1, 2], [5, 2, 5, 3, 0, 5, 6, 1]], ![[1, 3, 4, 5, 6, 3, 6], [6, 5, 4, 5, 6]]]
 h' := ![![[3, 1, 1, 3, 4], [0, 0, 0, 1], [0, 1]], ![[4, 2, 6, 1, 1], [5, 4, 6, 0, 1], [3, 1, 1, 3, 4]], ![[0, 6, 4, 0, 2], [2, 4, 0, 6, 2], [4, 2, 6, 1, 1]], ![[6, 4, 3, 3], [6, 4, 1, 6], [0, 6, 4, 0, 2]], ![[0, 1], [2, 2, 0, 1, 4], [6, 4, 3, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 5, 4, 4], [], [], []]
 b := ![[], [5, 2, 0, 4, 6], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 5
  hpos := by decide
  P := [3, 5, 6, 2, 1, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5081977626366844, 5658357036124072, 326523977935505, -2095236243182649, -12706747099507363]
  a := ![935, 890, 79, -369, -2189]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![725996803766692, 808336719446296, 46646282562215, -299319463311807, -1815249585643909]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 16807 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def PBC7 : ContainsPrimesAboveP 7 ![I7N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![7, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 7 (by decide) 𝕀

instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-115, -75, -4, 37, 204]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-115, -75, -4, 37, 204]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![4, 10, 3, 1, 0], ![2, 1, 1, 0, 1]] where
  M :=![![![-115, -75, -4, 37, 204], ![-578, -397, -22, 190, 1058], ![-2676, -1734, -95, 858, 4734], ![-5316, -3693, -201, 1753, 9786], ![436, 315, 17, -146, -821]]]
  hmulB := by decide  
  f := ![![![115, 66, 7, -25, -144]], ![![218, 133, 16, -52, -302]], ![![384, 186, 23, -78, -462]], ![![342, 191, 22, -75, -436]], ![![90, 50, 6, -20, -117]]]
  g := ![![![-61, -59, -29, 37, 204], ![-314, -305, -150, 190, 1058], ![-1416, -1368, -673, 858, 4734], ![-2900, -2819, -1386, 1753, 9786], ![242, 236, 116, -146, -821]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [8, 3, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 7, 5], [7, 3, 6], [0, 1]]
 g := ![![[1, 6, 9], [9, 10, 1], []], ![[6, 7, 7, 4], [10, 10, 6, 1], [1, 3]], ![[0, 4, 9, 10], [4, 6, 1, 8], [0, 3]]]
 h' := ![![[3, 7, 5], [5, 3, 8], [0, 0, 1], [0, 1]], ![[7, 3, 6], [0, 9, 6], [1, 4, 3], [3, 7, 5]], ![[0, 1], [0, 10, 8], [5, 7, 7], [7, 3, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5], []]
 b := ![[], [9, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [8, 3, 1, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4970813199, -6051870672, -359224092, 2152282488, 13261591544]
  a := ![-1313, -1315, -111, 518, 3074]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3645738749, -3712389736, -1825242100, 2152282488, 13261591544]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 1331 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-115, -66, -7, 25, 144]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![-115, -66, -7, 25, 144]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![1, 6, 1, 0, 0], ![2, 7, 0, 1, 0], ![7, 10, 0, 0, 1]] where
  M :=![![![-115, -66, -7, 25, 144], ![-218, -133, -16, 52, 302], ![-384, -186, -23, 78, 462], ![30, 51, 15, -29, -186], ![-158, -99, -13, 40, 235]]]
  hmulB := by decide  
  f := ![![![115, 75, 4, -37, -204]], ![![578, 397, 22, -190, -1058]], ![![569, 381, 21, -185, -1026]], ![![872, 602, 33, -287, -1600]], ![![559, 380, 21, -183, -1017]]]
  g := ![![![-106, -149, -7, 25, 144], ![-220, -311, -16, 52, 302], ![-341, -474, -23, 78, 462], ![125, 184, 15, -29, -186], ![-170, -241, -13, 40, 235]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P1 : CertificateIrreducibleZModOfList' 11 2 2 3 [6, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 10], [0, 1]]
 g := ![![[2, 9], [0, 1], [1]], ![[4, 2], [10, 10], [1]]]
 h' := ![![[10, 10], [0, 8], [5, 10], [0, 1]], ![[0, 1], [3, 3], [6, 1], [10, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [1, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N1 : CertifiedPrimeIdeal' SI11N1 11 where
  n := 2
  hpos := by decide
  P := [6, 1, 1]
  hirr := P11P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-24966, -21603, -1376, 9023, 53210]
  a := ![129, 120, 11, -51, -302]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-37646, -55328, -1376, 9023, 53210]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N1 B_one_repr
lemma NI11N1 : Nat.card (O ⧸ I11N1) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-115, -75, -4, 37, 204]] ![![-115, -66, -7, 25, 144]]
  ![![11, 0, 0, 0, 0]] where
 M := ![![![-11, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-23, -48, -2, 14, 90]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-23, -48, -2, 14, 90]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![10, 9, 1, 0, 0], ![2, 12, 0, 1, 0], ![5, 3, 0, 0, 1]] where
  M :=![![![-23, -48, -2, 14, 90], ![140, 229, 10, -70, -458], ![-924, -1344, -85, 438, 2826], ![2796, 4296, 282, -1393, -8922], ![-484, -744, -50, 242, 1547]]]
  hmulB := by decide  
  f := ![![![-659, -432, -26, 206, 1146]], ![![-2932, -1943, -110, 938, 5206]], ![![-3590, -2379, -135, 1148, 6372]], ![![-4786, -3180, -178, 1539, 8538]], ![![-779, -513, -30, 246, 1367]]]
  g := ![![![-37, -36, -2, 14, 90], ![190, 181, 10, -70, -458], ![-1160, -1101, -85, 438, 2826], ![3644, 3480, 282, -1393, -8922], ![-631, -603, -50, 242, 1547]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [8, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 12], [0, 1]]
 g := ![![[1, 10], [3], [5, 1]], ![[12, 3], [3], [10, 12]]]
 h' := ![![[5, 12], [3, 7], [12, 4], [0, 1]], ![[0, 1], [12, 6], [6, 9], [5, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [3, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [8, 8, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2872739, -2640380, -166735, 1068454, 6360508]
  a := ![-1401, -1316, -119, 552, 3280]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2703449, -2541749, -166735, 1068454, 6360508]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, -8, -1, 3, 18]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![-7, -8, -1, 3, 18]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![3, 11, 1, 0, 0], ![8, 7, 0, 1, 0], ![10, 12, 0, 0, 1]] where
  M :=![![![-7, -8, -1, 3, 18], ![-6, 11, 0, -2, -12], ![4, -18, 5, 0, 8], ![110, 123, 3, -39, -272], ![-26, -23, -1, 8, 55]]]
  hmulB := by decide  
  f := ![![![-39, -25, -2, 11, 62]], ![![-134, -85, -6, 40, 224]], ![![-163, -104, -7, 49, 274]], ![![-166, -108, -7, 51, 284]], ![![-150, -95, -7, 44, 247]]]
  g := ![![![-16, -18, -1, 3, 18], ![10, 13, 0, -2, -12], ![-7, -13, 5, 0, 8], ![241, 279, 3, -39, -272], ![-49, -56, -1, 8, 55]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P1 : CertificateIrreducibleZModOfList' 13 2 2 3 [11, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 12], [0, 1]]
 g := ![![[3, 12], [1], [6, 1]], ![[10, 1], [1], [12, 12]]]
 h' := ![![[6, 12], [3, 8], [12, 12], [0, 1]], ![[0, 1], [12, 5], [6, 1], [6, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [9, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N1 : CertifiedPrimeIdeal' SI13N1 13 where
  n := 2
  hpos := by decide
  P := [11, 7, 1]
  hirr := P13P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3801133, -3660717, -234390, 1449115, 8680338]
  a := ![1656, 1578, 142, -652, -3877]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7807251, -8876176, -234390, 1449115, 8680338]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N1 B_one_repr
lemma NI13N1 : Nat.card (O ⧸ I13N1) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N1

def I13N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, -845, -95, 242, 1278]] i)))

def SI13N2: IdealEqSpanCertificate' Table ![![101, -845, -95, 242, 1278]] 
 ![![13, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![101, -845, -95, 242, 1278], ![-5356, -3319, -736, 1724, 10690], ![6240, 14676, 2155, -5278, -30078], ![24418, 2208, 1806, -3951, -27670], ![-6210, -1802, -608, 1380, 9059]]]
  hmulB := by decide  
  f := ![![![54169, 30269, 3381, -11744, -68006]], ![![32102, 18011, 2006, -6980, -40442]], ![![24119, 13227, 1498, -5158, -29792]], ![![42383, 24543, 2673, -9427, -54860]], ![![33473, 18571, 2085, -7220, -41767]]]
  g := ![![![-436, -845, -95, 242, 1278], ![-5660, -3319, -736, 1724, 10690], ![13059, 14676, 2155, -5278, -30078], ![18077, 2208, 1806, -3951, -27670], ![-5339, -1802, -608, 1380, 9059]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N2 : Nat.card (O ⧸ I13N2) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N2)

lemma isPrimeI13N2 : Ideal.IsPrime I13N2 := prime_ideal_of_norm_prime hp13.out _ NI13N2
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-23, -48, -2, 14, 90]] ![![-7, -8, -1, 3, 18]]
  ![![-359, -656, -35, 201, 1288]] where
 M := ![![![-359, -656, -35, 201, 1288]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI13N1 : IdealMulLeCertificate' Table 
  ![![-359, -656, -35, 201, 1288]] ![![101, -845, -95, 242, 1278]]
  ![![13, 0, 0, 0, 0]] where
 M := ![![![168415, 89791, 21398, -49803, -312390]]]
 hmul := by decide  
 g := ![![![![12955, 6907, 1646, -3831, -24030]]]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1185, 671, 73, -264, -1526]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![1185, 671, 73, -264, -1526]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![3, 2, 14, 2, 1]] where
  M :=![![![1185, 671, 73, -264, -1526], ![2152, 1225, 126, -492, -2830], ![4400, 2616, 241, -1090, -6206], ![3566, 2298, 174, -1051, -5906], ![990, 524, 64, -190, -1115]]]
  hmulB := by decide  
  f := ![![![137, 221, 13, -70, -450]], ![![-700, -1123, -66, 356, 2290]], ![![3600, 5748, 341, -1826, -11742]], ![![-10978, -17556, -1044, 5577, 35854]], ![![1725, 2751, 163, -874, -5621]]]
  g := ![![![339, 219, 1261, 164, -1526], ![626, 405, 2338, 304, -2830], ![1354, 884, 5125, 666, -6206], ![1252, 830, 4874, 633, -5906], ![255, 162, 922, 120, -1115]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 4 2 4 [9, 6, 8, 1, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 16, 4, 11], [8, 16], [3, 1, 13, 6], [0, 1]]
 g := ![![[7, 2, 7, 9], [2, 15, 1], [1], []], ![[4, 7, 14, 13, 13, 6], [6, 1, 13], [15, 7, 9], [11, 1, 2]], ![[13, 11, 2, 8], [16, 3, 1], [1], []], ![[3, 4, 15, 15, 15, 11], [13, 12, 13], [1, 2, 9], [11, 1, 2]]]
 h' := ![![[5, 16, 4, 11], [12, 12, 14, 3], [8, 11, 9, 16], [0, 0, 1], [0, 1]], ![[8, 16], [6, 6, 15, 13], [3, 0, 14, 9], [11, 0, 14, 3], [5, 16, 4, 11]], ![[3, 1, 13, 6], [7, 4, 1, 14], [7, 3, 2, 1], [13, 1, 1], [8, 16]], ![[0, 1], [3, 12, 4, 4], [16, 3, 9, 8], [12, 16, 1, 14], [3, 1, 13, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [7], []]
 b := ![[], [], [5, 13, 9, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 4
  hpos := by decide
  P := [9, 6, 8, 1, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-27654690955, -44191891428, -2641716976, 14050038124, 90297311068]
  a := ![-170, -162, -16, 62, 398]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-17561566127, -13222736092, -74517886584, -9796740236, 90297311068]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 83521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-137, -221, -13, 70, 450]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![-137, -221, -13, 70, 450]] 
 ![![17, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![13, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![11, 0, 0, 0, 1]] where
  M :=![![![-137, -221, -13, 70, 450], ![700, 1123, 66, -356, -2290], ![-3600, -5748, -341, 1826, 11742], ![10978, 17556, 1044, -5577, -35854], ![-1870, -2990, -178, 950, 6107]]]
  hmulB := by decide  
  f := ![![![-1185, -671, -73, 264, 1526]], ![![-266, -151, -16, 60, 346]], ![![-1165, -667, -70, 266, 1532]], ![![-628, -372, -36, 155, 886]], ![![-825, -465, -51, 182, 1053]]]
  g := ![![![-288, -221, -13, 70, 450], ![1466, 1123, 66, -356, -2290], ![-7517, -5748, -341, 1826, 11742], ![22950, 17556, 1044, -5577, -35854], ![-3909, -2990, -178, 950, 6107]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![1185, 671, 73, -264, -1526]] ![![-137, -221, -13, 70, 450]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![253, 407, 24, -129, -830]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![253, 407, 24, -129, -830]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![16, 8, 17, 1, 0], ![3, 15, 18, 0, 1]] where
  M :=![![![253, 407, 24, -129, -830], ![-1310, -2089, -124, 664, 4268], ![6624, 10626, 631, -3372, -21684], ![-20268, -32445, -1923, 10303, 66228], ![3444, 5519, 327, -1752, -11263]]]
  hmulB := by decide  
  f := ![![![-69, -44, -5, 17, 98]], ![![-146, -79, -10, 34, 200]], ![![-180, -54, 1, 24, 132]], ![![-286, -127, -8, 53, 300]], ![![-301, -122, -8, 53, 303]]]
  g := ![![![253, 731, 903, -129, -830], ![-1302, -3759, -4644, 664, 4268], ![6612, 19098, 23593, -3372, -21684], ![-20200, -58331, -72062, 10303, 66228], ![3435, 9920, 12255, -1752, -11263]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 3 2 4 [11, 13, 7, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 14, 13], [18, 4, 6], [0, 1]]
 g := ![![[4, 0, 5], [2, 13, 4], [12, 1], []], ![[1, 16, 7, 13], [16, 5, 8, 12], [11, 16], [17, 17]], ![[10, 7, 10, 4], [8, 5, 17, 1], [12, 6], [5, 17]]]
 h' := ![![[13, 14, 13], [16, 3, 9], [1, 4, 17], [0, 0, 1], [0, 1]], ![[18, 4, 6], [7, 7, 18], [13, 11, 6], [1, 13, 4], [13, 14, 13]], ![[0, 1], [2, 9, 11], [10, 4, 15], [3, 6, 14], [18, 4, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 9], []]
 b := ![[], [1, 14, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 3
  hpos := by decide
  P := [11, 13, 7, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-50143991152, -48160927572, -2772642564, 19122695652, 113427470724]
  a := ![-2743, -2614, -230, 1086, 6422]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-36652080724, -100134450192, -124713312720, 19122695652, 113427470724]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 6859 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![789, 1752, 260, -636, -3634]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![789, 1752, 260, -636, -3634]] 
 ![![19, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![13, 0, 0, 0, 1]] where
  M :=![![![789, 1752, 260, -636, -3634], ![6368, 2069, 650, -1482, -9650], ![-18260, -23748, -4001, 9638, 56714], ![-16104, 16062, 912, -2693, -10314], ![5336, -1638, 140, -222, -2589]]]
  hmulB := by decide  
  f := ![![![-2105, -6348, -292, 1904, 12634]], ![![918, 269, 50, -130, -678]], ![![-6602, -11316, -649, 3566, 23022]], ![![19476, 29202, 1788, -9341, -59802]], ![![-4799, -9894, -524, 3058, 19953]]]
  g := ![![![2349, 1752, 260, -636, -3634], ![7152, 2069, 650, -1482, -9650], ![-37932, -23748, -4001, 9638, 56714], ![2742, 16062, 912, -2693, -10314], ![2695, -1638, 140, -222, -2589]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1

def I19N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5557, -3118, -347, 1209, 7004]] i)))

def SI19N2: IdealEqSpanCertificate' Table ![![-5557, -3118, -347, 1209, 7004]] 
 ![![19, 0, 0, 0, 0], ![18, 1, 0, 0, 0], ![18, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![-5557, -3118, -347, 1209, 7004], ![-9418, -5303, -588, 2056, 11914], ![-15928, -8898, -989, 3466, 20050], ![-5946, -3561, -369, 1381, 8034], ![-5846, -3247, -365, 1260, 7293]]]
  hmulB := by decide  
  f := ![![![1689, 2929, 458, -1113, -6440]], ![![2068, 2863, 474, -1144, -6706]], ![![-110, 816, 91, -232, -1222]], ![![-744, 1815, 171, -449, -2226]], ![![767, 522, 111, -261, -1607]]]
  g := ![![![1147, -3118, -347, 1209, 7004], ![1950, -5303, -588, 2056, 11914], ![3252, -8898, -989, 3466, 20050], ![1296, -3561, -369, 1381, 8034], ![1195, -3247, -365, 1260, 7293]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N2 : Nat.card (O ⧸ I19N2) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N2)

lemma isPrimeI19N2 : Ideal.IsPrime I19N2 := prime_ideal_of_norm_prime hp19.out _ NI19N2
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![253, 407, 24, -129, -830]] ![![789, 1752, 260, -636, -3634]]
  ![![1689, 2929, 458, -1113, -6440]] where
 M := ![![![1689, 2929, 458, -1113, -6440]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI19N1 : IdealMulLeCertificate' Table 
  ![![1689, 2929, 458, -1113, -6440]] ![![-5557, -3118, -347, 1209, 7004]]
  ![![19, 0, 0, 0, 0]] where
 M := ![![![19, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![433, 236, 29, -87, -510]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![433, 236, 29, -87, -510]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![1, 10, 10, 16, 1]] where
  M :=![![![433, 236, 29, -87, -510], ![510, 247, 40, -74, -456], ![-188, -270, 29, 212, 1100], ![-2526, -1731, -75, 869, 4788], ![770, 455, 41, -192, -1093]]]
  hmulB := by decide  
  f := ![![![-1, 5, 0, -1, -6]], ![![2, -7, 2, 0, 4]], ![![112, 114, 7, -40, -268]], ![![-408, -513, -45, 181, 1152]], ![![-231, -306, -27, 107, 677]]]
  g := ![![![41, 232, 223, 351, -510], ![42, 209, 200, 314, -456], ![-56, -490, -477, -756, 1100], ![-318, -2157, -2085, -3293, 4788], ![81, 495, 477, 752, -1093]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 4 2 4 [10, 3, 21, 8, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 18, 12, 7], [18, 20, 4, 14], [5, 7, 7, 2], [0, 1]]
 g := ![![[10, 1, 22, 6], [17, 5, 19, 9], [15, 1], []], ![[12, 22, 3, 12, 7, 21], [18, 14, 13, 16, 17, 21], [8, 20, 17, 6, 4, 5], [9, 6, 3]], ![[3, 7, 7, 14, 6, 19], [12, 6, 2, 3, 22, 15], [1, 20, 11, 21, 7, 15], [12, 16, 12]], ![[6, 9, 14, 17, 1, 8], [0, 7, 11, 4, 17, 8], [18, 21, 20, 6, 15, 16], [2, 19, 4]]]
 h' := ![![[15, 18, 12, 7], [14, 20, 22, 11], [11, 14, 4, 20], [0, 0, 1], [0, 1]], ![[18, 20, 4, 14], [0, 18, 4, 7], [9, 16, 2, 16], [20, 16, 10, 21], [15, 18, 12, 7]], ![[5, 7, 7, 2], [4, 7, 16, 7], [14, 11, 15, 12], [20, 18, 9, 12], [18, 20, 4, 14]], ![[0, 1], [14, 1, 4, 21], [14, 5, 2, 21], [5, 12, 3, 13], [5, 7, 7, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [2, 4, 19], []]
 b := ![[], [], [13, 8, 16, 20], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 4
  hpos := by decide
  P := [10, 3, 21, 8, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1761650979, -2652009210, -156152963, 862186298, 5490934398]
  a := ![-129, -126, -11, 50, 302]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-315329799, -2502667530, -2394152041, -3782294090, 5490934398]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 279841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -5, 0, 1, 6]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![1, -5, 0, 1, 6]] 
 ![![23, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![22, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![20, 0, 0, 0, 1]] where
  M :=![![![1, -5, 0, 1, 6], ![-2, 7, -2, 0, -4], ![-112, -114, -7, 40, 268], ![408, 513, 45, -181, -1152], ![-76, -95, -9, 34, 215]]]
  hmulB := by decide  
  f := ![![![-433, -236, -29, 87, 510]], ![![-41, -21, -3, 7, 42]], ![![-406, -214, -29, 74, 440]], ![![91, 65, 2, -34, -186]], ![![-410, -225, -27, 84, 491]]]
  g := ![![![-5, -5, 0, 1, 6], ![5, 7, -2, 0, -4], ![-228, -114, -7, 40, 268], ![962, 513, 45, -181, -1152], ![-179, -95, -9, 34, 215]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![433, 236, 29, -87, -510]] ![![1, -5, 0, 1, 6]]
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


lemma PB953I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB953I0 : PrimesBelowBoundCertificateInterval O 1 23 953 where
  m := 9
  g := ![5, 5, 5, 1, 2, 3, 2, 3, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB953I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N0, I2N0, I2N1, I2N2]
    · exact ![I3N0, I3N0, I3N1, I3N1, I3N1]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1, I13N2]
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
    · exact ![16807]
    · exact ![1331, 121]
    · exact ![169, 169, 13]
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
      exact NI2N0
      exact NI2N0
      exact NI2N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
      exact NI13N2
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
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I5N0, I11N1, I13N0, I13N1, I13N2, I17N1, I19N1, I19N2, I23N1]
  Il := ![[I2N0, I2N0, I2N0, I2N1, I2N2], [I3N0, I3N0, I3N1, I3N1, I3N1], [I5N0, I5N0, I5N0, I5N0, I5N0], [], [I11N1], [I13N0, I13N1, I13N2], [I17N1], [I19N1, I19N2], [I23N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
