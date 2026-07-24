
import IdealArithmetic.Examples.NF5_3_729000000_4.RI5_3_729000000_4
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7711433, -38123655, 19013323, 18232719, -33445971]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![-7711433, -38123655, 19013323, 18232719, -33445971]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-7711433, -38123655, 19013323, 18232719, -33445971], ![57833541, 262991719, -128506646, -107835106, 203463459], ![-370306659, -1616675472, 781495709, 605667556, -1163798331], ![1277646489, 5462369556, -2625340404, -1944008293, 3776615679], ![52272358, 242283519, -118964581, -103241463, 193364228]]]
  hmulB := by decide  
  f := ![![![-319756185355, 9159947631, 36176928125, 9404636087, -30891537294]], ![![49014934974, -1403962658, -5545470383, -1441616223, 4735252515]], ![![-15026565237, 431198286, 1700264297, 441989018, -1452021747]], ![![9817369932, -279690987, -1110367911, -288686284, 947802975]], ![![-182076487279, 5216971674, 20600224572, 5355258066, -17590805977]]]
  g := ![![![12867269, -38123655, 19013323, 18232719, -33445971], ![-72814959, 262991719, -128506646, -107835106, 203463459], ![396745836, -1616675472, 781495709, 605667556, -1163798331], ![-1249484595, 5462369556, -2625340404, -1944008293, 3776615679], ![-70545935, 242283519, -118964581, -103241463, 193364228]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![24633234035, -705635608, -2786976329, -724509185, 2379798192]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![24633234035, -705635608, -2786976329, -724509185, 2379798192]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![24633234035, -705635608, -2786976329, -724509185, 2379798192], ![-7551935850, 216440204, 854443173, 222120822, -729633096], ![2315440548, -65793000, -261841555, -68080230, 223468056], ![-1512149724, 44435445, 171344190, 44519480, -146558592], ![3420545964, -97195400, -386812603, -100573363, 330124511]]]
  hmulB := by decide  
  f := ![![![114940, 312575, -126323, 50596, -29760]], ![![-77388, 23228, -58662, -328707, 502992]], ![![-542718, -3657921, 1936808, 2512332, -4368024]], ![![3711893, 18800551, -9429118, -9343388, 17029032]], ![![-83365, -62250, -9966, -244056, 361775]]]
  g := ![![![11488972514, -705635608, -2786976329, -724509185, 2379798192], ![-3522211788, 216440204, 854443173, 222120822, -729633096], ![1080026361, -65793000, -261841555, -68080230, 223468056], ![-705055306, 44435445, 171344190, 44519480, -146558592], ![1595497408, -97195400, -386812603, -100573363, 330124511]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2, -68, 41, 78, -129]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![-2, -68, 41, 78, -129]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-2, -68, 41, 78, -129], ![177, 973, -495, -542, 969], ![-1593, -7542, 3730, 3346, -6225], ![6321, 28380, -13809, -11327, 21477], ![132, 800, -407, -498, 871]]]
  hmulB := by decide  
  f := ![![![390071, -11156, -44128, -11472, 37677]], ![![135259, -3819, -15290, -3976, 13044]], ![![213448, -5866, -24091, -6268, 20517]], ![![183229, -4744, -20612, -5369, 17490]], ![![222235, -6006, -25059, -6522, 21319]]]
  g := ![![![38, -68, 41, 78, -129], ![-364, 973, -495, -542, 969], ![2549, -7542, 3730, 3346, -6225], ![-9200, 28380, -13809, -11327, 21477], ![-317, 800, -407, -498, 871]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![-7711433, -38123655, 19013323, 18232719, -33445971]] ![![24633234035, -705635608, -2786976329, -724509185, 2379798192]]
  ![![-1, -1, 0, -2, 3]] where
 M := ![![![-1, -1, 0, -2, 3]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![-1, -1, 0, -2, 3]] ![![24633234035, -705635608, -2786976329, -724509185, 2379798192]]
  ![![-3795360845, 108738314, 429406967, 111629314, -366674379]] where
 M := ![![![-3795360845, 108738314, 429406967, 111629314, -366674379]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![-3795360845, 108738314, 429406967, 111629314, -366674379]] ![![-2, -68, 41, 78, -129]]
  ![![-19397, -12, 2062, 548, -1635]] where
 M := ![![![-19397, -12, 2062, 548, -1635]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![-19397, -12, 2062, 548, -1635]] ![![-2, -68, 41, 78, -129]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![-8, -44, 36, 24, -54]]]
 hmul := by decide  
 g := ![![![![-4, -22, 18, 12, -27]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-111, -331, -75, -12, 114]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![-111, -331, -75, -12, 114]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-111, -331, -75, -12, 114], ![-498, -1485, -334, -54, 510], ![-2226, -6642, -1495, -236, 2274], ![-3864, -11511, -2613, -433, 3990], ![-2782, -8297, -1869, -300, 2849]]]
  hmulB := by decide  
  f := ![![![-465, -79, 31, 10, -6]], ![![-10, -159, -36, -6, 66]], ![![-294, -814, -159, -24, 318]], ![![-576, -1699, -335, -51, 666]], ![![-589, -1228, -224, -32, 467]]]
  g := ![![![-75, -331, -75, -12, 114], ![-336, -1485, -334, -54, 510], ![-1500, -6642, -1495, -236, 2274], ![-2618, -11511, -2613, -433, 3990], ![-1877, -8297, -1869, -300, 2849]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4061367130, -116204006, -459466602, -119446940, 392308127]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![4061367130, -116204006, -459466602, -119446940, 392308127]] 
 ![![3, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![4061367130, -116204006, -459466602, -119446940, 392308127], ![-1244858995, 36383939, 141011032, 36642316, -120569671], ![382994459, -7234116, -42458925, -11116464, 35427887], ![-246717555, 14857110, 29732334, 7565163, -27113907], ![565786529, -10693318, -62724864, -16422288, 52339348]]]
  hmulB := by decide  
  f := ![![![-1414314, -5512938, 2578212, 1478992, -3077715]], ![![1228665, 4753059, -2217418, -1239176, 2598791]], ![![-10844857, -41935028, 19561957, 10914908, -22901699]], ![![27288973, 105023046, -48916608, -26836961, 56597293]], ![![1763997, 6850356, -3199570, -1812348, 3785469]]]
  g := ![![![1606800073, -116204006, -459466602, -119446940, 392308127], ![-493026422, 36383939, 141011032, 36642316, -120569671], ![148984218, -7234116, -42458925, -11116464, 35427887], ![-102927512, 14857110, 29732334, 7565163, -27113907], ![220094515, -10693318, -62724864, -16422288, 52339348]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![-111, -331, -75, -12, 114]] ![![-111, -331, -75, -12, 114]]
  ![![73329, 218700, 49294, 7902, -75108]] where
 M := ![![![73329, 218700, 49294, 7902, -75108]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![73329, 218700, 49294, 7902, -75108]] ![![4061367130, -116204006, -459466602, -119446940, 392308127]]
  ![![191474, 786, -20028, -5346, 16163]] where
 M := ![![![191474, 786, -20028, -5346, 16163]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![191474, 786, -20028, -5346, 16163]] ![![4061367130, -116204006, -459466602, -119446940, 392308127]]
  ![![779460897371955, -22328825402436, -88187477164692, -22925418790534, 75303400655502]] where
 M := ![![![779460897371955, -22328825402436, -88187477164692, -22925418790534, 75303400655502]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N3 : IdealMulLeCertificate' Table 
  ![![779460897371955, -22328825402436, -88187477164692, -22925418790534, 75303400655502]] ![![4061367130, -116204006, -459466602, -119446940, 392308127]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![3207959544699626710866270, -91896779655260913827238, -362945536915257246072846, -94352154664824528156006, 309919656440027589580071]]]
 hmul := by decide  
 g := ![![![![1069319848233208903622090, -30632259885086971275746, -120981845638419082024282, -31450718221608176052002, 103306552146675863193357]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-86976, 2187, 9769, 2546, -8275]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![-86976, 2187, 9769, 2546, -8275]] 
 ![![5, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-86976, 2187, 9769, 2546, -8275], ![26099, -2315, -3320, -830, 3179], ![-10915, -7758, -655, 0, 2333], ![-375, -16743, -3879, -655, 6999], ![-16105, -11403, -955, 2, 3426]]]
  hmulB := by decide  
  f := ![![![-7736, -31419, 14879, 9684, -19447]], ![![6279, 25300, -11953, -7606, 15368]], ![![-45219, -181770, 85815, 54232, -109783]], ![![114077, 455802, -214796, -133333, 271252]], ![![6281, 25368, -11994, -7684, 15497]]]
  g := ![![![-24502, 2187, 9769, 2546, -8275], ![7869, -2315, -3320, -830, 3179], ![-574, -7758, -655, 0, 2333], ![5108, -16743, -3879, -655, 6999], ![-862, -11403, -955, 2, 3426]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![-86976, 2187, 9769, 2546, -8275]] ![![-86976, 2187, 9769, 2546, -8275]]
  ![![7647588579, -219335172, -865301388, -224940286, 738939254]] where
 M := ![![![7647588579, -219335172, -865301388, -224940286, 738939254]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![7647588579, -219335172, -865301388, -224940286, 738939254]] ![![-86976, 2187, 9769, 2546, -8275]]
  ![![-673252592329532, 19286096208693, 76171114390255, 19801622480732, -65042561318727]] where
 M := ![![![-673252592329532, 19286096208693, 76171114390255, 19801622480732, -65042561318727]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![-673252592329532, 19286096208693, 76171114390255, 19801622480732, -65042561318727]] ![![-86976, 2187, 9769, 2546, -8275]]
  ![![59268842423442244349, -1697844476064860964, -6705621341349051036, -1743208707771720576, 5725938651911461828]] where
 M := ![![![59268842423442244349, -1697844476064860964, -6705621341349051036, -1743208707771720576, 5725938651911461828]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![59268842423442244349, -1697844476064860964, -6705621341349051036, -1743208707771720576, 5725938651911461828]] ![![-86976, 2187, 9769, 2546, -8275]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![-5217649563384924256264060, 149467343654819797839495, 590319982438597309943005, 153460937306112088613610, -504074985157007705148215]]]
 hmul := by decide  
 g := ![![![![-1043529912676984851252812, 29893468730963959567899, 118063996487719461988601, 30692187461222417722722, -100814997031401541029643]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-526, -2036, 950, 532, -1115]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![-526, -2036, 950, 532, -1115]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![1, 6, 2, 1, 0], ![4, 3, 1, 0, 1]] where
  M :=![![![-526, -2036, 950, 532, -1115], ![2383, 9181, -4278, -2356, 4963], ![-10679, -40932, 19039, 10292, -21803], ![28971, 110532, -51342, -27275, 58095], ![2465, 9512, -4436, -2456, 5166]]]
  hmulB := by decide  
  f := ![![![-3930, 32, 424, 112, -349]], ![![1073, -401, -216, -48, 245]], ![![-937, -1680, -329, -48, 563]], ![![-23, -1258, -318, -55, 480]], ![![-2103, -705, 43, 28, 90]]]
  g := ![![![486, -269, 143, 532, -1115], ![-2159, 1204, -647, -2356, 4963], ![9463, -5325, 2894, 10292, -21803], ![-25162, 14271, -7841, -27275, 58095], ![-2249, 1250, -670, -2456, 5166]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 3 2 2 [4, 3, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 2], [3, 4], [0, 1]]
 g := ![![[5, 5, 2], [1]], ![[5, 4, 1], [1]], ![[3, 5, 4], [1]]]
 h' := ![![[1, 2], [3, 4, 4], [0, 1]], ![[3, 4], [4, 3, 2], [1, 2]], ![[0, 1], [2, 0, 1], [3, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5], []]
 b := ![[], [2, 4, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 3
  hpos := by decide
  P := [4, 3, 3, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1594166321, 3972811998, 2115442180, 813974237, -3781429092]
  a := ![47, 70, 42, 53, -188]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2272272636, 1490464836, 609846114, 813974237, -3781429092]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 343 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3930, -32, -424, -112, 349]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![3930, -32, -424, -112, 349]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![1, 4, 1, 0, 0], ![1, 1, 0, 1, 0], ![0, 2, 0, 0, 1]] where
  M :=![![![3930, -32, -424, -112, 349], ![-1073, 401, 216, 48, -245], ![937, 1680, 329, 48, -563], ![795, 3072, 696, 113, -1113], ![1283, 2180, 418, 60, -728]]]
  hmulB := by decide  
  f := ![![![526, 2036, -950, -532, 1115]], ![![-2383, -9181, 4278, 2356, -4963]], ![![239, 892, -411, -200, 438]], ![![-4404, -16811, 7810, 4157, -8849]], ![![-1033, -3982, 1856, 1024, -2156]]]
  g := ![![![638, 154, -424, -112, 349], ![-191, -3, 216, 48, -245], ![80, 206, 329, 48, -563], ![-2, 343, 696, 113, -1113], ![115, 272, 418, 60, -728]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P1 : CertificateIrreducibleZModOfList' 7 2 2 2 [1, 4, 1] where
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

def PI7N1 : CertifiedPrimeIdeal' SI7N1 7 where
  n := 2
  hpos := by decide
  P := [1, 4, 1]
  hirr := P7P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-54370658, -122244397, -82347345, -38726873, 160285884]
  a := ![562, 811, 499, 623, -2245]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![9529080, -10671416, -82347345, -38726873, 160285884]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N1 B_one_repr
lemma NI7N1 : Nat.card (O ⧸ I7N1) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![-526, -2036, 950, 532, -1115]] ![![3930, -32, -424, -112, 349]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5560476, -18677044, 8294276, 2035364, -5906209]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-5560476, -18677044, 8294276, 2035364, -5906209]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![9, 1, 10, 10, 1]] where
  M :=![![![-5560476, -18677044, 8294276, 2035364, -5906209], ![17318861, 52901965, -22594952, 305640, 7505273], ![-39360205, -83000448, 28473173, -47635024, 59872271], ![12904497, -152992032, 101404848, 242830781, -392003475], ![20525597, 65232880, -28336790, -2834896, 14134602]]]
  hmulB := by decide  
  f := ![![![-9827341076, 281474240, 1111845750, 289038912, -949396627]], ![![3012749663, -86535133, -340913482, -88619796, 291157499]], ![![-924068719, 25280340, 104270161, 27131404, -88772611]], ![![602571675, -19743876, -68754042, -17821157, 59259015]], ![![-8183035900, 230858709, 924990522, 240537594, -789062784]]]
  g := ![![![4326855, -1160985, 6123306, 5554314, -5906209], ![-4566236, 4126972, -8877062, -6795190, 7505273], ![-52564604, -12988429, -51840867, -58759794, 59872271], ![321903252, 21728313, 365585418, 378442321, -392003475], ![-9698711, 4645298, -15425710, -13107356, 14134602]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 4 2 3 [10, 1, 4, 4, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 9, 5, 2], [2, 3, 3, 3], [3, 9, 3, 6], [0, 1]]
 g := ![![[2, 6, 4, 1], [7, 1], []], ![[6, 0, 1, 10, 9, 6], [8, 3, 0, 6, 5, 6], [7, 4, 4]], ![[1, 2, 3, 0, 5, 5], [8, 2, 5, 3, 10, 9], [8, 4, 9]], ![[7, 4, 1, 8, 0, 8], [3, 1, 0, 6, 3, 6], [9, 2, 3]]]
 h' := ![![[2, 9, 5, 2], [7, 5, 4, 1], [0, 0, 1], [0, 1]], ![[2, 3, 3, 3], [8, 6, 9, 6], [0, 0, 7, 6], [2, 9, 5, 2]], ![[3, 9, 3, 6], [10, 7, 5, 8], [1, 8, 5, 6], [2, 3, 3, 3]], ![[0, 1], [7, 4, 4, 7], [7, 3, 9, 10], [3, 9, 3, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [7, 3, 6], []]
 b := ![[], [], [4, 5, 4, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 4
  hpos := by decide
  P := [10, 1, 4, 4, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5207582957041, -14074903286118, -5063779462716, -1537220844166, 9176209268629]
  a := ![45, 66, 40, 50, -179]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7981224215882, -2113737504977, -8802352013546, -8481755775496, 9176209268629]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 14641 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9827341076, -281474240, -1111845750, -289038912, 949396627]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![9827341076, -281474240, -1111845750, -289038912, 949396627]] 
 ![![11, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  M :=![![![9827341076, -281474240, -1111845750, -289038912, 949396627], ![-3012749663, 86535133, 340913482, 88619796, -291157499], ![924068719, -25280340, -104270161, -27131404, 88772611], ![-602571675, 19743876, 68754042, 17821157, -59259015], ![1365104439, -37348132, -154036284, -40080652, 131142520]]]
  hmulB := by decide  
  f := ![![![5560476, 18677044, -8294276, -2035364, 5906209]], ![![1458545, 5378209, -2470064, -1137984, 2539271]], ![![7622183, 21128800, -8620671, 2850192, -1147509]], ![![1354353, 22397932, -12988748, -23000691, 38321320]], ![![2683517, 9350956, -4210154, -1407580, 3547389]]]
  g := ![![![1210143403, -281474240, -1111845750, -289038912, 949396627], ![-371086346, 86535133, 340913482, 88619796, -291157499], ![113328688, -25280340, -104270161, -27131404, 88772611], ![-75167447, 19743876, 68754042, 17821157, -59259015], ![167418553, -37348132, -154036284, -40080652, 131142520]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-5560476, -18677044, 8294276, 2035364, -5906209]] ![![9827341076, -281474240, -1111845750, -289038912, 949396627]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19, -71, 29, 16, -32]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-19, -71, 29, 16, -32]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![6, 8, 2, 1, 0], ![4, 5, 7, 0, 1]] where
  M :=![![![-19, -71, 29, 16, -32], ![64, 253, -138, -70, 160], ![-380, -1386, 535, 284, -560], ![738, 2865, -1545, -743, 1728], ![-4, 59, -185, -80, 249]]]
  hmulB := by decide  
  f := ![![![225, 95, 1, -2, -16]], ![![92, 451, 108, 18, -160]], ![![692, 2010, 451, 72, -688]], ![![356, 899, 197, 31, -304]], ![![544, 1478, 328, 52, -503]]]
  g := ![![![1, -3, 17, 16, -32], ![-12, 1, -86, -70, 160], ![12, -66, 299, 284, -560], ![-132, 13, -935, -743, 1728], ![-40, -42, -136, -80, 249]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [6, 11, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 8, 2], [3, 4, 11], [0, 1]]
 g := ![![[3, 9, 9], [10, 4], [1]], ![[2, 3, 10, 11], [10, 3], [5, 11, 2, 8]], ![[0, 2, 0, 5], [6, 10], [10, 4, 12, 5]]]
 h' := ![![[8, 8, 2], [2, 11, 3], [7, 2, 11], [0, 1]], ![[3, 4, 11], [6, 11, 8], [1, 11, 9], [8, 8, 2]], ![[0, 1], [0, 4, 2], [6, 0, 6], [3, 4, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 9], []]
 b := ![[], [5, 10, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [6, 11, 2, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-145689937861, -366525248028, -186148263246, -70426394644, 334851415365]
  a := ![-209, -304, -187, -235, 837]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-81733633189, -113643935977, -183788875501, -70426394644, 334851415365]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 2197 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-362, -208, -10, 2, 57]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![-362, -208, -10, 2, 57]] 
 ![![13, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![-362, -208, -10, 2, 57], ![-297, -1121, -230, -36, 447], ![-2019, -5784, -1135, -172, 2265], ![-4137, -12066, -2376, -361, 4731], ![-2981, -8540, -1676, -254, 3344]]]
  hmulB := by decide  
  f := ![![![-2, 40, -24, -58, 93]], ![![-9, -53, 28, 32, -57]], ![![93, 444, -217, -200, 369]], ![![-369, -1674, 822, 683, -1293]], ![![-5, -28, 18, 16, -31]]]
  g := ![![![-41, -208, -10, 2, 57], ![-126, -1121, -230, -36, 447], ![-678, -5784, -1135, -172, 2265], ![-1410, -12066, -2376, -361, 4731], ![-1001, -8540, -1676, -254, 3344]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1

def I13N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![57, 170, 38, 6, -58]] i)))

def SI13N2: IdealEqSpanCertificate' Table ![![57, 170, 38, 6, -58]] 
 ![![13, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![57, 170, 38, 6, -58], ![254, 757, 172, 28, -262], ![1142, 3408, 761, 120, -1162], ![1974, 5880, 1344, 221, -2046], ![1424, 4246, 958, 154, -1461]]]
  hmulB := by decide  
  f := ![![![401, -14, -42, -10, 34]], ![![300, -7, -32, -8, 26]], ![![126, -8, -7, 0, 2]], ![![134, 40, -24, -11, 22]], ![![70, 10, -6, -2, 3]]]
  g := ![![![-131, 170, 38, 6, -58], ![-584, 757, 172, 28, -262], ![-2626, 3408, 761, 120, -1162], ![-4538, 5880, 1344, 221, -2046], ![-3274, 4246, 958, 154, -1461]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N2 : Nat.card (O ⧸ I13N2) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N2)

lemma isPrimeI13N2 : Ideal.IsPrime I13N2 := prime_ideal_of_norm_prime hp13.out _ NI13N2
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-19, -71, 29, 16, -32]] ![![-362, -208, -10, 2, 57]]
  ![![-1386, -3969, -779, -118, 1553]] where
 M := ![![![-1386, -3969, -779, -118, 1553]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI13N1 : IdealMulLeCertificate' Table 
  ![![-1386, -3969, -779, -118, 1553]] ![![57, 170, 38, 6, -58]]
  ![![13, 0, 0, 0, 0]] where
 M := ![![![1794, 5213, 1027, 156, -2041]]]
 hmul := by decide  
 g := ![![![![138, 401, 79, 12, -157]]]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-134968334, 3863042, 15269414, 3969542, -13037835]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![-134968334, 3863042, 15269414, 3969542, -13037835]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![2, 16, 1, 0, 0], ![0, 1, 0, 1, 0], ![3, 4, 0, 0, 1]] where
  M :=![![![-134968334, 3863042, 15269414, 3969542, -13037835], ![41371923, -1202357, -4684796, -1217508, 4004163], ![-12715767, 275376, 1417895, 370472, -1191051], ![8224095, -420864, -973728, -249229, 872511], ![-18784655, 406954, 2094652, 547294, -1759570]]]
  hmulB := by decide  
  f := ![![![-233782, -933106, 439584, 272002, -553851]], ![![1137243, 4518263, -2125534, -1296848, 2651091]], ![![720821, 2868864, -1350327, -828344, 1690767]], ![![995298, 3925627, -1842608, -1098809, 2260914]], ![![294037, 1167828, -549326, -334824, 684659]]]
  g := ![![![-7434921, -11309752, 15269414, 3969542, -13037835], ![2278178, 3467955, -4684796, -1217508, 4004163], ![-704612, -1059836, 1417895, 370472, -1191051], ![444354, 701057, -973728, -249229, 872511], ![-1040897, -1565676, 2094652, 547294, -1759570]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [3, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 16], [0, 1]]
 g := ![![[15, 9], [15], [2], [1]], ![[1, 8], [15], [2], [1]]]
 h' := ![![[6, 16], [15, 14], [3, 10], [14, 6], [0, 1]], ![[0, 1], [14, 3], [12, 7], [16, 11], [6, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [13, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 2
  hpos := by decide
  P := [3, 11, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-173436, -285951, -447751, -241200, 814161]
  a := ![40, 60, 38, 49, -161]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-101201, 227213, -447751, -241200, 814161]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17212, 488, 1946, 506, -1661]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![-17212, 488, 1946, 506, -1661]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![7, 2, 1, 0, 0], ![15, 9, 0, 1, 0], ![6, 3, 0, 0, 1]] where
  M :=![![![-17212, 488, 1946, 506, -1661], ![5269, -173, -602, -156, 517], ![-1649, -48, 161, 44, -125], ![1005, -186, -156, -37, 153], ![-2427, -44, 244, 66, -194]]]
  hmulB := by decide  
  f := ![![![12, 32, -12, 6, -5]], ![![-11, 23, -16, -72, 109]], ![![-3, -30, 19, 26, -46]], ![![54, 285, -138, -151, 267]], ![![2, 17, -6, -14, 21]]]
  g := ![![![-1674, -175, 1946, 506, -1661], ![513, 52, -602, -156, 517], ![-158, -23, 161, 44, -125], ![102, 0, -156, -37, 153], ![-233, -32, 244, 66, -194]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P1 : CertificateIrreducibleZModOfList' 17 2 2 4 [16, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 16], [0, 1]]
 g := ![![[16, 16], [9], [1], [1]], ![[0, 1], [9], [1], [1]]]
 h' := ![![[16, 16], [13, 13], [2, 14], [1, 16], [0, 1]], ![[0, 1], [0, 4], [5, 3], [2, 1], [16, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [10, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N1 : CertifiedPrimeIdeal' SI17N1 17 where
  n := 2
  hpos := by decide
  P := [16, 1, 1]
  hirr := P17P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-176540, -487566, -101990, -22702, 254032]
  a := ![20, 30, 14, 14, -80]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-38016, -49492, -101990, -22702, 254032]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N1 B_one_repr
lemma NI17N1 : Nat.card (O ⧸ I17N1) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N1

def I17N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11071807, -43744618, 20543818, 12318472, -25306706]] i)))

def SI17N2: IdealEqSpanCertificate' Table ![![-11071807, -43744618, 20543818, 12318472, -25306706]] 
 ![![17, 0, 0, 0, 0], ![16, 1, 0, 0, 0], ![16, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![14, 0, 0, 0, 1]] where
  M :=![![![-11071807, -43744618, 20543818, 12318472, -25306706], ![52622698, 207049123, -97111632, -57460140, 118496386], ![-247721090, -970689060, 454698331, 265457856, -549568658], ![701408622, 2739119910, -1281718098, -739862021, 1536788298], ![53639438, 211321594, -99155110, -58913312, 121347969]]]
  hmulB := by decide  
  f := ![![![-2353882284675, 67430455202, 266316033886, 69232127504, -227407598654]], ![![-2172968901562, 62247919619, 245847662720, 63911122812, -209929629938]], ![![-2228432716990, 63836751652, 252122784123, 65542418016, -215287961534]], ![![8501943378, -243580758, -961908894, -250059413, 821381862]], ![![-1957716713744, 56081682730, 221494227842, 57580148360, -189134197023]]]
  g := ![![![42025581, -43744618, 20543818, 12318472, -25306706], ![-197960386, 207049123, -97111632, -57460140, 118496386], ![923652458, -970689060, 454698331, 265457856, -549568658], ![-2596003326, 2739119910, -1281718098, -739862021, 1536788298], ![-202346816, 211321594, -99155110, -58913312, 121347969]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N2 : Nat.card (O ⧸ I17N2) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N2)

lemma isPrimeI17N2 : Ideal.IsPrime I17N2 := prime_ideal_of_norm_prime hp17.out _ NI17N2
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![-134968334, 3863042, 15269414, 3969542, -13037835]] ![![-17212, 488, 1946, 506, -1661]]
  ![![2353882284675, -67430455202, -266316033886, -69232127504, 227407598654]] where
 M := ![![![2353882284675, -67430455202, -266316033886, -69232127504, 227407598654]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI17N1 : IdealMulLeCertificate' Table 
  ![![2353882284675, -67430455202, -266316033886, -69232127504, 227407598654]] ![![-11071807, -43744618, 20543818, 12318472, -25306706]]
  ![![17, 0, 0, 0, 0]] where
 M := ![![![-17, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19, -65, 13, 10, -12]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-19, -65, 13, 10, -12]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 7, 10, 15, 1]] where
  M :=![![![-19, -65, 13, 10, -12], ![0, 47, -112, -54, 156], ![-456, -1542, 259, 208, -204], ![114, 933, -1395, -677, 1884], ![-304, -835, -289, -82, 505]]]
  hmulB := by decide  
  f := ![![![-145, -1, 15, 4, -12]], ![![36, -25, -10, -2, 12]], ![![-48, -102, -23, -4, 36]], ![![-54, -189, -39, -5, 60]], ![![-58, -219, -48, -7, 73]]]
  g := ![![![-1, 1, 7, 10, -12], ![0, -55, -88, -126, 156], ![-24, -6, 121, 172, -204], ![6, -645, -1065, -1523, 1884], ![-16, -230, -281, -403, 505]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 4 2 4 [12, 11, 10, 5, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 9, 18, 6], [17, 8, 0, 16], [7, 1, 1, 16], [0, 1]]
 g := ![![[4, 15, 9, 4], [4, 9, 13, 6], [1], []], ![[9, 0, 15, 18, 11, 17], [16, 14, 11, 1, 13, 9], [18, 4, 11], [6, 17, 17]], ![[11, 10, 15, 1, 16, 17], [9, 13, 11, 6, 10, 1], [14, 7, 16], [11, 12, 9]], ![[8, 7, 6, 18, 14, 1], [14, 16, 5, 15, 0, 11], [5, 17, 7], [8, 6, 9]]]
 h' := ![![[9, 9, 18, 6], [9, 11, 7, 17], [7, 8, 9, 14], [0, 0, 1], [0, 1]], ![[17, 8, 0, 16], [15, 5, 15, 5], [17, 14, 11, 7], [9, 6, 11, 7], [9, 9, 18, 6]], ![[7, 1, 1, 16], [15, 0, 12, 11], [9, 3, 10, 14], [5, 7, 18, 4], [17, 8, 0, 16]], ![[0, 1], [12, 3, 4, 5], [2, 13, 8, 3], [10, 6, 8, 8], [7, 1, 1, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [16, 10, 14], []]
 b := ![[], [], [10, 12, 14, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 4
  hpos := by decide
  P := [12, 11, 10, 5, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-337643010288, 358246332341, -3149407384901, -1544928157439, 4671447689004]
  a := ![43, 64, 40, 51, -159]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-17770684752, -1702204604773, -2624414961839, -3769297025921, 4671447689004]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 130321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-145, -1, 15, 4, -12]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![-145, -1, 15, 4, -12]] 
 ![![19, 0, 0, 0, 0], ![13, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![12, 0, 0, 0, 1]] where
  M :=![![![-145, -1, 15, 4, -12], ![36, -25, -10, -2, 12], ![-48, -102, -23, -4, 36], ![-54, -189, -39, -5, 60], ![-64, -131, -27, -4, 43]]]
  hmulB := by decide  
  f := ![![![-19, -65, 13, 10, -12]], ![![-13, -42, 3, 4, 0]], ![![-26, -88, 15, 12, -12]], ![![1, 32, -70, -33, 96]], ![![-28, -85, -7, 2, 19]]]
  g := ![![![-2, -1, 15, 4, -12], ![13, -25, -10, -2, 12], ![48, -102, -23, -4, 36], ![94, -189, -39, -5, 60], ![63, -131, -27, -4, 43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-19, -65, 13, 10, -12]] ![![-145, -1, 15, 4, -12]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11289274, 326555, 1277995, 332164, -1091981]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![-11289274, 326555, 1277995, 332164, -1091981]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![9, 1, 3, 1, 0], ![12, 2, 4, 0, 1]] where
  M :=![![![-11289274, 326555, 1277995, 332164, -1091981], ![3466921, -82997, -388434, -101322, 328069], ![-1032413, 113922, 136501, 33708, -135245], ![753195, 154239, -44163, -15185, -1239], ![-1525207, 168157, 201623, 49792, -199740]]]
  hmulB := by decide  
  f := ![![![-13014, -52813, 25003, 16238, -32627]], ![![65707, 264995, -125238, -79898, 161323]], ![![-327227, -1312410, 619145, 388708, -788291]], ![![-2821, -12185, 5865, 4449, -8590]], ![![-55127, -221207, 104369, 65622, -133024]]]
  g := ![![![-51086, 94711, 202149, 332164, -1091981], ![19217, -27731, -60728, -101322, 328069], ![12485, 15248, 25059, 33708, -135245], ![39336, 7474, 276, -15185, -1239], ![18415, 22515, 37009, 49792, -199740]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [17, 18, 17, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 9, 11], [22, 13, 12], [0, 1]]
 g := ![![[5, 16, 18], [5, 3, 13], [18, 6, 1], []], ![[22, 18, 21, 20], [18, 5, 22, 14], [20, 4, 5, 19], [4, 6]], ![[12, 21, 8, 16], [13, 9, 6, 2], [11, 10, 3, 6], [3, 6]]]
 h' := ![![[7, 9, 11], [7, 0, 15], [16, 11, 6], [0, 0, 1], [0, 1]], ![[22, 13, 12], [21, 16, 11], [2, 18, 15], [4, 21, 13], [7, 9, 11]], ![[0, 1], [16, 7, 20], [4, 17, 2], [19, 2, 9], [22, 13, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 16], []]
 b := ![[], [11, 8, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [17, 18, 17, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![66686899, 184806315, 49768093, 12856650, -100237756]
  a := ![13, 18, 11, 13, -53]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![50166527, 16192399, 17919529, 12856650, -100237756]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 12167 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13014, 52813, -25003, -16238, 32627]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![13014, 52813, -25003, -16238, 32627]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![1, 18, 1, 0, 0], ![2, 2, 0, 1, 0], ![14, 12, 0, 0, 1]] where
  M :=![![![13014, 52813, -25003, -16238, 32627], ![-65707, -264995, 125238, 79898, -161323], ![327227, 1312410, -619145, -388708, 788291], ![-968217, -3867297, 1822329, 1130041, -2299623], ![-65741, -265645, 125653, 80586, -162490]]]
  hmulB := by decide  
  f := ![![![11289274, -326555, -1277995, -332164, 1091981]], ![![-3466921, 82997, 388434, 101322, -328069]], ![![-2177517, 45803, 242492, 63388, -203392]], ![![647457, -27885, -75433, -19413, 66481]], ![![5129217, -162781, -584015, -151488, 502202]]]
  g := ![![![-16795, 6253, -25003, -16238, 32627], ![82947, -32313, 125238, 79898, -161323], ![-404882, 164128, -619145, -388708, 788291], ![1180178, -492775, 1822329, 1130041, -2299623], ![83578, -32117, 125653, 80586, -162490]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P1 : CertificateIrreducibleZModOfList' 23 2 2 4 [4, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 22], [0, 1]]
 g := ![![[4, 6], [21, 6], [11, 3], [1]], ![[0, 17], [17, 17], [9, 20], [1]]]
 h' := ![![[7, 22], [8, 12], [2, 12], [19, 7], [0, 1]], ![[0, 1], [0, 11], [17, 11], [22, 16], [7, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [3, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N1 : CertifiedPrimeIdeal' SI23N1 23 where
  n := 2
  hpos := by decide
  P := [4, 16, 1]
  hirr := P23P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-137217, -254457, -300540, -158193, 559994]
  a := ![-32, -48, -29, -39, 131]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-320009, -54273, -300540, -158193, 559994]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N1 B_one_repr
lemma NI23N1 : Nat.card (O ⧸ I23N1) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![-11289274, 326555, 1277995, 332164, -1091981]] ![![13014, 52813, -25003, -16238, 32627]]
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


lemma PB1321I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB1321I0 : PrimesBelowBoundCertificateInterval O 1 23 1321 where
  m := 9
  g := ![5, 5, 5, 2, 2, 3, 3, 2, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB1321I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N0, I3N1, I3N1, I3N1]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1, I13N2]
    · exact ![I17N0, I17N1, I17N2]
    · exact ![I19N0, I19N1]
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
    · exact ![343, 49]
    · exact ![14641, 11]
    · exact ![2197, 13, 13]
    · exact ![289, 289, 17]
    · exact ![130321, 19]
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
      exact NI17N2
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I5N0, I7N0, I7N1, I11N1, I13N1, I13N2, I17N0, I17N1, I17N2, I19N1, I23N1]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N0, I3N1, I3N1, I3N1], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N0, I7N1], [I11N1], [I13N1, I13N2], [I17N0, I17N1, I17N2], [I19N1], [I23N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
