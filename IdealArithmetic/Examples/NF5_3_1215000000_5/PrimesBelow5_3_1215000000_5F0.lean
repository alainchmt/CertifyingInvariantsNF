
import IdealArithmetic.Examples.NF5_3_1215000000_5.RI5_3_1215000000_5
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-179, -59, 52, 19, 78]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![-179, -59, 52, 19, 78]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-179, -59, 52, 19, 78], ![-582, -192, 169, 62, 254], ![-1896, -623, 552, 202, 832], ![-2811, -927, 816, 295, 1215], ![975, 320, -284, -103, -426]]]
  hmulB := by decide  
  f := ![![![-289, 136, -35, -8, -63]], ![![213, -88, 20, 4, 37]], ![![-246, 137, -40, -10, -70]], ![![-11, 44, -19, -6, -30]], ![![-39, 4, 2, 1, 2]]]
  g := ![![![-99, -59, 52, 19, 78], ![-322, -192, 169, 62, 254], ![-1049, -623, 552, 202, 832], ![-1553, -927, 816, 295, 1215], ![539, 320, -284, -103, -426]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![39230, -18189, 4643, 1051, 8372]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![39230, -18189, 4643, 1051, 8372]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![39230, -18189, 4643, 1051, 8372], ![-56538, 24048, -5577, -1152, -10294], ![68676, -35915, 10224, 2522, 17988], ![-33261, 7843, -37, 378, -899], ![9183, -1648, -256, -191, -175]]]
  hmulB := by decide  
  f := ![![![145, 34, -50, -19, -105]], ![![372, 134, -97, -2, -46]], ![![288, 433, 110, -114, 200]], ![![-444, -1009, -419, -431, -2743]], ![![437, 115, -127, 148, 327]]]
  g := ![![![15429, -18189, 4643, 1051, 8372], ![-23122, 24048, -5577, -1152, -10294], ![25344, -35915, 10224, 2522, 17988], ![-16181, 7843, -37, 378, -899], ![4679, -1648, -256, -191, -175]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8096, 2879, -2194, -805, -3365]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![8096, 2879, -2194, -805, -3365]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![8096, 2879, -2194, -805, -3365], ![25020, 8897, -6781, -2488, -10400], ![77328, 27495, -20959, -7690, -32144], ![106992, 38039, -29002, -10641, -44478], ![-39891, -14184, 10812, 3967, 16582]]]
  hmulB := by decide  
  f := ![![![4, -1, 3, 0, 6]], ![![-16, -9, 1, -3, -15]], ![![128, 14, -43, 17, -3]], ![![-22, 167, 111, 14, 353]], ![![-87, -58, 6, -17, -88]]]
  g := ![![![4108, 2879, -2194, -805, -3365], ![12696, 8897, -6781, -2488, -10400], ![39241, 27495, -20959, -7690, -32144], ![54298, 38039, -29002, -10641, -44478], ![-20243, -14184, 10812, 3967, 16582]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![-179, -59, 52, 19, 78]] ![![39230, -18189, 4643, 1051, 8372]]
  ![![-30961, -10108, 8923, 3267, 13403]] where
 M := ![![![-30961, -10108, 8923, 3267, 13403]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![-30961, -10108, 8923, 3267, 13403]] ![![39230, -18189, 4643, 1051, 8372]]
  ![![-15901916, 3137837, 297098, 283164, 70626]] where
 M := ![![![-15901916, 3137837, 297098, 283164, 70626]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![-15901916, 3137837, 297098, 283164, 70626]] ![![8096, 2879, -2194, -805, -3365]]
  ![![219704870, 73945347, -64459991, -23554478, -96923632]] where
 M := ![![![219704870, 73945347, -64459991, -23554478, -96923632]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![219704870, 73945347, -64459991, -23554478, -96923632]] ![![8096, 2879, -2194, -805, -3365]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![-9479080652, -3129371910, 2749730354, 1006039358, 4131861014]]]
 hmul := by decide  
 g := ![![![![-4739540326, -1564685955, 1374865177, 503019679, 2065930507]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![24, 7, 5, 3, 27]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![24, 7, 5, 3, 27]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![24, 7, 5, 3, 27], ![-180, -40, 43, -26, -48], ![444, -283, -352, 26, -700], ![2112, 1635, -7, 439, 2618], ![-891, -224, 280, -137, -146]]]
  hmulB := by decide  
  f := ![![![-274512, -97707, 74329, 27273, 114031]], ![![-282608, -100586, 76523, 28078, 117396]], ![![-872844, -310655, 236350, 86722, 362588]], ![![-1206626, -429437, 326743, 119889, 501256]], ![![450313, 160272, -121936, -44741, -187064]]]
  g := ![![![8, 7, 5, 3, 27], ![-60, -40, 43, -26, -48], ![148, -283, -352, 26, -700], ![704, 1635, -7, 439, 2618], ![-297, -224, 280, -137, -146]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19, -7, 5, 2, 8]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![-19, -7, 5, 2, 8]] 
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-19, -7, 5, 2, 8], ![-60, -20, 17, 6, 28], ![-204, -77, 52, 14, 60], ![-192, -95, 37, 31, 72], ![96, 44, -20, -8, -19]]]
  hmulB := by decide  
  f := ![![![927, -413, 101, 22, 184]], ![![-103, 55, -16, -4, -28]], ![![1222, -527, 124, 26, 228]], ![![-144, 97, -33, -9, -56]], ![![341, -163, 43, 10, 77]]]
  g := ![![![-10, -7, 5, 2, 8], ![-34, -20, 17, 6, 28], ![-97, -77, 52, 14, 60], ![-81, -95, 37, 31, 72], ![37, 44, -20, -8, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![24, 7, 5, 3, 27]] ![![24, 7, 5, 3, 27]]
  ![![-16185, -2670, 6200, -2362, 724]] where
 M := ![![![-16185, -2670, 6200, -2362, 724]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![-16185, -2670, 6200, -2362, 724]] ![![-19, -7, 5, 2, 8]]
  ![![-274077, -54459, 94211, -40604, -16060]] where
 M := ![![![-274077, -54459, 94211, -40604, -16060]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![-274077, -54459, 94211, -40604, -16060]] ![![-19, -7, 5, 2, 8]]
  ![![-4489833, -1095788, 1421636, -686198, -683156]] where
 M := ![![![-4489833, -1095788, 1421636, -686198, -683156]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N3 : IdealMulLeCertificate' Table 
  ![![-4489833, -1095788, 1421636, -686198, -683156]] ![![-19, -7, 5, 2, 8]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![-72792597, -20991435, 21121305, -11458380, -17728860]]]
 hmul := by decide  
 g := ![![![![-24264199, -6997145, 7040435, -3819460, -5909620]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-205, 2, 96, -26, 76]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![-205, 2, 96, -26, 76]] 
 ![![5, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-205, 2, 96, -26, 76], ![-300, -751, -310, -116, -1444], ![9360, 3658, -2143, 1572, 4256], ![-17334, 5690, 11416, -1625, 17822], ![-2706, -4384, -1368, -798, -8091]]]
  hmulB := by decide  
  f := ![![![-56381, -18834, 16484, 6026, 24776]], ![![-70791, -23433, 20586, 7530, 30932]], ![![-131161, -43412, 38137, 13950, 57304]], ![![-199352, -65846, 57892, 21179, 86982]], ![![61506, 20288, -17848, -6530, -26815]]]
  g := ![![![-51, 2, 96, -26, 76], ![499, -751, -310, -116, -1444], ![-523, 3658, -2143, 1572, 4256], ![-8514, 5690, 11416, -1625, 17822], ![2682, -4384, -1368, -798, -8091]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![-205, 2, 96, -26, 76]] ![![-205, 2, 96, -26, 76]]
  ![![1185013, -131868, -626812, 137612, -688180]] where
 M := ![![![1185013, -131868, -626812, 137612, -688180]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![1185013, -131868, -626812, 137612, -688180]] ![![-205, 2, 96, -26, 76]]
  ![![-6593478913, 1608517998, 4010307276, -675313974, 5633351952]] where
 M := ![![![-6593478913, 1608517998, 4010307276, -675313974, 5633351952]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![-6593478913, 1608517998, 4010307276, -675313974, 5633351952]] ![![-205, 2, 96, -26, 76]]
  ![![34867625924329, -15090631428344, -25141512845016, 2891015751896, -43370832908104]] where
 M := ![![![34867625924329, -15090631428344, -25141512845016, 2891015751896, -43370832908104]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![34867625924329, -15090631428344, -25141512845016, 2891015751896, -43370832908104]] ![![-205, 2, 96, -26, 76]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![-170696627309369845, 126022756564882650, 154238785100322520, -8766479156873810, 319875624474149620]]]
 hmul := by decide  
 g := ![![![![-34139325461873969, 25204551312976530, 30847757020064504, -1753295831374762, 63975124894829924]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-921764, -304260, 267452, 97851, 401863]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![-921764, -304260, 267452, 97851, 401863]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![2, 6, 2, 1, 0], ![3, 2, 4, 0, 1]] where
  M :=![![![-921764, -304260, 267452, 97851, 401863], ![-2998284, -989701, 869952, 318284, 1307160], ![-9752664, -3219280, 2829707, 1035288, 4251832], ![-14362218, -4740920, 4167112, 1524597, 6261396], ![4998327, 1649908, -1450252, -530595, -2179104]]]
  hmulB := by decide  
  f := ![![![-188, -108, 20, -35, -161]], ![![1176, 21, -528, 152, -364]], ![![1272, 4080, 1845, 584, 7960]], ![![-2428, -358, 910, -347, 116]], ![![1839, 2238, 484, 466, 3965]]]
  g := ![![![-331865, -242156, -219386, 97851, 401863], ![-1079476, -787675, -713608, 318284, 1307160], ![-3511248, -2562096, -2321171, 1035288, 4251832], ![-5170800, -3773042, -3418238, 1524597, 6261396], ![1799547, 1313098, 1189622, -530595, -2179104]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 3 2 2 [6, 6, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 4], [4, 2], [0, 1]]
 g := ![![[5, 5, 4], [1]], ![[4, 5, 1], [1]], ![[5, 4, 2], [1]]]
 h' := ![![[5, 4], [1, 1, 2], [0, 1]], ![[4, 2], [0, 0, 4], [5, 4]], ![[0, 1], [2, 6, 1], [4, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3], []]
 b := ![[], [5, 6, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 3
  hpos := by decide
  P := [6, 6, 5, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1256199150, 1199986804, 133762170, 264235536, 1981791770]
  a := ![33, -74, -69, -37, -209]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-745378176, -621287136, -1188839426, 264235536, 1981791770]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 343 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-188, -108, 20, -35, -161]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![-188, -108, 20, -35, -161]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![6, 3, 1, 0, 0], ![5, 6, 0, 1, 0], ![1, 4, 0, 0, 1]] where
  M :=![![![-188, -108, 20, -35, -161], ![1176, 21, -528, 152, -364], ![1272, 4080, 1845, 584, 7960], ![-26220, -10576, 5808, -4439, -12602], ![5997, -372, -2996, 727, -2874]]]
  hmulB := by decide  
  f := ![![![-921764, -304260, 267452, 97851, 401863]], ![![-2998284, -989701, 869952, 318284, 1307160]], ![![-3468300, -1144849, 1006325, 368178, 1512070]], ![![-5280106, -1742918, 1532012, 560508, 2301953]], ![![-1130939, -373308, 328144, 120056, 493057]]]
  g := ![![![4, 98, 20, -35, -161], ![564, 307, -528, 152, -364], ![-2954, -5257, 1845, 584, 7960], ![-3753, 7006, 5808, -4439, -12602], ![3316, 2250, -2996, 727, -2874]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P1 : CertificateIrreducibleZModOfList' 7 2 2 2 [1, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 6], [0, 1]]
 g := ![![[3, 1], [4, 1]], ![[0, 6], [1, 6]]]
 h' := ![![[4, 6], [3, 1], [0, 1]], ![[0, 1], [0, 6], [4, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [5, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N1 : CertifiedPrimeIdeal' SI7N1 7 where
  n := 2
  hpos := by decide
  P := [1, 3, 1]
  hirr := P7P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2356646, -2333519, -283437, -479783, -3867077]
  a := ![-45, 35, 95, -17, 286]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![801424, 2409114, -283437, -479783, -3867077]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N1 B_one_repr
lemma NI7N1 : Nat.card (O ⧸ I7N1) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![-921764, -304260, 267452, 97851, 401863]] ![![-188, -108, 20, -35, -161]]
  ![![7, 0, 0, 0, 0]] where
 M := ![![![7, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-73922, 32823, -8001, -1737, -14587]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-73922, 32823, -8001, -1737, -14587]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![2, 1, 4, 10, 1]] where
  M :=![![![-73922, 32823, -8001, -1737, -14587], ![97944, -46156, 11979, 2750, 21516], ![-145596, 59609, -13156, -2574, -24596], ![32538, -23837, 8371, 2343, 14124], ![-6939, 6304, -2416, -705, -4014]]]
  hmulB := by decide  
  f := ![![![50, -3, -25, 5, -27]], ![![132, 198, 57, 34, 352]], ![![-2316, -777, 606, -386, -820]], ![![3552, -1823, -2733, 251, -5050]], ![![2489, -1822, -2241, 113, -4682]]]
  g := ![![![-4068, 4310, 4577, 13103, -14587], ![4992, -6152, -6735, -19310, 21516], ![-8764, 7655, 7748, 22126, -24596], ![390, -3451, -4375, -12627, 14124], ![99, 938, 1240, 3585, -4014]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 4 2 3 [7, 3, 2, 3, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 7, 7, 3], [6, 5, 0, 8], [1, 9, 4], [0, 1]]
 g := ![![[3, 1, 5, 5], [8, 1], []], ![[3, 9, 6, 3, 9, 4], [7, 1, 10, 2, 5, 4], [6, 4, 9]], ![[4, 0, 4, 5, 0, 10], [7, 5, 5, 0, 4, 10], [0, 6, 9]], ![[6, 9, 8, 9, 4], [6, 7, 4, 9, 5], [5]]]
 h' := ![![[1, 7, 7, 3], [10, 2, 3, 7], [0, 0, 1], [0, 1]], ![[6, 5, 0, 8], [4, 8, 7, 7], [3, 1, 9, 7], [1, 7, 7, 3]], ![[1, 9, 4], [5, 10, 8, 9], [3, 7, 10, 2], [6, 5, 0, 8]], ![[0, 1], [3, 2, 4, 10], [10, 3, 2, 2], [1, 9, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [9, 8, 2], []]
 b := ![[], [], [8, 1, 1, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 4
  hpos := by decide
  P := [7, 3, 2, 3, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2271576059, 416469540, 1305594192, -190131450, 1806954537]
  a := ![4, -12, -8, -8, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-535044103, -126407727, -538383996, -1659970620, 1806954537]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 14641 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![50, -3, -25, 5, -27]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![50, -3, -25, 5, -27]] 
 ![![11, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![50, -3, -25, 5, -27], ![132, 198, 57, 34, 352], ![-2316, -777, 606, -386, -820], ![3552, -1823, -2733, 251, -5050], ![891, 1104, 248, 233, 1980]]]
  hmulB := by decide  
  f := ![![![-73922, 32823, -8001, -1737, -14587]], ![![8904, -4196, 1089, 250, 1956]], ![![-13236, 5419, -1196, -234, -2236]], ![![2958, -2167, 761, 213, 1284]], ![![-7351, 3557, -947, -222, -1691]]]
  g := ![![![7, -3, -25, 5, -27], ![-20, 198, 57, 34, 352], ![-136, -777, 606, -386, -820], ![782, -1823, -2733, 251, -5050], ![-99, 1104, 248, 233, 1980]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-73922, 32823, -8001, -1737, -14587]] ![![50, -3, -25, 5, -27]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7504, -2764, 1962, 721, 3043]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-7504, -2764, 1962, 721, 3043]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![10, 5, 12, 6, 1]] where
  M :=![![![-7504, -2764, 1962, 721, 3043], ![-22584, -8341, 5888, 2164, 9140], ![-67824, -25124, 17627, 6480, 27392], ![-90324, -33592, 23374, 8593, 36374], ![35121, 13004, -9132, -3357, -14190]]]
  hmulB := by decide  
  f := ![![![-1408, 636, -158, -35, -287]], ![![1932, -873, 216, 48, 392]], ![![-2640, 1204, -297, -64, -528]], ![![810, -392, 110, 15, 172]], ![![-2419, 1091, -264, -61, -482]]]
  g := ![![![-2918, -1383, -2658, -1349, 3043], ![-8768, -4157, -7984, -4052, 9140], ![-26288, -12468, -23929, -12144, 27392], ![-34928, -16574, -31778, -16127, 36374], ![13617, 6458, 12396, 6291, -14190]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 4 2 3 [7, 1, 3, 6, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 10, 7, 11], [7, 12, 9, 7], [11, 3, 10, 8], [0, 1]]
 g := ![![[9, 6, 2, 1], [7, 7, 1], []], ![[8, 10, 11, 1, 2, 7], [3, 9, 9], [8, 4, 7, 7, 2, 5]], ![[4, 12, 0, 10, 12, 7], [11, 9, 4], [7, 4, 9, 8, 6, 5]], ![[12, 2, 2, 12, 0, 2], [12, 2, 3], [0, 6, 11, 6, 5, 5]]]
 h' := ![![[2, 10, 7, 11], [3, 9, 4, 1], [0, 0, 0, 1], [0, 1]], ![[7, 12, 9, 7], [8, 8, 1, 4], [4, 6, 9, 10], [2, 10, 7, 11]], ![[11, 3, 10, 8], [0, 4, 6, 1], [8, 0, 8, 11], [7, 12, 9, 7]], ![[0, 1], [6, 5, 2, 7], [5, 7, 9, 4], [11, 3, 10, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [1, 9], []]
 b := ![[], [], [1, 6, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 4
  hpos := by decide
  P := [7, 1, 3, 6, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1311445865976, -21342833819158, -13333017322283, -1799783460512, -43847716576616]
  a := ![-53, 134, 111, 72, 336]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![33829893202472, 15222749927994, 39449198584393, 20098962769168, -43847716576616]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 28561 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1408, 636, -158, -35, -287]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![-1408, 636, -158, -35, -287]] 
 ![![13, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![12, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![-1408, 636, -158, -35, -287], ![1932, -873, 216, 48, 392], ![-2640, 1204, -297, -64, -528], ![810, -392, 110, 15, 172], ![-207, 92, -28, -5, -52]]]
  hmulB := by decide  
  f := ![![![-7504, -2764, 1962, 721, 3043]], ![![-8664, -3193, 2264, 832, 3512]], ![![-12144, -4484, 3167, 1164, 4916]], ![![-6948, -2584, 1798, 661, 2798]], ![![-1339, -488, 354, 130, 547]]]
  g := ![![![-395, 636, -158, -35, -287], ![544, -873, 216, 48, 392], ![-756, 1204, -297, -64, -528], ![230, -392, 110, 15, 172], ![-47, 92, -28, -5, -52]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-7504, -2764, 1962, 721, 3043]] ![![-1408, 636, -158, -35, -287]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-808, -291, 221, 81, 339]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![-808, -291, 221, 81, 339]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![1, 14, 1, 1, 0], ![5, 14, 13, 0, 1]] where
  M :=![![![-808, -291, 221, 81, 339], ![-2520, -890, 681, 250, 1044], ![-7764, -2765, 2110, 774, 3236], ![-10770, -3823, 2921, 1071, 4476], ![4011, 1424, -1088, -399, -1668]]]
  hmulB := by decide  
  f := ![![![-8, -3, 3, 1, 5]], ![![-36, -12, 9, 2, 8]], ![![-60, -33, 12, 14, 28]], ![![-40, -11, 12, 4, 19]], ![![-77, -36, 17, 12, 27]]]
  g := ![![![-152, -363, -251, 81, 339], ![-470, -1118, -773, 250, 1044], ![-1454, -3465, -2396, 774, 3236], ![-2013, -4793, -3314, 1071, 4476], ![750, 1786, 1235, -399, -1668]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [5, 7, 11, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 13, 11], [3, 3, 6], [0, 1]]
 g := ![![[13, 6, 4], [8, 8], [6, 1], []], ![[0, 5, 7, 11], [16, 8], [16, 9], [9, 2]], ![[16, 5, 15, 6], [14, 15], [0, 16], [14, 2]]]
 h' := ![![[3, 13, 11], [10, 4, 2], [4, 4, 12], [0, 0, 1], [0, 1]], ![[3, 3, 6], [1, 11, 16], [9, 10, 12], [15, 5, 3], [3, 13, 11]], ![[0, 1], [2, 2, 16], [15, 3, 10], [7, 12, 13], [3, 3, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 16], []]
 b := ![[], [7, 0, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [5, 7, 11, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![908470697, 7203085634, 3878854267, 816460644, 14422816225]
  a := ![59, -126, -123, -55, -374]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4236592416, -12126281796, -10849071606, 816460644, 14422816225]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 4913 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![421, 182, -86, 72, 226]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![421, 182, -86, 72, 226]] 
 ![![17, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![13, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![15, 0, 0, 0, 1]] where
  M :=![![![421, 182, -86, 72, 226], ![-1788, 367, 1046, -192, 1380], ![-7128, -8758, -1937, -1820, -15576], ![53082, 14606, -15822, 8275, 11458], ![-8568, 2968, 5736, -784, 9139]]]
  hmulB := by decide  
  f := ![![![-50059, -43798, 25854, 8960, 40682]], ![![-23410, -9297, 6790, 2472, 10456]], ![![-80807, -51512, 32641, 11516, 50970]], ![![-73647, -29888, 21664, 7875, 33384]], ![![-20109, -30306, 16410, 5552, 26081]]]
  g := ![![![-143, 182, -86, 72, 226], ![-2132, 367, 1046, -192, 1380], ![16157, -8758, -1937, -1820, -15576], ![1933, 14606, -15822, 8275, 11458], ![-13165, 2968, 5736, -784, 9139]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1

def I17N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4030, 1477, -289, -47, -557]] i)))

def SI17N2: IdealEqSpanCertificate' Table ![![-4030, 1477, -289, -47, -557]] 
 ![![17, 0, 0, 0, 0], ![13, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![15, 0, 0, 0, 1]] where
  M :=![![![-4030, 1477, -289, -47, -557], ![3624, -2702, 913, 254, 1556], ![-10860, 1615, 346, 238, 316], ![-3474, -2991, 1779, 617, 2796], ![1563, 992, -632, -223, -986]]]
  hmulB := by decide  
  f := ![![![58, 133, 53, 25, 265]], ![![-58, 65, 66, 3, 165]], ![![326, -128, -227, 31, -371]], ![![1136, 1061, 109, 259, 1802]], ![![-507, -53, 203, -68, 75]]]
  g := ![![![-847, 1477, -289, -47, -557], ![793, -2702, 913, 254, 1556], ![-2229, 1615, 346, 238, 316], ![-634, -2991, 1779, 617, 2796], ![293, 992, -632, -223, -986]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N2 : Nat.card (O ⧸ I17N2) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N2)

lemma isPrimeI17N2 : Ideal.IsPrime I17N2 := prime_ideal_of_norm_prime hp17.out _ NI17N2
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![-808, -291, 221, 81, 339]] ![![421, 182, -86, 72, 226]]
  ![![-58, -133, -53, -25, -265]] where
 M := ![![![-58, -133, -53, -25, -265]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI17N1 : IdealMulLeCertificate' Table 
  ![![-58, -133, -53, -25, -265]] ![![-4030, 1477, -289, -47, -557]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2455, 873, -665, -244, -1020]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![2455, 873, -665, -244, -1020]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![17, 8, 1, 0, 0], ![8, 15, 0, 1, 0], ![3, 5, 0, 0, 1]] where
  M :=![![![2455, 873, -665, -244, -1020], ![7584, 2698, -2055, -754, -3152], ![23436, 8335, -6350, -2330, -9740], ![32418, 11529, -8785, -3223, -13474], ![-12090, -4300, 3276, 1202, 5025]]]
  hmulB := by decide  
  f := ![![![25, -5, -1, 0, 0]], ![![0, 24, -5, -2, 0]], ![![23, 4, -3, -2, -4]], ![![26, 17, -12, -1, -10]], ![![3, 7, 0, 0, 5]]]
  g := ![![![988, 787, -665, -244, -1020], ![3053, 2432, -2055, -754, -3152], ![9434, 7515, -6350, -2330, -9740], ![13051, 10396, -8785, -3223, -13474], ![-4867, -3877, 3276, 1202, 5025]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [15, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 18], [0, 1]]
 g := ![![[16, 5], [], [11], [1]], ![[13, 14], [], [11], [1]]]
 h' := ![![[7, 18], [0, 9], [3], [4, 7], [0, 1]], ![[0, 1], [6, 10], [3], [15, 12], [7, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [8, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [15, 12, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1465965, -647856, 292100, -250120, -809324]
  a := ![-42, 82, 88, 24, 266]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-105407, 253356, 292100, -250120, -809324]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2987, 1349, -335, -74, -608]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![-2987, 1349, -335, -74, -608]] 
 ![![19, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![10, 0, 0, 1, 0], ![0, 0, 0, 0, 19]] where
  M :=![![![-2987, 1349, -335, -74, -608], ![4092, -1852, 461, 102, 836], ![-5628, 2535, -628, -138, -1140], ![1788, -819, 209, 47, 380], ![-444, 204, -52, -12, -95]]]
  hmulB := by decide  
  f := ![![![391, 143, -103, -38, -160]], ![![186, 68, -49, -18, -76]], ![![230, 85, -60, -22, -92]], ![![454, 167, -119, -45, -188]], ![![-1836, -684, 476, 180, 739]]]
  g := ![![![-509, 1349, -335, -74, -32], ![698, -1852, 461, 102, 44], ![-958, 2535, -628, -138, -60], ![306, -819, 209, 47, 20], ![-76, 204, -52, -12, -5]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P1 : CertificateIrreducibleZModOfList' 19 2 2 4 [18, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 18], [0, 1]]
 g := ![![[17, 9], [10, 11], [4], [1]], ![[18, 10], [7, 8], [4], [1]]]
 h' := ![![[17, 18], [10, 16], [5, 7], [1, 17], [0, 1]], ![[0, 1], [16, 3], [10, 12], [5, 2], [17, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [14, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N1 : CertifiedPrimeIdeal' SI19N1 19 where
  n := 2
  hpos := by decide
  P := [18, 2, 1]
  hirr := P19P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2278191, -35216, 1057396, -110496, 1156416]
  a := ![-65, 150, 140, 80, 416]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-161933, -35216, 1057396, -110496, 60864]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N1 B_one_repr
lemma NI19N1 : Nat.card (O ⧸ I19N1) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N1

def I19N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13, -4, 4, 2, 8]] i)))

def SI19N2: IdealEqSpanCertificate' Table ![![-13, -4, 4, 2, 8]] 
 ![![19, 0, 0, 0, 0], ![18, 1, 0, 0, 0], ![18, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![15, 0, 0, 0, 1]] where
  M :=![![![-13, -4, 4, 2, 8], ![-60, -15, 20, 4, 28], ![-192, -100, 33, 8, -16], ![54, 12, -12, 71, 186], ![30, 40, 8, -14, 9]]]
  hmulB := by decide  
  f := ![![![1541, -980, 308, 82, 532]], ![![1266, -887, 292, 80, 500]], ![![1470, -1076, 361, 100, 616]], ![![-306, -60, 60, 23, 90]], ![![1323, -748, 220, 56, 385]]]
  g := ![![![-7, -4, 4, 2, 8], ![-30, -15, 20, 4, 28], ![66, -100, 33, 8, -16], ![-144, 12, -12, 71, 186], ![-51, 40, 8, -14, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N2 : Nat.card (O ⧸ I19N2) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N2)

lemma isPrimeI19N2 : Ideal.IsPrime I19N2 := prime_ideal_of_norm_prime hp19.out _ NI19N2
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![2455, 873, -665, -244, -1020]] ![![-2987, 1349, -335, -74, -608]]
  ![![-1541, 980, -308, -82, -532]] where
 M := ![![![-1541, 980, -308, -82, -532]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI19N1 : IdealMulLeCertificate' Table 
  ![![-1541, 980, -308, -82, -532]] ![![-13, -4, 4, 2, 8]]
  ![![19, 0, 0, 0, 0]] where
 M := ![![![-19, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-46, -56, -12, -9, -91]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![-46, -56, -12, -9, -91]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![6, 17, 21, 1, 0], ![8, 5, 16, 0, 1]] where
  M :=![![![-46, -56, -12, -9, -91], ![600, 189, -164, 104, 204], ![-1848, 972, 1437, -112, 2728], ![-8148, -6484, -104, -1679, -10414], ![3567, 948, -1084, 541, 664]]]
  hmulB := by decide  
  f := ![![![58174, -26272, 6524, 1441, 11841]], ![![-79692, 36067, -8980, -1988, -16288]], ![![109656, -49364, 12211, 2688, 22184]], ![![54882, -24571, 6037, 1321, 10986]], ![![79567, -35811, 8856, 1949, 16090]]]
  g := ![![![32, 24, 71, -9, -91], ![-72, -113, -244, 104, 204], ![-1000, -468, -1733, -112, 2728], ![3706, 3223, 8773, -1679, -10414], ![-217, -503, -1003, 541, 664]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [15, 21, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 11, 6], [2, 11, 17], [0, 1]]
 g := ![![[21, 13, 13], [2, 10, 12], [14, 9, 1], []], ![[22, 18, 2, 3], [6, 9, 15, 12], [2, 22, 17, 13], [19, 13]], ![[17, 21, 5, 15], [20, 6, 0, 20], [14, 10, 13, 10], [8, 13]]]
 h' := ![![[7, 11, 6], [16, 1, 17], [20, 8, 14], [0, 0, 1], [0, 1]], ![[2, 11, 17], [13, 6, 9], [15, 0, 18], [17, 20, 11], [7, 11, 6]], ![[0, 1], [1, 16, 20], [22, 15, 14], [22, 3, 11], [2, 11, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 6], []]
 b := ![[], [6, 17, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [15, 21, 14, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![152713447, -46657270, -98497034, 14694460, -149795916]
  a := ![-13, 24, 27, 8, 82]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![54909305, 19674630, 86506694, 14694460, -149795916]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 12167 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![26, -14, 4, 1, 7]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![26, -14, 4, 1, 7]] 
 ![![23, 0, 0, 0, 0], ![13, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![11, 0, 0, 1, 0], ![13, 0, 0, 0, 1]] where
  M :=![![![26, -14, 4, 1, 7], ![-48, 15, -2, 0, -4], ![24, -34, 15, 4, 24], ![-60, -10, 8, 3, 6], ![21, 4, -4, -1, -4]]]
  hmulB := by decide  
  f := ![![![-458, -158, 128, 47, 195]], ![![-322, -111, 90, 33, 137]], ![![-498, -172, 139, 51, 211]], ![![-500, -172, 140, 52, 215]], ![![-157, -54, 44, 16, 67]]]
  g := ![![![2, -14, 4, 1, 7], ![-7, 15, -2, 0, -4], ![-5, -34, 15, 4, 24], ![-7, -10, 8, 3, 6], ![4, 4, -4, -1, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1

def I23N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1259, -438, 76, 10, 152]] i)))

def SI23N2: IdealEqSpanCertificate' Table ![![1259, -438, 76, 10, 152]] 
 ![![23, 0, 0, 0, 0], ![14, 1, 0, 0, 0], ![11, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![14, 0, 0, 0, 1]] where
  M :=![![![1259, -438, 76, 10, 152], ![-972, 857, -318, -92, -532], ![3744, -358, -247, -124, -304], ![1770, 1122, -764, -269, -1178], ![-702, -368, 264, 94, 405]]]
  hmulB := by decide  
  f := ![![![-167, -62, 40, -30, -76]], ![![-74, -47, 6, -16, -76]], ![![85, 128, 37, 22, 228]], ![![-974, -218, 320, -149, -114]], ![![16, -108, -72, -10, -231]]]
  g := ![![![189, -438, 76, 10, 152], ![-56, 857, -318, -92, -532], ![727, -358, -247, -124, -304], ![570, 1122, -764, -269, -1178], ![-212, -368, 264, 94, 405]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N2 : Nat.card (O ⧸ I23N2) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N2)

lemma isPrimeI23N2 : Ideal.IsPrime I23N2 := prime_ideal_of_norm_prime hp23.out _ NI23N2
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![-46, -56, -12, -9, -91]] ![![26, -14, 4, 1, 7]]
  ![![-167, -62, 40, -30, -76]] where
 M := ![![![-167, -62, 40, -30, -76]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI23N1 : IdealMulLeCertificate' Table 
  ![![-167, -62, 40, -30, -76]] ![![1259, -438, 76, 10, 152]]
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


lemma PB1705I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB1705I0 : PrimesBelowBoundCertificateInterval O 1 23 1705 where
  m := 9
  g := ![5, 5, 5, 2, 2, 2, 3, 3, 3]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB1705I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N0, I3N1, I3N1, I3N1]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1]
    · exact ![I17N0, I17N1, I17N2]
    · exact ![I19N0, I19N1, I19N2]
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
    · exact ![3, 3, 3, 3, 3]
    · exact ![5, 5, 5, 5, 5]
    · exact ![343, 49]
    · exact ![14641, 11]
    · exact ![28561, 13]
    · exact ![4913, 17, 17]
    · exact ![361, 361, 19]
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
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
      exact NI17N2
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
      exact NI19N2
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
      exact NI23N2
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I5N0, I7N0, I7N1, I11N1, I13N1, I17N1, I17N2, I19N0, I19N1, I19N2, I23N1, I23N2]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N0, I3N1, I3N1, I3N1], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N0, I7N1], [I11N1], [I13N1], [I17N1, I17N2], [I19N0, I19N1, I19N2], [I23N1, I23N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
