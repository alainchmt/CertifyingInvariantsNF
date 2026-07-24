
import IdealArithmetic.Examples.NF5_3_1215000000_3.RI5_3_1215000000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13, 8, 1, 1, -2]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![-13, 8, 1, 1, -2]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-13, 8, 1, 1, -2], ![24, -15, -2, -2, 4], ![-48, 28, 5, 4, -8], ![36, -20, -5, -2, 6], ![-36, 20, 4, 2, -5]]]
  hmulB := by decide  
  f := ![![![-14, -8, -1, 1, 2]], ![![-12, -7, -1, 1, 2]], ![![-24, -12, -1, 2, 4]], ![![-25, -12, 0, 3, 4]], ![![-24, -12, -1, 3, 5]]]
  g := ![![![-7, 8, 1, 1, -2], ![13, -15, -2, -2, 4], ![-26, 28, 5, 4, -8], ![19, -20, -5, -2, 6], ![-19, 20, 4, 2, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9751, 5824, 883, -580, -1373]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![9751, 5824, 883, -580, -1373]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![9751, 5824, 883, -580, -1373], ![16476, 9841, 1492, -980, -2320], ![27840, 16628, 2521, -1656, -3920], ![15282, 9128, 1384, -909, -2152], ![24495, 14630, 2218, -1457, -3449]]]
  hmulB := by decide  
  f := ![![![11, -2, -3, -1, 1]], ![![-6, 5, 2, -2, -2]], ![![24, -4, 1, 0, -8]], ![![51, 6, -19, -6, 1]], ![![13, 8, 5, -10, -10]]]
  g := ![![![5562, 5824, 883, -580, -1373], ![9398, 9841, 1492, -980, -2320], ![15880, 16628, 2521, -1656, -3920], ![8717, 9128, 1384, -909, -2152], ![13972, 14630, 2218, -1457, -3449]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1112, 305, -115, -249, -301]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![1112, 305, -115, -249, -301]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![1112, 305, -115, -249, -301], ![3612, 945, -401, -832, -996], ![11952, 3047, -1375, -2794, -3328], ![18162, 4549, -2138, -4287, -5090], ![22149, 5565, -2597, -5219, -6200]]]
  hmulB := by decide  
  f := ![![![8932, -5433, -783, -656, 1398]], ![![-3922, 2385, 344, 287, -613]], ![![20210, -12296, -1768, -1481, 3159]], ![![-6100, 3723, 524, 448, -951]], ![![15191, -9250, -1324, -1118, 2377]]]
  g := ![![![736, 305, -115, -249, -301], ![2448, 945, -401, -832, -996], ![8201, 3047, -1375, -2794, -3328], ![12564, 4549, -2138, -4287, -5090], ![15300, 5565, -2597, -5219, -6200]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![-13, 8, 1, 1, -2]] ![![9751, 5824, 883, -580, -1373]]
  ![![-823, -488, -74, 49, 115]] where
 M := ![![![-823, -488, -74, 49, 115]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![-823, -488, -74, 49, 115]] ![![9751, 5824, 883, -580, -1373]]
  ![![-14559778, -8696310, -1318473, 866028, 2050136]] where
 M := ![![![-14559778, -8696310, -1318473, 866028, 2050136]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![-14559778, -8696310, -1318473, 866028, 2050136]] ![![1112, 305, -115, -249, -301]]
  ![![-2222671352, -1327564259, -201275901, 132206384, 312970362]] where
 M := ![![![-2222671352, -1327564259, -201275901, 132206384, 312970362]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![-2222671352, -1327564259, -201275901, 132206384, 312970362]] ![![1112, 305, -115, -249, -301]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![-339309321538, -202663752116, -30726441892, 20182410044, 47777538484]]]
 hmul := by decide  
 g := ![![![![-169654660769, -101331876058, -15363220946, 10091205022, 23888769242]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-42920, 26121, 3756, 3151, -6719]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![-42920, 26121, 3756, 3151, -6719]] 
 ![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 1, 0, 1, 0], ![1, 2, 0, 0, 1]] where
  M :=![![![-42920, 26121, 3756, 3151, -6719], ![80628, -49034, -7057, -5926, 12604], ![-151248, 92101, 13234, 11094, -23704], ![101910, -61889, -8923, -7507, 15886], ![-103125, 62887, 9020, 7547, -16208]]]
  hmulB := by decide  
  f := ![![![186, -85, -6, 79, -57]], ![![684, 44, -471, -126, 316]], ![![-1202, 190, 518, -77, -187]], ![![1122, -397, -202, 331, -154]], ![![721, 168, -644, -272, 507]]]
  g := ![![![-13319, 12136, 3756, 3151, -6719], ![25027, -22772, -7057, -5926, 12604], ![-46926, 42805, 13234, 11094, -23704], ![31649, -28718, -8923, -7507, 15886], ![-31979, 29252, 9020, 7547, -16208]]]
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
  c := ![-34417, -4086, 7609, 5017, 5191]
  a := ![0, 4, 9, -4, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-15739, -6495, 7609, 5017, 5191]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 9 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-159, -91, -13, 8, 22]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![-159, -91, -13, 8, 22]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-159, -91, -13, 8, 22], ![-264, -158, -19, 18, 32], ![-384, -269, -66, 26, 72], ![-300, -123, -7, -3, 36], ![-366, -241, -31, 32, 41]]]
  hmulB := by decide  
  f := ![![![-463857, 282227, 40595, 34068, -72578]], ![![290312, -176636, -25407, -21322, 45424]], ![![-545088, 331651, 47704, 40034, -85288]], ![![366572, -223035, -32081, -26923, 57356]], ![![-372034, 226359, 32559, 27324, -58211]]]
  g := ![![![-53, -91, -13, 8, 22], ![-88, -158, -19, 18, 32], ![-128, -269, -66, 26, 72], ![-100, -123, -7, -3, 36], ![-122, -241, -31, 32, 41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![-42920, 26121, 3756, 3151, -6719]] ![![-159, -91, -13, 8, 22]]
  ![![-114, -56, -3, 13, 21]] where
 M := ![![![-114, -56, -3, 13, 21]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N1 : IdealMulLeCertificate' Table 
  ![![-114, -56, -3, 13, 21]] ![![-159, -91, -13, 8, 22]]
  ![![22476, 13369, 2002, -1365, -3187]] where
 M := ![![![22476, 13369, 2002, -1365, -3187]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![22476, 13369, 2002, -1365, -3187]] ![![-159, -91, -13, 8, 22]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![-6295926, -3760194, -569979, 374613, 886617]]]
 hmul := by decide  
 g := ![![![![-2098642, -1253398, -189993, 124871, 295539]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1001, 585, 83, -66, -146]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![1001, 585, 83, -66, -146]] 
 ![![5, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![1001, 585, 83, -66, -146], ![1752, 1004, 133, -126, -264], ![3168, 1747, 200, -262, -504], ![2148, 1061, 61, -241, -392], ![3198, 1639, 127, -328, -559]]]
  hmulB := by decide  
  f := ![![![-191, 49, 57, -38, 2]], ![![-43, -9, 38, 16, -30]], ![![212, 7, -142, -38, 96]], ![![-564, 149, 167, -105, 0]], ![![143, -84, 14, 78, -65]]]
  g := ![![![46, 585, 83, -66, -146], ![96, 1004, 133, -126, -264], ![225, 1747, 200, -262, -504], ![247, 1061, 61, -241, -392], ![322, 1639, 127, -328, -559]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![1001, 585, 83, -66, -146]] ![![1001, 585, 83, -66, -146]]
  ![![1681189, 1008606, 154920, -97728, -234932]] where
 M := ![![![1681189, 1008606, 154920, -97728, -234932]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![1681189, 1008606, 154920, -97728, -234932]] ![![1001, 585, 83, -66, -146]]
  ![![2979502181, 1778038273, 268869513, -178021726, -420168894]] where
 M := ![![![2979502181, 1778038273, 268869513, -178021726, -420168894]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![2979502181, 1778038273, 268869513, -178021726, -420168894]] ![![1001, 585, 83, -66, -146]]
  ![![5223292564201, 3120336372636, 473330899108, -310405145552, -735260728712]] where
 M := ![![![5223292564201, 3120336372636, 473330899108, -310405145552, -735260728712]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![5223292564201, 3120336372636, 473330899108, -310405145552, -735260728712]] ![![1001, 585, 83, -66, -146]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![9176743406930945, 5480920755136165, 830891373785775, -545939228660130, -1292238725493290]]]
 hmul := by decide  
 g := ![![![![1835348681386189, 1096184151027233, 166178274757155, -109187845732026, -258447745098658]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4181, 531, 2093, 334, -1280]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![-4181, 531, 2093, 334, -1280]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![5, 6, 0, 5, 1]] where
  M :=![![![-4181, 531, 2093, 334, -1280], ![15360, -3702, -5257, 1626, 1336], ![-16032, 9813, -1610, -7842, 6504], ![-46704, 203, 28385, 4081, -16352], ![44880, -5707, -20461, 2502, 7667]]]
  hmulB := by decide  
  f := ![![![-232043, -137087, -20107, 14570, 33280]], ![![-399360, -233440, -33107, 26346, 58280]], ![![-699360, -400533, -53012, 50346, 105384]], ![![-432624, -231947, -23291, 39199, 71552]], ![![-911953, -515761, -65207, 68973, 140043]]]
  g := ![![![317, 1173, 299, 962, -1280], ![1240, -1674, -751, -722, 1336], ![-6936, -4173, -230, -5766, 6504], ![5008, 14045, 4055, 12263, -16352], ![935, -7387, -2923, -5119, 7667]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 4 2 2 [5, 5, 0, 2, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 3, 4, 3], [2, 0, 0, 5], [1, 3, 3, 6], [0, 1]]
 g := ![![[1, 4, 5, 1], []], ![[6, 3, 5, 0, 2, 6], [5, 6, 0, 5, 5, 6]], ![[3, 3], [0, 5, 2, 3, 2, 6]], ![[0, 4, 1, 4, 0, 3], [3, 4, 5, 2, 4, 6]]]
 h' := ![![[2, 3, 4, 3], [0, 0, 0, 1], [0, 1]], ![[2, 0, 0, 5], [4, 2, 2, 4], [2, 3, 4, 3]], ![[1, 3, 3, 6], [1, 3], [2, 0, 0, 5]], ![[0, 1], [0, 2, 5, 2], [1, 3, 3, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [4, 3, 4], []]
 b := ![[], [], [1, 4, 2, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 4
  hpos := by decide
  P := [5, 5, 0, 2, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-33400821878689, -8747086429140, 3678200426740, 8290652979974, 9835632488132]
  a := ![3, -4, 59, -65, -178]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-11796997759907, -9680125908276, 525457203820, -5841072780098, 9835632488132]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 2401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-232043, -137087, -20107, 14570, 33280]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![-232043, -137087, -20107, 14570, 33280]] 
 ![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![-232043, -137087, -20107, 14570, 33280], ![-399360, -233440, -33107, 26346, 58280], ![-699360, -400533, -53012, 50346, 105384], ![-432624, -231947, -23291, 39199, 71552], ![-664176, -364517, -40817, 55890, 106461]]]
  hmulB := by decide  
  f := ![![![-4181, 531, 2093, 334, -1280]], ![![1597, -453, -452, 280, 8]], ![![-5874, 1857, 1564, -834, -168]], ![![-6672, 29, 4055, 583, -2336]], ![![3425, -436, -1428, 596, 181]]]
  g := ![![![-20102, -137087, -20107, 14570, 33280], ![-36954, -233440, -33107, 26346, 58280], ![-72525, -400533, -53012, 50346, 105384], ![-59813, -231947, -23291, 39199, 71552], ![-83866, -364517, -40817, 55890, 106461]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![-4181, 531, 2093, 334, -1280]] ![![-232043, -137087, -20107, 14570, 33280]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-295, 230, 24, 12, -72]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-295, 230, 24, 12, -72]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![7, 2, 7, 9, 1]] where
  M :=![![![-295, 230, 24, 12, -72], ![864, -355, -82, -96, 48], ![-576, 926, 29, -68, -384], ![1872, -254, -196, -307, -160], ![408, 830, -76, -236, -487]]]
  hmulB := by decide  
  f := ![![![67, 38, 4, -4, -8]], ![![96, 67, 14, -8, -16]], ![![192, 102, 19, -4, -32]], ![![144, 58, -16, -9, 0]], ![![311, 158, 7, -15, -31]]]
  g := ![![![19, 34, 48, 60, -72], ![48, -41, -38, -48, 48], ![192, 154, 247, 308, -384], ![272, 6, 84, 103, -160], ![347, 164, 303, 377, -487]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 4 2 3 [10, 1, 8, 6, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 6, 1, 1], [2, 7, 1, 4], [1, 8, 9, 6], [0, 1]]
 g := ![![[2, 5, 7, 3], [5, 1], []], ![[5, 3, 10, 10, 9, 4], [2, 7, 3, 5, 7, 3], [7, 7, 1]], ![[10, 7, 4, 0, 1, 3], [8, 0, 10, 4], [6, 0, 5]], ![[0, 1, 1, 9, 3, 7], [10, 9, 3, 2, 7, 7], [9, 2, 3]]]
 h' := ![![[2, 6, 1, 1], [5, 7, 3, 6], [0, 0, 1], [0, 1]], ![[2, 7, 1, 4], [2, 5, 10, 2], [0, 2, 0, 5], [2, 6, 1, 1]], ![[1, 8, 9, 6], [10, 10, 6, 8], [10, 0, 10], [2, 7, 1, 4]], ![[0, 1], [0, 0, 3, 6], [10, 9, 0, 6], [1, 8, 9, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [9, 1, 3], []]
 b := ![[], [], [5, 3, 3, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 4
  hpos := by decide
  P := [10, 1, 8, 6, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1973659813, -523331499, 201858378, 492432235, 601335131]
  a := ![1, 1, 6, -5, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-562091430, -156909251, -364317049, -447234904, 601335131]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 14641 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 38, 4, -4, -8]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![67, 38, 4, -4, -8]] 
 ![![11, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![10, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![67, 38, 4, -4, -8], ![96, 67, 14, -8, -16], ![192, 102, 19, -4, -32], ![144, 58, -16, -9, 0], ![120, 102, 32, -12, -29]]]
  hmulB := by decide  
  f := ![![![-295, 230, 24, 12, -72]], ![![-136, 135, 10, 0, -48]], ![![-106, 126, 7, -4, -48]], ![![-98, 186, 4, -17, -80]], ![![-97, 180, 4, -16, -77]]]
  g := ![![![-15, 38, 4, -4, -8], ![-28, 67, 14, -8, -16], ![-42, 102, 19, -4, -32], ![-18, 58, -16, -9, 0], ![-45, 102, 32, -12, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-295, 230, 24, 12, -72]] ![![67, 38, 4, -4, -8]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-40, 8, 17, -3, -5]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-40, 8, 17, -3, -5]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![8, 1, 7, 11, 1]] where
  M :=![![![-40, 8, 17, -3, -5], ![60, -25, -6, 24, -12], ![144, 18, -121, -36, 96], ![-606, 90, 240, -37, -66], ![285, -96, -87, 75, 8]]]
  hmulB := by decide  
  f := ![![![-694, 424, 61, 51, -109]], ![![1308, -793, -114, -96, 204]], ![![-2448, 1494, 215, 180, -384]], ![![1650, -1002, -144, -121, 258]], ![![-377, 235, 34, 28, -60]]]
  g := ![![![0, 1, 4, 4, -5], ![12, -1, 6, 12, -12], ![-48, -6, -61, -84, 96], ![-6, 12, 54, 53, -66], ![17, -8, -11, -1, 8]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 4 2 3 [4, 7, 4, 7, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 6, 7, 2], [0, 11, 3, 2], [7, 8, 3, 9], [0, 1]]
 g := ![![[10, 8, 9, 12], [6, 6, 1], []], ![[4, 12, 2, 6], [8, 5, 10], [5, 0, 0, 8, 2, 8]], ![[8, 12, 6, 9, 10, 2], [8, 12, 9], [4, 0, 1, 8, 6, 8]], ![[7, 8, 6, 11, 3, 1], [11, 12, 4], [10, 2, 11, 2, 7, 1]]]
 h' := ![![[12, 6, 7, 2], [2, 12, 8, 5], [0, 0, 0, 1], [0, 1]], ![[0, 11, 3, 2], [6, 1, 9], [5, 9, 10, 7], [12, 6, 7, 2]], ![[7, 8, 3, 9], [3, 12, 11, 12], [10, 11, 6, 3], [0, 11, 3, 2]], ![[0, 1], [11, 1, 11, 9], [4, 6, 10, 2], [7, 8, 3, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [10, 10, 5], []]
 b := ![[], [], [2, 2, 4, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 4
  hpos := by decide
  P := [4, 7, 4, 7, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1046730557047, -272823482156, 99928652068, 255461341780, 327446511011]
  a := ![1, -8, -30, 18, 87]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-282023280395, -46174614859, -168630532693, -257419252257, 327446511011]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 28561 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-694, 424, 61, 51, -109]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![-694, 424, 61, 51, -109]] 
 ![![13, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![12, 0, 0, 0, 1]] where
  M :=![![![-694, 424, 61, 51, -109], ![1308, -793, -114, -96, 204], ![-2448, 1494, 215, 180, -384], ![1650, -1002, -144, -121, 258], ![-1671, 1020, 147, 123, -262]]]
  hmulB := by decide  
  f := ![![![-40, 8, 17, -3, -5]], ![![-20, 3, 10, 0, -4]], ![![8, 2, -8, -3, 7]], ![![-62, 10, 25, -4, -7]], ![![-15, 0, 9, 3, -4]]]
  g := ![![![-238, 424, 61, 51, -109], ![446, -793, -114, -96, 204], ![-839, 1494, 215, 180, -384], ![563, -1002, -144, -121, 258], ![-573, 1020, 147, 123, -262]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-40, 8, 17, -3, -5]] ![![-694, 424, 61, 51, -109]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13153, -8003, -1151, -966, 2058]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![13153, -8003, -1151, -966, 2058]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![15, 12, 1, 1, 0], ![1, 2, 2, 0, 1]] where
  M :=![![![13153, -8003, -1151, -966, 2058], ![-24696, 15026, 2161, 1814, -3864], ![46368, -28213, -4058, -3406, 7256], ![-31188, 18973, 2731, 2291, -4880], ![31650, -19257, -2771, -2324, 4953]]]
  hmulB := by decide  
  f := ![![![-91, -55, -9, 6, 14]], ![![-168, -92, -11, 10, 24]], ![![-288, -165, -16, 26, 40]], ![![-225, -129, -18, 15, 34]], ![![-77, -42, -4, 6, 11]]]
  g := ![![![1505, -31, -253, -966, 2058], ![-2826, 58, 475, 1814, -3864], ![5306, -109, -892, -3406, 7256], ![-3569, 73, 600, 2291, -4880], ![3621, -75, -609, -2324, 4953]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [7, 15, 7, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 9, 3], [16, 7, 14], [0, 1]]
 g := ![![[13, 12, 1], [], [10, 1], []], ![[1, 1, 2, 11], [9, 8], [3, 15], [8, 9]], ![[0, 12, 4, 11], [3, 8], [13, 13], [14, 9]]]
 h' := ![![[11, 9, 3], [4, 16, 16], [15, 13], [0, 0, 1], [0, 1]], ![[16, 7, 14], [13, 10, 7], [5, 15, 5], [14, 15, 7], [11, 9, 3]], ![[0, 1], [0, 8, 11], [2, 6, 12], [5, 2, 9], [16, 7, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 13], []]
 b := ![[], [5, 7, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [7, 15, 7, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2706614, 4483911, 3830263, -3219879, -4286514]
  a := ![-1, 11, 13, 5, -34]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2934005, 3040911, 919010, -3219879, -4286514]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 4913 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2804, 1525, 164, -243, -455]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![2804, 1525, 164, -243, -455]] 
 ![![17, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![13, 0, 0, 1, 0], ![14, 0, 0, 0, 1]] where
  M :=![![![2804, 1525, 164, -243, -455], ![5460, 2756, 191, -582, -972], ![11664, 5261, 32, -1562, -2328], ![11238, 4087, -559, -2005, -2638], ![15111, 5831, -550, -2525, -3412]]]
  hmulB := by decide  
  f := ![![![394, 109, -390, -205, 341]], ![![-148, 58, 19, -54, 32]], ![![602, -166, -172, 113, -3]], ![![560, 208, -611, -326, 535]], ![![-269, 109, 22, -127, 88]]]
  g := ![![![357, 1525, 164, -243, -455], ![907, 2756, 191, -582, -972], ![2558, 5261, 32, -1562, -2328], ![3438, 4087, -559, -2005, -2638], ![4290, 5831, -550, -2525, -3412]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1

def I17N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![836, -206, -265, 141, 19]] i)))

def SI17N2: IdealEqSpanCertificate' Table ![![836, -206, -265, 141, 19]] 
 ![![17, 0, 0, 0, 0], ![11, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![14, 0, 0, 1, 0], ![10, 0, 0, 0, 1]] where
  M :=![![![836, -206, -265, 141, 19], ![-228, 449, -412, -492, 564], ![-6768, 416, 3689, 304, -1968], ![11922, -2900, -3826, 1967, 326], ![-4419, 1934, 359, -1721, 1124]]]
  hmulB := by decide  
  f := ![![![-1898, 1198, 219, 191, -241]], ![![-1058, 651, 133, 121, -111]], ![![-2214, 1266, 254, 241, -223]], ![![-1586, 768, 196, 209, -76]], ![![-1711, 794, 199, 217, -84]]]
  g := ![![![289, -206, -265, 141, 19], ![133, 449, -412, -492, 564], ![-3015, 416, 3689, 304, -1968], ![4142, -2900, -3826, 1967, 326], ![-1072, 1934, 359, -1721, 1124]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N2 : Nat.card (O ⧸ I17N2) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N2)

lemma isPrimeI17N2 : Ideal.IsPrime I17N2 := prime_ideal_of_norm_prime hp17.out _ NI17N2
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![13153, -8003, -1151, -966, 2058]] ![![2804, 1525, 164, -243, -455]]
  ![![1898, -1198, -219, -191, 241]] where
 M := ![![![1898, -1198, -219, -191, 241]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI17N1 : IdealMulLeCertificate' Table 
  ![![1898, -1198, -219, -191, 241]] ![![836, -206, -265, 141, 19]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-482, -251, -22, 47, 83]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-482, -251, -22, 47, 83]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![16, 8, 1, 1, 0], ![11, 0, 1, 0, 1]] where
  M :=![![![-482, -251, -22, 47, 83], ![-996, -468, -13, 122, 188], ![-2256, -943, 40, 350, 488], ![-2430, -805, 161, 467, 606], ![-3195, -1121, 188, 589, 758]]]
  hmulB := by decide  
  f := ![![![-63164, 38431, 5528, 4639, -9883]], ![![118596, -72158, -10379, -8710, 18556]], ![![-222672, 135483, 19486, 16354, -34840]], ![![-7094, 4316, 621, 521, -1110]], ![![-56287, 34247, 4926, 4134, -8807]]]
  g := ![![![-113, -33, -8, 47, 83], ![-264, -76, -17, 122, 188], ![-696, -197, -42, 350, 488], ![-872, -239, -48, 467, 606], ![-1103, -307, -61, 589, 758]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 3 2 4 [12, 11, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 10, 2], [1, 8, 17], [0, 1]]
 g := ![![[10, 4, 5], [6, 15, 6], [14, 1], []], ![[12, 18, 1, 12], [7, 14, 11, 14], [8, 7], [1, 4]], ![[3, 10, 8, 6], [18, 12, 10, 1], [2, 5], [5, 4]]]
 h' := ![![[13, 10, 2], [4, 10, 10], [3, 5, 14], [0, 0, 1], [0, 1]], ![[1, 8, 17], [13, 1, 5], [5, 14, 8], [5, 11, 8], [13, 10, 2]], ![[0, 1], [13, 8, 4], [18, 0, 16], [17, 8, 10], [1, 8, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 14], []]
 b := ![[], [18, 7, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 3
  hpos := by decide
  P := [12, 11, 5, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11821404, 156112, -7771394, -1911570, 5213756]
  a := ![0, -16, -10, -18, 28]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-786568, 813088, -582820, -1911570, 5213756]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 6859 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-58, 38, 3, 5, -9]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![-58, 38, 3, 5, -9]] 
 ![![19, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![13, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![-58, 38, 3, 5, -9], ![108, -69, -8, -12, 20], ![-240, 132, 35, 24, -48], ![234, -104, -50, -7, 38], ![-207, 106, 31, 3, -26]]]
  hmulB := by decide  
  f := ![![![5300, 3174, 485, -311, -743]], ![![1864, 1117, 171, -109, -261]], ![![4412, 2646, 406, -257, -617]], ![![1254, 758, 119, -70, -173]], ![![1793, 1082, 169, -101, -248]]]
  g := ![![![-14, 38, 3, 5, -9], ![27, -69, -8, -12, 20], ![-65, 132, 35, 24, -48], ![67, -104, -50, -7, 38], ![-55, 106, 31, 3, -26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1

def I19N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![407, -257, -37, -30, 66]] i)))

def SI19N2: IdealEqSpanCertificate' Table ![![407, -257, -37, -30, 66]] 
 ![![19, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![17, 0, 0, 0, 1]] where
  M :=![![![407, -257, -37, -30, 66], ![-792, 466, 67, 58, -120], ![1440, -903, -130, -106, 232], ![-996, 591, 85, 73, -152], ![978, -619, -89, -72, 159]]]
  hmulB := by decide  
  f := ![![![-55, 9, 15, -6, 2]], ![![-36, 4, 11, -2, 0]], ![![-8, 1, -4, -2, 8]], ![![-51, 8, 14, -5, 2]], ![![-47, 0, 14, 2, 1]]]
  g := ![![![145, -257, -37, -30, 66], ![-266, 466, 67, 58, -120], ![510, -903, -130, -106, 232], ![-337, 591, 85, 73, -152], ![349, -619, -89, -72, 159]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N2 : Nat.card (O ⧸ I19N2) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N2)

lemma isPrimeI19N2 : Ideal.IsPrime I19N2 := prime_ideal_of_norm_prime hp19.out _ NI19N2
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-482, -251, -22, 47, 83]] ![![-58, 38, 3, 5, -9]]
  ![![-55, 9, 15, -6, 2]] where
 M := ![![![-55, 9, 15, -6, 2]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI19N1 : IdealMulLeCertificate' Table 
  ![![-55, 9, 15, -6, 2]] ![![407, -257, -37, -30, 66]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0, 0]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0, 0, 0]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]] where
  M :=![![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 5 2 4 [2, 0, 15, 4, 2, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 9, 8, 12, 11], [4, 12, 8, 16, 7], [2, 17, 0, 14, 5], [22, 7, 7, 4], [0, 1]]
 g := ![![[15, 19, 19, 0, 9], [11, 9, 21, 8, 4], [1], []], ![[11, 9, 2, 18, 21, 1, 13, 7], [4, 21, 8, 22, 15, 2, 20, 7], [8, 3, 15, 0, 1, 4, 18, 10], [7, 22, 22, 6]], ![[0, 21, 2, 20, 11, 14, 1, 14], [2, 18, 9, 12, 22, 13, 17, 20], [0, 20, 0, 22, 1, 22, 21, 15], [12, 12, 11, 3]], ![[13, 3, 14, 6, 11, 16, 1, 22], [18, 6, 8, 14, 6, 5], [20, 4, 4, 16, 17, 20], [17, 8, 21, 2]], ![[0, 11, 15, 16, 9, 12, 16], [7, 1, 20, 2, 0, 4, 8], [21, 0, 4, 22, 4, 19, 12], [1, 16]]]
 h' := ![![[16, 9, 8, 12, 11], [1, 9, 0, 3, 3], [21, 0, 8, 19, 21], [0, 0, 1], [0, 1]], ![[4, 12, 8, 16, 7], [19, 7, 16, 19, 20], [11, 19, 4, 17, 3], [12, 14, 4, 20, 16], [16, 9, 8, 12, 11]], ![[2, 17, 0, 14, 5], [9, 10, 13, 20, 5], [3, 7, 2, 10, 4], [15, 3, 6, 17, 14], [4, 12, 8, 16, 7]], ![[22, 7, 7, 4], [22, 1, 15, 5, 20], [12, 13, 9, 22], [16, 6, 15, 2], [2, 17, 0, 14, 5]], ![[0, 1], [0, 19, 2, 22, 21], [3, 7, 0, 1, 18], [22, 0, 20, 7, 16], [22, 7, 7, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 9, 5, 4], [], [], []]
 b := ![[], [6, 16, 2, 11, 8], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 5
  hpos := by decide
  P := [2, 0, 15, 4, 2, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1422884722404, 407296409328, -322006060224, -417994125076, -213626323920]
  a := ![13, 8, 11, 2, -29]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![61864553148, 17708539536, -14000263488, -18173657612, -9288101040]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 6436343 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def PBC23 : ContainsPrimesAboveP 23 ![I23N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![23, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 23 (by decide) 𝕀



lemma PB1705I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB1705I0 : PrimesBelowBoundCertificateInterval O 1 23 1705 where
  m := 9
  g := ![5, 4, 5, 2, 2, 2, 3, 3, 1]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB1705I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N1, I3N1, I3N1]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1]
    · exact ![I17N0, I17N1, I17N2]
    · exact ![I19N0, I19N1, I19N2]
    · exact ![I23N0]
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
    · exact ![2401, 7]
    · exact ![14641, 11]
    · exact ![28561, 13]
    · exact ![4913, 17, 17]
    · exact ![6859, 19, 19]
    · exact ![6436343]
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
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I5N0, I7N1, I11N1, I13N1, I17N1, I17N2, I19N1, I19N2]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N1, I3N1, I3N1], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N1], [I11N1], [I13N1], [I17N1, I17N2], [I19N1, I19N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
