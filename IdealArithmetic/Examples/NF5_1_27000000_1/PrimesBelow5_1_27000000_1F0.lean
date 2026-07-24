
import IdealArithmetic.Examples.NF5_1_27000000_1.RI5_1_27000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, -1, -2, -1, -1]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![3, -1, -2, -1, -1]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![3, -1, -2, -1, -1], ![8, 2, -2, -1, -2], ![4, 4, 2, 1, 0], ![-4, 3, 4, 2, 2], ![2, 7, 5, 2, 1]]]
  hmulB := by decide  
  f := ![![![2, -1, 1, 0, 0]], ![![0, 1, -1, 1, 0]], ![![1, -2, 1, -2, 1]], ![![-4, 1, 2, 0, -2]], ![![7, -1, 0, 3, 0]]]
  g := ![![![3, -1, -2, -1, -1], ![6, 2, -2, -1, -2], ![1, 4, 2, 1, 0], ![-5, 3, 4, 2, 2], ![-2, 7, 5, 2, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![554, 457, 148, 66, -47]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![554, 457, 148, 66, -47]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![554, 457, 148, 66, -47], ![376, 1027, 688, 324, 132], ![-716, 208, 491, 232, 258], ![-1220, -754, -110, -45, 166], ![-1614, -139, 581, 280, 428]]]
  hmulB := by decide  
  f := ![![![-866, -53, -11, -632, 173]], ![![-692, 167, 752, 132, -632]], ![![2874, -102, -973, 1252, 448]], ![![-1446, -436, -1282, -2113, 1568]], ![![-4813, 378, 2383, -1466, -1513]]]
  g := ![![![277, 457, 148, 66, -47], ![188, 1027, 688, 324, 132], ![-358, 208, 491, 232, 258], ![-610, -754, -110, -45, 166], ![-807, -139, 581, 280, 428]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 0, 0, -1, 0]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![-1, 0, 0, -1, 0]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-1, 0, 0, -1, 0], ![0, 1, 2, 1, -2], ![8, 0, -3, 3, 2], ![-8, -1, -2, -7, 4], ![-12, 2, 8, -2, -5]]]
  hmulB := by decide  
  f := ![![![30, -17, 8, -5, 6]], ![![-9, 7, -2, 2, -2]], ![![47, -28, 13, -8, 10]], ![![-1, 0, 0, 0, 0]], ![![12, -8, 4, -2, 3]]]
  g := ![![![0, 0, 0, -1, 0], ![-2, 1, 2, 1, -2], ![4, 0, -3, 3, 2], ![1, -1, -2, -7, 4], ![-10, 2, 8, -2, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![3, -1, -2, -1, -1]] ![![554, 457, 148, 66, -47]]
  ![![5552, 821, -1697, -825, -1383]] where
 M := ![![![5552, 821, -1697, -825, -1383]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![5552, 821, -1697, -825, -1383]] ![![554, 457, 148, 66, -47]]
  ![![7838218, 3841742, -159456, -111383, -1319272]] where
 M := ![![![7838218, 3841742, -159456, -111383, -1319272]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![7838218, 3841742, -159456, -111383, -1319272]] ![![-1, 0, 0, -1, 0]]
  ![![7608462, 1314581, -2169558, -1056619, -1851568]] where
 M := ![![![7608462, 1314581, -2169558, -1056619, -1851568]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![7608462, 1314581, -2169558, -1056619, -1851568]] ![![-1, 0, 0, -1, 0]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![5706842, -1331936, -3561470, -1703086, -1936914]]]
 hmul := by decide  
 g := ![![![![2853421, -665968, -1780735, -851543, -968457]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, -36, -160, -34, 136]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![139, -36, -160, -34, 136]] 
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![139, -36, -160, -34, 136], ![-1088, 11, 268, -558, -68], ![816, 148, 367, 894, -524], ![2640, -234, -1404, 723, 928], ![-2664, -180, -96, -1996, 595]]]
  hmulB := by decide  
  f := ![![![265, 32, 56, -10, 8]], ![![67, 135, 52, 32, -4]], ![![214, -8, 103, -2, 44]], ![![-144, -30, -12, 7, 8]], ![![-88, -20, 64, 20, 43]]]
  g := ![![![165, -36, -160, -34, 136], ![-545, 11, 268, -558, -68], ![-22, 148, 367, 894, -524], ![1894, -234, -1404, 723, 928], ![-764, -180, -96, -1996, 595]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9, -8, -27, -29, 29]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![-9, -8, -27, -29, 29]] 
 ![![3, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-9, -8, -27, -29, 29], ![-232, 14, 100, -83, -58], ![348, 17, -11, 241, -54], ![332, -71, -328, -36, 270], ![-798, -2, 160, -440, -13]]]
  hmulB := by decide  
  f := ![![![-3893, 2350, -1035, 677, -809]], ![![-438, 256, -114, 75, -88]], ![![-2884, 1743, -771, 501, -602]], ![![-1266, 765, -338, 220, -264]], ![![-2461, 1486, -659, 427, -514]]]
  g := ![![![12, -8, -27, -29, 29], ![-12, 14, 100, -83, -58], ![-38, 17, -11, 241, -54], ![92, -71, -328, -36, 270], ![33, -2, 160, -440, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![139, -36, -160, -34, 136]] ![![-9, -8, -27, -29, 29]]
  ![![-168395, -2194, 27319, -98219, 3811]] where
 M := ![![![-168395, -2194, 27319, -98219, 3811]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N1 : IdealMulLeCertificate' Table 
  ![![-168395, -2194, 27319, -98219, 3811]] ![![-9, -8, -27, -29, 29]]
  ![![-24118311, 8746794, 36852348, 13508480, -32800102]] where
 M := ![![![-24118311, 8746794, 36852348, 13508480, -32800102]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![-24118311, 8746794, 36852348, 13508480, -32800102]] ![![-9, -8, -27, -29, 29]]
  ![![41671722451, 48389644, -8558299791, 22800602585, 876919063]] where
 M := ![![![41671722451, 48389644, -8558299791, 22800602585, 876919063]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N3 : IdealMulLeCertificate' Table 
  ![![41671722451, 48389644, -8558299791, 22800602585, 876919063]] ![![-9, -8, -27, -29, 29]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![3505458419211, -2098784042700, -8364446841876, -4481712621942, 7812584290572]]]
 hmul := by decide  
 g := ![![![![1168486139737, -699594680900, -2788148947292, -1493904207314, 2604194763524]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N1, I3N1, I3N1, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N1
    exact isPrimeI3N1
    exact isPrimeI3N1
    exact isPrimeI3N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1 ⊙ MulI3N2 ⊙ MulI3N3)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 5, 7, 44, -17]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![53, 5, 7, 44, -17]] 
 ![![5, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![53, 5, 7, 44, -17], ![136, -23, -112, 4, 88], ![-420, 8, 117, -204, -40], ![92, 68, 228, 257, -248], ![754, -44, -318, 276, 181]]]
  hmulB := by decide  
  f := ![![![-81, -87, -67, -24, -13]], ![![-44, -107, -84, -36, -20]], ![![28, 12, -15, -4, -12]], ![![-11, -17, -21, -7, -7]], ![![32, -4, -34, -12, -19]]]
  g := ![![![-13, 5, 7, 44, -17], ![8, -23, -112, 4, 88], ![48, 8, 117, -204, -40], ![-91, 68, 228, 257, -248], ![-52, -44, -318, 276, 181]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![53, 5, 7, 44, -17]] ![![53, 5, 7, 44, -17]]
  ![![-8221, 3946, 16068, 7540, -14730]] where
 M := ![![![-8221, 3946, 16068, 7540, -14730]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![-8221, 3946, 16068, 7540, -14730]] ![![53, 5, 7, 44, -17]]
  ![![-17060357, 1157521, 7783717, -5751512, -4691765]] where
 M := ![![![-17060357, 1157521, 7783717, -5751512, -4691765]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![-17060357, 1157521, 7783717, -5751512, -4691765]] ![![53, 5, 7, 44, -17]]
  ![![-8082667119, -234320188, 842266572, -5106969616, 657704748]] where
 M := ![![![-8082667119, -234320188, 842266572, -5106969616, 657704748]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![-8082667119, -234320188, 842266572, -5106969616, 657704748]] ![![53, 5, 7, 44, -17]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![-787932687795, -404498781495, -1305328802165, -1659361695540, 1468667525755]]]
 hmul := by decide  
 g := ![![![![-157586537559, -80899756299, -261065760433, -331872339108, 293733505151]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-159, 92, 145, 69, 67]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![-159, 92, 145, 69, 67]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![3, 0, 3, 1, 0], ![3, 2, 2, 0, 1]] where
  M :=![![![-159, 92, 145, 69, 67], ![-536, -60, 180, 87, 138], ![-284, -265, -99, -45, 18], ![196, -249, -292, -138, -114], ![-266, -484, -290, -136, -39]]]
  hmulB := by decide  
  f := ![![![-1047, 634, -279, 183, -219]], ![![1752, -1058, 464, -303, 366]], ![![-2340, 1411, -621, 401, -486]], ![![-1299, 784, -344, 224, -271]], ![![-749, 454, -201, 131, -156]]]
  g := ![![![-81, -6, -28, 69, 67], ![-173, -48, -51, 87, 138], ![-29, -43, 0, -45, 18], ![136, -3, 50, -138, -114], ![37, -58, 28, -136, -39]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 3 2 2 [6, 3, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 4], [1, 2], [0, 1]]
 g := ![![[3, 5, 2], [1]], ![[1, 5, 4], [1]], ![[3, 4, 1], [1]]]
 h' := ![![[3, 4], [1, 4, 4], [0, 1]], ![[1, 2], [0, 0, 1], [3, 4]], ![[0, 1], [2, 3, 2], [1, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3], []]
 b := ![[], [6, 5, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 3
  hpos := by decide
  P := [6, 3, 3, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2579676, -182026, -1002337, 1056815, 464171]
  a := ![0, 8, 5, -1, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-283326, -158624, -728732, 1056815, 464171]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 343 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1047, 634, -279, 183, -219]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![-1047, 634, -279, 183, -219]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![5, 5, 1, 0, 0], ![3, 5, 0, 1, 0], ![6, 3, 0, 0, 1]] where
  M :=![![![-1047, 634, -279, 183, -219], ![1752, -1058, 464, -303, 366], ![-2340, 1411, -621, 401, -486], ![1068, -647, 292, -184, 218], ![-926, 570, -256, 172, -195]]]
  hmulB := by decide  
  f := ![![![-159, 92, 145, 69, 67]], ![![-536, -60, 180, 87, 138]], ![![-537, -15, 218, 105, 149]], ![![-423, -39, 149, 72, 111]], ![![-404, -16, 160, 77, 111]]]
  g := ![![![159, 253, -279, 183, -219], ![-265, -423, 464, -303, 366], ![354, 567, -621, 401, -486], ![-164, -263, 292, -184, 218], ![144, 225, -256, 172, -195]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P1 : CertificateIrreducibleZModOfList' 7 2 2 2 [5, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 6], [0, 1]]
 g := ![![[1, 1], [2, 1]], ![[3, 6], [4, 6]]]
 h' := ![![[2, 6], [4, 6], [0, 1]], ![[0, 1], [2, 1], [2, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [6, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N1 : CertifiedPrimeIdeal' SI7N1 7 where
  n := 2
  hpos := by decide
  P := [5, 5, 1]
  hirr := P7P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-39531, -8669, -2182, -26615, 4650]
  a := ![3, -5, -3, -1, -52]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3332, 17338, -2182, -26615, 4650]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N1 B_one_repr
lemma NI7N1 : Nat.card (O ⧸ I7N1) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![-159, 92, 145, 69, 67]] ![![-1047, 634, -279, 183, -219]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![46143, -27921, 12308, -8029, 9624]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![46143, -27921, 12308, -8029, 9624]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![4, 8, 10, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![46143, -27921, 12308, -8029, 9624], ![-76992, 46588, -20536, 13397, -16058], ![102728, -62161, 27401, -17875, 21426], ![-47208, 28565, -12592, 8214, -9846], ![41516, -25122, 11074, -7224, 8659]]]
  hmulB := by decide  
  f := ![![![-3, -5, -4, -7, -4]], ![![32, 2, -4, 7, -14]], ![![40, 7, -17, 3, 14]], ![![52, 7, -18, 2, 2]], ![![-2, 0, 2, -2, -5]]]
  g := ![![![1865, 3301, 8418, -8029, 9624], ![-3112, -5508, -14046, 13397, -16058], ![4152, 7349, 18741, -17875, 21426], ![-1908, -3377, -8612, 8214, -9846], ![1678, 2970, 7574, -7224, 8659]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [5, 1, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 6, 5], [4, 4, 6], [0, 1]]
 g := ![![[3, 1, 3], [10, 0, 1], []], ![[7, 2, 6, 3], [3, 3, 5, 3], [5, 3]], ![[4, 4, 6, 2], [7, 2, 2, 7], [4, 3]]]
 h' := ![![[7, 6, 5], [5, 1, 6], [0, 0, 1], [0, 1]], ![[4, 4, 6], [2, 5, 7], [2, 9, 4], [7, 6, 5]], ![[0, 1], [7, 5, 9], [7, 2, 6], [4, 4, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 4], []]
 b := ![[], [0, 10, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [5, 1, 0, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![351133, -26428, -135786, 146918, 62578]
  a := ![1, 3, 2, -1, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-55637, -109252, -145906, 146918, 62578]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 1331 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-260811, 157817, -69567, 45382, -54397]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![-260811, 157817, -69567, 45382, -54397]] 
 ![![11, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-260811, 157817, -69567, 45382, -54397], ![435176, -263325, 116076, -75722, 90764], ![-580644, 351348, -154877, 101034, -121104], ![266828, -161458, 71172, -46429, 55652], ![-234662, 141994, -62592, 40832, -48943]]]
  hmulB := by decide  
  f := ![![![-47, -1, -15, -62, 17]], ![![-38, 5, 6, -34, -2]], ![![47, 1, -14, 20, 7]], ![![-37, -9, -33, -59, 39]], ![![-94, 8, 42, -32, -21]]]
  g := ![![![-124096, 157817, -69567, 45382, -54397], ![207060, -263325, 116076, -75722, 90764], ![-276275, 351348, -154877, 101034, -121104], ![126959, -161458, 71172, -46429, 55652], ![-111654, 141994, -62592, 40832, -48943]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1

def I11N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![57, 1, -6, 35, -4]] i)))

def SI11N2: IdealEqSpanCertificate' Table ![![57, 1, -6, 35, -4]] 
 ![![11, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![10, 0, 0, 0, 1]] where
  M :=![![![57, 1, -6, 35, -4], ![32, -18, -76, -39, 70], ![-296, 17, 129, -107, -74], ![280, 41, 88, 276, -142], ![444, -52, -280, 84, 201]]]
  hmulB := by decide  
  f := ![![![-325, -699, -442, -207, -72]], ![![-184, -604, -424, -199, -90]], ![![-112, -485, -355, -167, -82]], ![![-144, -387, -260, -122, -50]], ![![-82, -538, -412, -194, -103]]]
  g := ![![![-13, 1, -6, 35, -4], ![36, -18, -76, -39, 70], ![12, 17, 129, -107, -74], ![-140, 41, 88, 276, -142], ![38, -52, -280, 84, 201]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N2 : Nat.card (O ⧸ I11N2) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N2)

lemma isPrimeI11N2 : Ideal.IsPrime I11N2 := prime_ideal_of_norm_prime hp11.out _ NI11N2
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![46143, -27921, 12308, -8029, 9624]] ![![-260811, 157817, -69567, 45382, -54397]]
  ![![-35732466521, 21621734878, -9531039589, 6217567669, -7452667787]] where
 M := ![![![-35732466521, 21621734878, -9531039589, 6217567669, -7452667787]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI11N1 : IdealMulLeCertificate' Table 
  ![![-35732466521, 21621734878, -9531039589, 6217567669, -7452667787]] ![![57, 1, -6, 35, -4]]
  ![![11, 0, 0, 0, 0]] where
 M := ![![![-91732907365, 55507632015, -24468223351, 15961830082, -19132597055]]]
 hmul := by decide  
 g := ![![![![-8339355215, 5046148365, -2224383941, 1451075462, -1739327005]]]]
 hle2 := by decide  


def PBC11 : ContainsPrimesAboveP 11 ![I11N0, I11N1, I11N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
    exact isPrimeI11N1
    exact isPrimeI11N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 11 (by decide) (𝕀 ⊙ MulI11N0 ⊙ MulI11N1)
instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-791, 477, -209, 136, -165]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-791, 477, -209, 136, -165]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![8, 2, 6, 1, 0], ![8, 9, 7, 0, 1]] where
  M :=![![![-791, 477, -209, 136, -165], ![1320, -795, 352, -224, 272], ![-1748, 1060, -475, 304, -360], ![780, -488, 220, -155, 168], ![-710, 432, -178, 132, -159]]]
  hmulB := by decide  
  f := ![![![-69, -87, -43, -20, -1]], ![![8, -159, -136, -64, -40]], ![![156, 0, -67, -32, -44]], ![![44, -66, -74, -35, -28]], ![![70, -157, -161, -76, -57]]]
  g := ![![![-43, 130, 10, 136, -165], ![72, -215, -16, -224, 272], ![-100, 284, 17, 304, -360], ![52, -130, -2, -155, 168], ![-38, 123, 11, 132, -159]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [12, 4, 11, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 11, 10], [4, 1, 3], [0, 1]]
 g := ![![[11, 6, 1], [5, 4], [1]], ![[9, 0, 9, 3], [9, 1], [7, 10, 9, 12]], ![[10, 8, 6, 9], [2, 9], [1, 2, 3, 1]]]
 h' := ![![[11, 11, 10], [6, 2, 1], [1, 9, 2], [0, 1]], ![[4, 1, 3], [10, 10, 8], [12, 10, 1], [11, 11, 10]], ![[0, 1], [2, 1, 4], [0, 7, 10], [4, 1, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 4], []]
 b := ![[], [5, 1, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [12, 4, 11, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16254496, 1413443, 7526757, -5756178, -4339001]
  a := ![1, -11, -7, -1, 47]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![4962072, 3998216, 5572064, -5756178, -4339001]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 2197 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 6, 2, 2, 0]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![-3, 6, 2, 2, 0]] 
 ![![13, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![-3, 6, 2, 2, 0], ![0, 1, 8, 2, 4], ![-16, 2, -1, 2, 0], ![0, -10, -4, -3, 0], ![-16, -6, -2, 0, 1]]]
  hmulB := by decide  
  f := ![![![-15, 2, 10, -2, -8]], ![![-2, 1, 4, 2, -4]], ![![-7, 0, 1, -4, 0]], ![![-24, 2, 12, -7, -8]], ![![4, 2, 6, 8, -7]]]
  g := ![![![-5, 6, 2, 2, 0], ![-6, 1, 8, 2, 4], ![-3, 2, -1, 2, 0], ![8, -10, -4, -3, 0], ![2, -6, -2, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1

def I13N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, 1, -3, -2, -3]] i)))

def SI13N2: IdealEqSpanCertificate' Table ![![9, 1, -3, -2, -3]] 
 ![![13, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![9, 1, -3, -2, -3], ![24, 11, 0, 2, -4], ![4, 10, 5, 2, 4], ![-28, 2, 12, -1, 4], ![-2, 16, 18, 12, 1]]]
  hmulB := by decide  
  f := ![![![-8357, 5057, -2229, 1454, -1743]], ![![-4713, 2852, -1257, 820, -983]], ![![-5931, 3589, -1582, 1032, -1237]], ![![-1271, 769, -339, 221, -265]], ![![-3150, 1906, -840, 548, -657]]]
  g := ![![![3, 1, -3, -2, -3], ![-5, 11, 0, 2, -4], ![-11, 10, 5, 2, 4], ![-11, 2, 12, -1, 4], ![-24, 16, 18, 12, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N2 : Nat.card (O ⧸ I13N2) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N2)

lemma isPrimeI13N2 : Ideal.IsPrime I13N2 := prime_ideal_of_norm_prime hp13.out _ NI13N2
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-791, 477, -209, 136, -165]] ![![-3, 6, 2, 2, 0]]
  ![![8357, -5057, 2229, -1454, 1743]] where
 M := ![![![8357, -5057, 2229, -1454, 1743]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI13N1 : IdealMulLeCertificate' Table 
  ![![8357, -5057, 2229, -1454, 1743]] ![![9, 1, -3, -2, -3]]
  ![![13, 0, 0, 0, 0]] where
 M := ![![![-13, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-280207, 169553, -74740, 48757, -58442]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![-280207, 169553, -74740, 48757, -58442]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![1, 3, 15, 13, 1]] where
  M :=![![![-280207, 169553, -74740, 48757, -58442], ![467536, -282908, 124708, -81353, 97514], ![-623824, 377475, -166395, 108547, -130110], ![286672, -173465, 76464, -49882, 59790], ![-252112, 152552, -67248, 43868, -52583]]]
  hmulB := by decide  
  f := ![![![1, -5, -8, -3, 6]], ![![-48, -6, 8, -25, -6]], ![![48, 5, 9, 39, -22]], ![![112, -5, -60, 24, 42]], ![![113, -1, -37, 43, 13]]]
  g := ![![![-13045, 20287, 47170, 47559, -58442], ![21766, -33850, -78706, -79355, 97514], ![-29042, 45165, 105015, 105881, -130110], ![13346, -20755, -48258, -48656, 59790], ![-11737, 18253, 42441, 42791, -52583]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 4 2 4 [6, 0, 9, 15, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 9, 14, 2], [4, 12, 14, 1], [15, 12, 6, 14], [0, 1]]
 g := ![![[0, 7, 9, 4], [6, 6, 4], [1], []], ![[5, 12, 13, 0, 11, 16], [4, 10, 2], [6, 13, 1], [1, 13, 4]], ![[6, 15, 4, 8, 14, 1], [6, 6, 4], [8, 13, 16], [16, 13, 1]], ![[11, 13, 3, 9, 6, 3], [4, 10, 2], [16, 2, 8], [0, 16, 9]]]
 h' := ![![[0, 9, 14, 2], [0, 15, 13, 2], [11, 0, 8, 2], [0, 0, 1], [0, 1]], ![[4, 12, 14, 1], [10, 8, 16, 12], [0, 8, 8, 11], [11, 7, 14, 1], [0, 9, 14, 2]], ![[15, 12, 6, 14], [0, 15, 1, 16], [11, 0, 9, 15], [5, 1, 4, 4], [4, 12, 14, 1]], ![[0, 1], [1, 13, 4, 4], [5, 9, 9, 6], [4, 9, 15, 12], [15, 12, 6, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [13, 4, 3], []]
 b := ![[], [], [2, 14, 10, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 4
  hpos := by decide
  P := [6, 0, 9, 15, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-29150255, 149302897, 569414605, 459799162, -576246550]
  a := ![-1, 13, 9, 2, -30]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![32182135, 110473091, 541947815, 467706136, -576246550]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 83521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 5, 8, 3, -6]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![-1, 5, 8, 3, -6]] 
 ![![17, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  M :=![![![-1, 5, 8, 3, -6], ![48, 6, -8, 25, 6], ![-48, -5, -9, -39, 22], ![-112, 5, 60, -24, -42], ![112, 4, 0, 88, -17]]]
  hmulB := by decide  
  f := ![![![280207, -169553, 74740, -48757, 58442]], ![![104360, -63148, 27836, -18159, 21766]], ![![283937, -171810, 75735, -49406, 59220]], ![![49068, -29691, 13088, -8538, 10234]], ![![163175, -98737, 43524, -28393, 34033]]]
  g := ![![![-7, 5, 8, 3, -6], ![-2, 6, -8, 25, 6], ![5, -5, -9, -39, 22], ![-34, 5, 60, -24, -42], ![-7, 4, 0, 88, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![-280207, 169553, -74740, 48757, -58442]] ![![-1, 5, 8, 3, -6]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9, 1, 3, -4, -1]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-9, 1, 3, -4, -1]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![7, 15, 10, 1, 0], ![0, 15, 14, 0, 1]] where
  M :=![![![-9, 1, 3, -4, -1], ![8, 3, 8, 12, -8], ![28, -4, -21, 4, 16], ![-68, -4, 4, -45, 8], ![-30, 8, 38, 12, -33]]]
  hmulB := by decide  
  f := ![![![-5, 3, -5, 0, -3]], ![![24, -7, 0, -4, 0]], ![![-12, 16, -3, 4, -4]], ![![11, 4, -3, -1, -3]], ![![10, 7, -2, 0, -3]]]
  g := ![![![1, 4, 3, -4, -1], ![-4, -3, 0, 12, -8], ![0, -16, -15, 4, 16], ![13, 29, 18, -45, 8], ![-6, 17, 20, 12, -33]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 3 2 4 [10, 15, 18, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 13, 3], [14, 5, 16], [0, 1]]
 g := ![![[7, 2, 9], [1, 3, 6], [1, 1], []], ![[13, 18, 4, 12], [9, 3, 12, 14], [4, 6], [11, 9]], ![[17, 16, 7, 1], [2, 4, 5, 5], [7, 17], [17, 9]]]
 h' := ![![[6, 13, 3], [9, 17, 16], [9, 13, 5], [0, 0, 1], [0, 1]], ![[14, 5, 16], [10, 5, 17], [2, 16, 7], [2, 15, 5], [6, 13, 3]], ![[0, 1], [17, 16, 5], [17, 9, 7], [7, 4, 13], [14, 5, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 18], []]
 b := ![[], [4, 1, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 3
  hpos := by decide
  P := [10, 15, 18, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![104074, 20130, 65158, 122690, -81144]
  a := ![0, -10, -6, -10, 8]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-39724, -31740, -1354, 122690, -81144]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 6859 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, 3, -5, 0, -3]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![-5, 3, -5, 0, -3]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![12, 10, 1, 0, 0], ![13, 16, 0, 1, 0], ![7, 14, 0, 0, 1]] where
  M :=![![![-5, 3, -5, 0, -3], ![24, -7, 0, -4, 0], ![-12, 16, -3, 4, -4], ![4, 0, 8, 1, 4], ![-2, 14, 4, 4, -1]]]
  hmulB := by decide  
  f := ![![![-9, 1, 3, -4, -1]], ![![8, 3, 8, 12, -8]], ![![0, 2, 5, 4, -4]], ![![-3, 3, 9, 5, -7]], ![![1, 3, 9, 8, -8]]]
  g := ![![![4, 5, -5, 0, -3], ![4, 3, 0, -4, 0], ![0, 2, -3, 4, -4], ![-7, -8, 8, 1, 4], ![-5, -4, 4, 4, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P1 : CertificateIrreducibleZModOfList' 19 2 2 4 [13, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 18], [0, 1]]
 g := ![![[5, 16], [], [7], [1]], ![[10, 3], [], [7], [1]]]
 h' := ![![[11, 18], [0, 4], [2], [6, 11], [0, 1]], ![[0, 1], [6, 15], [2], [13, 8], [11, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [12, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N1 : CertifiedPrimeIdeal' SI19N1 19 where
  n := 2
  hpos := by decide
  P := [13, 8, 1]
  hirr := P19P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6568, -982, -1196, -6590, 1006]
  a := ![13, 10, 7, 1, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![4548, 5386, -1196, -6590, 1006]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N1 B_one_repr
lemma NI19N1 : Nat.card (O ⧸ I19N1) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-9, 1, 3, -4, -1]] ![![-5, 3, -5, 0, -3]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0, 0]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0, 0, 0]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]] where
  M :=![![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 5 2 4 [13, 2, 12, 2, 1, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 18, 19, 18, 9], [14, 12, 5, 18, 3], [19, 15, 0, 18, 15], [10, 0, 22, 15, 19], [0, 1]]
 g := ![![[14, 18, 7, 18, 1], [14, 11, 0, 3, 1], [1], []], ![[18, 8, 19, 14, 8, 3, 17, 2], [18, 9, 8, 18, 21, 3, 14, 2], [3, 18, 19, 16, 13, 9, 10, 6], [2, 8, 13, 12]], ![[10, 0, 3, 16, 3, 13, 6, 4], [17, 22, 18, 1, 12, 19, 12, 9], [21, 4, 22, 16, 16, 1, 10, 4], [8, 7, 7, 9]], ![[6, 12, 15, 15, 14, 12, 10, 15], [3, 9, 22, 9, 1, 1, 10, 15], [15, 21, 6, 15, 18, 0, 2, 11], [22, 19, 16, 18]], ![[7, 0, 17, 14, 4, 7, 18, 22], [22, 5, 13, 13, 20, 6, 10, 14], [7, 3, 14, 9, 8, 8, 21, 11], [12, 15, 2, 16]]]
 h' := ![![[2, 18, 19, 18, 9], [2, 21, 0, 2, 22], [10, 21, 11, 21, 22], [0, 0, 1], [0, 1]], ![[14, 12, 5, 18, 3], [20, 20, 12, 12, 17], [9, 2, 12, 18, 6], [1, 10, 7, 14, 19], [2, 18, 19, 18, 9]], ![[19, 15, 0, 18, 15], [20, 11, 5, 11, 20], [3, 21, 20, 14, 7], [0, 22, 14, 2, 3], [14, 12, 5, 18, 3]], ![[10, 0, 22, 15, 19], [1, 1, 13, 22, 22], [6, 1, 15, 1, 1], [6, 3, 14, 8, 17], [19, 15, 0, 18, 15]], ![[0, 1], [4, 16, 16, 22, 11], [12, 1, 11, 15, 10], [13, 11, 10, 22, 7], [10, 0, 22, 15, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20, 4, 22, 17], [], [], []]
 b := ![[], [20, 14, 22, 2, 16], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 5
  hpos := by decide
  P := [13, 2, 12, 2, 1, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1083860809, 20580515, -155507761, 648494062, -44187209]
  a := ![-1, -5, -3, -1, 9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![47124383, 894805, -6761207, 28195394, -1921183]
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



lemma PB324I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB324I0 : PrimesBelowBoundCertificateInterval O 1 23 324 where
  m := 9
  g := ![5, 5, 5, 2, 3, 3, 2, 2, 1]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB324I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N1, I3N1, I3N1, I3N1]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1]
    · exact ![I11N0, I11N1, I11N2]
    · exact ![I13N0, I13N1, I13N2]
    · exact ![I17N0, I17N1]
    · exact ![I19N0, I19N1]
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
    · exact ![3, 3, 3, 3, 3]
    · exact ![5, 5, 5, 5, 5]
    · exact ![343, 49]
    · exact ![1331, 11, 11]
    · exact ![2197, 13, 13]
    · exact ![83521, 17]
    · exact ![6859, 361]
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
      exact NI11N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I5N0, I7N1, I11N1, I11N2, I13N1, I13N2, I17N1]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N1, I3N1, I3N1, I3N1], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N1], [I11N1, I11N2], [I13N1, I13N2], [I17N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
