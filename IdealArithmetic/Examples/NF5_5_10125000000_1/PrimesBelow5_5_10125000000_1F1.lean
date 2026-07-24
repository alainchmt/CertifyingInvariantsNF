
import IdealArithmetic.Examples.NF5_5_10125000000_1.RI5_5_10125000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37019, -27335, -30042, -2449, 3405]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![37019, -27335, -30042, -2449, 3405]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![11, 22, 1, 0, 0], ![19, 26, 0, 1, 0], ![20, 11, 0, 0, 1]] where
  M :=![![![37019, -27335, -30042, -2449, 3405], ![-107048, 78387, 86428, 7060, -9796], ![207524, -152352, -167807, -13694, 19018], ![-245440, 180250, 198488, 16181, -22490], ![200658, -147174, -162126, -13206, 18365]]]
  hmulB := by decide  
  f := ![![![11001, -15035, -18460, -11001, -4415]], ![![110448, -150529, -184668, -109804, -44004]], ![![105031, -143179, -175663, -104469, -41871]], ![![189539, -258405, -317040, -188562, -75579]], ![![286458, -390615, -479278, -285100, -114285]]]
  g := ![![![11928, 22752, -30042, -2449, 3405], ![-34344, -65477, 86428, 7060, -9796], ![66663, 127112, -167807, -13694, 19018], ![-78843, -150338, 198488, 16181, -22490], ![64402, 122791, -162126, -13206, 18365]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [15, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 28], [0, 1]]
 g := ![![[], [5], [0, 22], [0, 1]], ![[], [5], [0, 7], [0, 28]]]
 h' := ![![[0, 28], [12], [0, 18], [0, 14], [0, 1]], ![[0, 1], [12], [0, 11], [0, 15], [0, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [0, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [15, 0, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-784926, 1677270, 1909757, 1484182, 888048]
  a := ![-25, -17, 5, -1, -50]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2336299, -3058436, 1909757, 1484182, 888048]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5363, -3987, -3708, -243, 408]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![5363, -3987, -3708, -243, 408]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![6, 15, 1, 0, 0], ![26, 18, 0, 1, 0], ![14, 4, 0, 0, 1]] where
  M :=![![![5363, -3987, -3708, -243, 408], ![-12726, 9500, 8832, 579, -972], ![21522, -16041, -14935, -981, 1644], ![-19278, 14361, 13404, 884, -1476], ![14772, -11016, -10284, -678, 1133]]]
  hmulB := by decide  
  f := ![![![2671, -1989, -2808, -711, 480]], ![![-15822, 11794, 16644, 4215, -2844]], ![![-5742, 4281, 6041, 1530, -1032]], ![![-12752, 9507, 13416, 3398, -2292]], ![![6562, -4888, -6900, -1746, 1181]]]
  g := ![![![973, 1875, -3708, -243, 408], ![-2316, -4466, 8832, 579, -972], ![3918, 7554, -14935, -981, 1644], ![-3518, -6783, 13404, 884, -1476], ![2698, 5204, -10284, -678, 1133]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P1 : CertificateIrreducibleZModOfList' 29 2 2 4 [16, 27, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 28], [0, 1]]
 g := ![![[18, 20], [23], [12, 28], [2, 1]], ![[0, 9], [23], [10, 1], [4, 28]]]
 h' := ![![[2, 28], [14, 22], [11, 20], [26, 17], [0, 1]], ![[0, 1], [0, 7], [22, 9], [2, 12], [2, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [28, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N1 : CertifiedPrimeIdeal' SI29N1 29 where
  n := 2
  hpos := by decide
  P := [16, 27, 1]
  hirr := P29P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1849692, 4044925, 4589398, 3603715, 2180191]
  a := ![-37, -48, -6, -1, -77]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5296736, -4771851, 4589398, 3603715, 2180191]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N1 B_one_repr
lemma NI29N1 : Nat.card (O ⧸ I29N1) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N1

def I29N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-287, 888, 682, 40, -77]] i)))

def SI29N2: IdealEqSpanCertificate' Table ![![-287, 888, 682, 40, -77]] 
 ![![29, 0, 0, 0, 0], ![15, 1, 0, 0, 0], ![25, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![14, 0, 0, 0, 1]] where
  M :=![![![-287, 888, 682, 40, -77], ![2390, -950, -1384, -139, 160], ![-3734, 2823, 3081, 275, -358], ![4450, -3631, -3920, -388, 470], ![-4330, 2692, 3298, 390, -411]]]
  hmulB := by decide  
  f := ![![![-1098553, 1498002, 1838028, 1093364, 438287]], ![![-946213, 1290270, 1583144, 941745, 377509]], ![![-2643951, 3605331, 4423693, 2631467, 1054853]], ![![-8580430, 11700409, 14356248, 8539926, 3423326]], ![![-24078192, 32833400, 40286150, 23964530, 9606453]]]
  g := ![![![-1031, 888, 682, 40, -77], ![1728, -950, -1384, -139, 160], ![-4148, 2823, 3081, 275, -358], ![5291, -3631, -3920, -388, 470], ![-4294, 2692, 3298, 390, -411]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N2 : Nat.card (O ⧸ I29N2) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N2)

lemma isPrimeI29N2 : Ideal.IsPrime I29N2 := prime_ideal_of_norm_prime hp29.out _ NI29N2
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![37019, -27335, -30042, -2449, 3405]] ![![5363, -3987, -3708, -243, 408]]
  ![![-2655335, 1946900, 2144682, 175114, -243087]] where
 M := ![![![-2655335, 1946900, 2144682, 175114, -243087]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI29N1 : IdealMulLeCertificate' Table 
  ![![-2655335, 1946900, 2144682, 175114, -243087]] ![![-287, 888, 682, 40, -77]]
  ![![29, 0, 0, 0, 0]] where
 M := ![![![-761246433, 556715668, 614169366, 50206888, -69619024]]]
 hmul := by decide  
 g := ![![![![-26249877, 19197092, 21178254, 1731272, -2400656]]]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7811, -6893, -2164, 137, 231]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![-7811, -6893, -2164, 137, 231]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![28, 0, 22, 1, 0], ![25, 28, 11, 0, 1]] where
  M :=![![![-7811, -6893, -2164, 137, 231], ![-6656, -10169, -4820, -76, 548], ![-4968, 2208, 3277, 462, -426], ![10180, -834, -4364, -963, 650], ![-1390, 10300, 8194, 1068, -1129]]]
  hmulB := by decide  
  f := ![![![-90731, 123725, 151810, 90307, 36201]], ![![-905416, 1234633, 1514876, 901132, 361228]], ![![-4064580, 5542536, 6800623, 4045410, 1621650]], ![![-3606060, 4917290, 6033454, 3589053, 1438714]], ![![-4152707, 5662697, 6948055, 4133105, 1656802]]]
  g := ![![![-562, -431, -249, 137, 231], ![-588, -823, -296, -76, 548], ![-234, 456, -71, 462, -426], ![674, -614, 312, -963, 650], ![-99, 1352, -93, 1068, -1129]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 3 2 4 [16, 22, 15, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 23, 15], [5, 7, 16], [0, 1]]
 g := ![![[9, 20, 10], [26, 21, 14], [4, 13, 8], [1]], ![[3, 23, 5, 30], [7, 10, 14, 24], [24, 27, 0, 15], [25, 4, 23, 27]], ![[16, 28, 3, 18], [28, 28], [21, 27, 30, 4], [2, 20, 15, 4]]]
 h' := ![![[11, 23, 15], [18, 26, 14], [29, 22, 13], [15, 9, 16], [0, 1]], ![[5, 7, 16], [23, 24, 23], [30, 4, 18], [1, 16, 30], [11, 23, 15]], ![[0, 1], [18, 12, 25], [5, 5], [0, 6, 16], [5, 7, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23, 13], []]
 b := ![[], [23, 30, 26], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 3
  hpos := by decide
  P := [16, 22, 15, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2142220630, -3010548988, -3673932836, -2237385364, -938386208]
  a := ![-8, -7, 1, -1, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2846731162, 750460156, 1802283660, -2237385364, -938386208]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 29791 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![45, -37, -46, -9, 7]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![45, -37, -46, -9, 7]] 
 ![![31, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![17, 0, 0, 1, 0], ![23, 0, 0, 0, 1]] where
  M :=![![![45, -37, -46, -9, 7], ![-228, 165, 224, 50, -36], ![704, -524, -717, -168, 118], ![-1824, 1360, 1892, 463, -318], ![2490, -1852, -2594, -644, 439]]]
  hmulB := by decide  
  f := ![![![1181, -887, -820, -55, 89]], ![![177, -134, -124, -9, 13]], ![![269, -203, -189, -15, 19]], ![![527, -405, -380, -38, 33]], ![![1019, -789, -746, -85, 58]]]
  g := ![![![14, -37, -46, -9, 7], ![-67, 165, 224, 50, -36], ![215, -524, -717, -168, 118], ![-567, 1360, 1892, 463, -318], ![777, -1852, -2594, -644, 439]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1

def I31N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, -7, -8, -1, 1]] i)))

def SI31N2: IdealEqSpanCertificate' Table ![![9, -7, -8, -1, 1]] 
 ![![31, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![28, 0, 0, 1, 0], ![24, 0, 0, 0, 1]] where
  M :=![![![9, -7, -8, -1, 1], ![-32, 23, 28, 4, -4], ![80, -60, -75, -14, 10], ![-148, 106, 140, 25, -26], ![206, -164, -218, -60, 23]]]
  hmulB := by decide  
  f := ![![![-1751, 1255, 1174, 77, -129]], ![![-548, 387, 364, 24, -40]], ![![-1067, 771, 719, 47, -79]], ![![-1388, 990, 928, 61, -102]], ![![-1502, 1082, 1010, 66, -111]]]
  g := ![![![7, -7, -8, -1, 1], ![-24, 23, 28, 4, -4], ![67, -60, -75, -14, 10], ![-116, 106, 140, 25, -26], ![212, -164, -218, -60, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N2 : Nat.card (O ⧸ I31N2) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N2)

lemma isPrimeI31N2 : Ideal.IsPrime I31N2 := prime_ideal_of_norm_prime hp31.out _ NI31N2
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![-7811, -6893, -2164, 137, 231]] ![![45, -37, -46, -9, 7]]
  ![![21955, 44106, 26852, 3868, -4038]] where
 M := ![![![21955, 44106, 26852, 3868, -4038]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI31N1 : IdealMulLeCertificate' Table 
  ![![21955, 44106, 26852, 3868, -4038]] ![![9, -7, -8, -1, 1]]
  ![![31, 0, 0, 0, 0]] where
 M := ![![![-469929, 321873, 467232, 117521, -79391]]]
 hmul := by decide  
 g := ![![![![-15159, 10383, 15072, 3791, -2561]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N1, I31N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
    exact isPrimeI31N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0 ⊙ MulI31N1)
instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![63, -107, -74, -3, 8]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![63, -107, -74, -3, 8]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![8, 20, 1, 0, 0], ![25, 3, 0, 1, 0], ![8, 34, 0, 0, 1]] where
  M :=![![![63, -107, -74, -3, 8], ![-246, 114, 112, 7, -12], ![310, -241, -189, -9, 20], ![-186, 173, 112, 2, -12], ![168, -86, -64, -4, 5]]]
  hmulB := by decide  
  f := ![![![355, -265, -374, -95, 64]], ![![-2110, 1572, 2220, 563, -380]], ![![-866, 645, 911, 231, -156]], ![![-489, 364, 514, 130, -88]], ![![-1080, 804, 1136, 288, -195]]]
  g := ![![![18, 30, -74, -3, 8], ![-33, -47, 112, 7, -12], ![51, 78, -189, -9, 20], ![-28, -45, 112, 2, -12], ![20, 28, -64, -4, 5]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [21, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 36], [0, 1]]
 g := ![![[8, 30], [9], [36, 28], [30], [1]], ![[0, 7], [9], [31, 9], [30], [1]]]
 h' := ![![[17, 36], [30, 20], [21, 3], [33, 18], [16, 17], [0, 1]], ![[0, 1], [0, 17], [35, 34], [6, 19], [9, 20], [17, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22]]
 b := ![[], [36, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [21, 20, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3006201, 6801552, 7682046, 6117396, 3760688]
  a := ![52, 39, -8, -1, 103]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6688729, -7920404, 7682046, 6117396, 3760688]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, -15, -18, -9, -3]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![13, -15, -18, -9, -3]] 
 ![![37, 0, 0, 0, 0], ![18, 1, 0, 0, 0], ![14, 0, 1, 0, 0], ![13, 0, 0, 1, 0], ![17, 0, 0, 0, 1]] where
  M :=![![![13, -15, -18, -9, -3], ![72, -107, -132, -84, -36], ![420, -552, -677, -390, -150], ![1824, -2526, -3096, -1865, -762], ![5442, -7374, -9054, -5358, -2129]]]
  hmulB := by decide  
  f := ![![![11815, 11589, 4104, -153, -447]], ![![6102, 6031, 2148, -78, -234]], ![![4538, 4398, 1543, -60, -168]], ![![3955, 3927, 1404, -50, -153]], ![![5225, 5073, 1782, -69, -194]]]
  g := ![![![19, -15, -18, -9, -3], ![150, -107, -132, -84, -36], ![742, -552, -677, -390, -150], ![3455, -2526, -3096, -1865, -762], ![10021, -7374, -9054, -5358, -2129]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-417, -427, -156, 5, 17]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![-417, -427, -156, 5, 17]] 
 ![![37, 0, 0, 0, 0], ![20, 1, 0, 0, 0], ![12, 0, 1, 0, 0], ![18, 0, 0, 1, 0], ![32, 0, 0, 0, 1]] where
  M :=![![![-417, -427, -156, 5, 17], ![-500, -507, -184, 6, 20], ![-44, -52, -21, 0, 2], ![220, 224, 80, -5, -10], ![314, 302, 102, -10, -15]]]
  hmulB := by decide  
  f := ![![![1021, -755, -766, -55, 85]], ![![480, -355, -360, -26, 40]], ![![460, -340, -345, -24, 38]], ![![370, -274, -280, -23, 32]], ![![974, -720, -726, -48, 79]]]
  g := ![![![253, -427, -156, 5, 17], ![300, -507, -184, 6, 20], ![32, -52, -21, 0, 2], ![-130, 224, 80, -5, -10], ![-170, 302, 102, -10, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2

def I37N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 2, 4, 4, 2]] i)))

def SI37N3: IdealEqSpanCertificate' Table ![![-1, 2, 4, 4, 2]] 
 ![![37, 0, 0, 0, 0], ![34, 1, 0, 0, 0], ![34, 0, 1, 0, 0], ![34, 0, 0, 1, 0], ![33, 0, 0, 0, 1]] where
  M :=![![![-1, 2, 4, 4, 2], ![-52, 63, 76, 42, 16], ![-172, 244, 303, 186, 76], ![-928, 1258, 1540, 911, 364], ![-2592, 3542, 4348, 2590, 1039]]]
  hmulB := by decide  
  f := ![![![1827, -1358, -1476, -116, 166]], ![![1538, -1145, -1244, -98, 140]], ![![1946, -1444, -1569, -122, 176]], ![![1382, -1030, -1124, -93, 128]], ![![1855, -1376, -1488, -110, 165]]]
  g := ![![![-11, 2, 4, 4, 2], ![-182, 63, 76, 42, 16], ![-746, 244, 303, 186, 76], ![-3758, 1258, 1540, 911, 364], ![-10627, 3542, 4348, 2590, 1039]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N3 : Nat.card (O ⧸ I37N3) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N3)

lemma isPrimeI37N3 : Ideal.IsPrime I37N3 := prime_ideal_of_norm_prime hp37.out _ NI37N3
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![63, -107, -74, -3, 8]] ![![13, -15, -18, -9, -3]]
  ![![99, -62, -56, 12, 17]] where
 M := ![![![99, -62, -56, 12, 17]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![99, -62, -56, 12, 17]] ![![-417, -427, -156, 5, 17]]
  ![![159, -105, -166, -107, -44]] where
 M := ![![![159, -105, -166, -107, -44]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI37N2 : IdealMulLeCertificate' Table 
  ![![159, -105, -166, -107, -44]] ![![-1, 2, 4, 4, 2]]
  ![![37, 0, 0, 0, 0]] where
 M := ![![![247197, -337255, -413734, -246087, -98642]]]
 hmul := by decide  
 g := ![![![![6681, -9115, -11182, -6651, -2666]]]]
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


def P41P0 : CertificateIrreducibleZModOfList' 41 5 2 5 [1, 31, 19, 28, 22, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 0, 6, 12, 32], [23, 35, 6, 8], [2, 21, 6, 15, 15], [28, 25, 23, 6, 35], [0, 1]]
 g := ![![[34, 3, 4], [9, 1, 14, 4], [7, 19, 14, 33], [1], []], ![[5, 30, 38, 14, 40, 37, 6, 36], [2, 25, 27, 20], [19, 21, 21, 1], [22, 25, 31, 22, 40, 17, 25, 36], [40, 27, 11, 40]], ![[6, 6, 29, 6, 16, 0, 16], [31, 5, 38, 33], [27, 22, 39, 5], [13, 22, 26, 22, 26, 0, 23], [0, 23]], ![[8, 35, 37, 33, 4, 22, 10, 13], [14, 28, 19, 39], [34, 14, 23, 39], [4, 5, 13, 11, 27, 24, 35, 11], [36, 35, 10, 20]], ![[34, 29, 31, 12, 39, 2, 39, 6], [23, 24, 31, 2], [15, 27, 6, 16], [40, 24, 7, 13, 19, 25, 24, 14], [1, 7, 38, 36]]]
 h' := ![![[7, 0, 6, 12, 32], [27, 4, 8, 39], [35, 31, 17, 5, 2], [40, 10, 22, 13, 19], [0, 0, 1], [0, 1]], ![[23, 35, 6, 8], [2, 2, 29, 27, 18], [2, 12, 7, 35, 26], [12, 2, 9, 1, 1], [9, 4, 34, 40, 23], [7, 0, 6, 12, 32]], ![[2, 21, 6, 15, 15], [35, 39, 23, 32, 17], [5, 39, 35, 5, 19], [27, 6, 16, 40, 28], [37, 29, 9, 23, 34], [23, 35, 6, 8]], ![[28, 25, 23, 6, 35], [31, 12, 37, 4, 15], [2, 16, 8, 38, 11], [35, 19, 40, 14, 30], [9, 40, 39, 31, 30], [2, 21, 6, 15, 15]], ![[0, 1], [16, 25, 26, 21, 32], [30, 25, 15, 40, 24], [39, 4, 36, 14, 4], [4, 9, 40, 29, 36], [28, 25, 23, 6, 35]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25, 0, 25, 5], [], [], []]
 b := ![[], [20, 21, 14, 37, 37], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 5
  hpos := by decide
  P := [1, 31, 19, 28, 22, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![242731132895348187256, -331200052681158335586, -406331869663910047466, -241830593488561753504, -97036955747342780782]
  a := ![-35, -20, 10, 2, -69]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![5920271534032882616, -8078050065394105746, -9910533406436830426, -5898307158257603744, -2366755018227872702]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-145, 244, 308, 214, 93]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![-145, 244, 308, 214, 93]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![10, 41, 1, 6, 1]] where
  M :=![![![-145, 244, 308, 214, 93], ![-2362, 3104, 3780, 2169, 856], ![-9490, 13121, 16165, 9743, 3910], ![-47726, 65041, 79688, 47354, 19058], ![-135862, 185120, 227274, 135134, 54027]]]
  hmulB := by decide  
  f := ![![![2815, -1882, -1810, -122, 199]], ![![-6214, 4894, 4440, 283, -488]], ![![10710, -7963, -7369, -479, 810]], ![![-9522, 6987, 6496, 424, -714]], ![![-6184, 4891, 4431, 282, -487]]]
  g := ![![![-25, -83, 5, -8, 93], ![-254, -744, 68, -69, 856], ![-1130, -3423, 285, -319, 3910], ![-5542, -16659, 1410, -1558, 19058], ![-15724, -47209, 4029, -4396, 54027]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 4 2 5 [38, 37, 34, 40, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 23, 3, 23], [35, 3, 7, 40], [9, 16, 33, 23], [0, 1]]
 g := ![![[9, 36, 36, 21], [34, 5, 1, 17], [4, 10, 23], [3, 1], []], ![[15, 14, 31, 7, 35, 4], [24, 24, 41, 6, 31, 38], [8, 42, 35], [15, 38, 24, 31, 38, 11], [38, 5, 13]], ![[42, 42, 28, 11, 41, 24], [39, 15, 2, 9, 9, 41], [29, 28, 23], [20, 11, 14, 10, 12, 11], [24, 28, 9]], ![[1, 42, 40, 15], [36, 26, 11, 8, 18, 36], [29, 2, 16], [35, 18, 5, 11, 22, 31], [34, 9, 13]]]
 h' := ![![[2, 23, 3, 23], [41, 11, 42, 35], [30, 33, 10, 19], [15, 23, 33, 18], [0, 0, 1], [0, 1]], ![[35, 3, 7, 40], [18, 6, 41, 19], [32, 31, 23, 22], [11, 19, 3, 11], [22, 1, 32, 37], [2, 23, 3, 23]], ![[9, 16, 33, 23], [3, 0, 31, 32], [29, 15, 31, 31], [23, 15, 12, 18], [12, 21, 25, 38], [35, 3, 7, 40]], ![[0, 1], [3, 26, 15], [40, 7, 22, 14], [14, 29, 38, 39], [36, 21, 28, 11], [9, 16, 33, 23]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [8, 38, 19], []]
 b := ![[], [], [11, 16, 18, 35], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 4
  hpos := by decide
  P := [38, 37, 34, 40, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4962532770498, 7217579232886, 8755561013386, 5470120459630, 2401711618928]
  a := ![8, -2, -6, -10, 16]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-673945324646, -2122153421934, 147763939406, -207910447766, 2401711618928]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 3418801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2815, 1882, 1810, 122, -199]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-2815, 1882, 1810, 122, -199]] 
 ![![43, 0, 0, 0, 0], ![19, 1, 0, 0, 0], ![25, 0, 1, 0, 0], ![11, 0, 0, 1, 0], ![28, 0, 0, 0, 1]] where
  M :=![![![-2815, 1882, 1810, 122, -199], ![6214, -4894, -4440, -283, 488], ![-10710, 7963, 7369, 479, -810], ![9522, -6987, -6496, -424, 714], ![-7134, 5480, 5014, 322, -551]]]
  hmulB := by decide  
  f := ![![![145, -244, -308, -214, -93]], ![![119, -180, -224, -145, -61]], ![![305, -447, -555, -351, -145]], ![![1147, -1575, -1932, -1156, -467]], ![![3254, -4464, -5486, -3282, -1317]]]
  g := ![![![-1851, 1882, 1810, 122, -199], ![4643, -4894, -4440, -283, 488], ![-7647, 7963, 7369, 479, -810], ![6729, -6987, -6496, -424, 714], ![-5226, 5480, 5014, 322, -551]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![-145, 244, 308, 214, 93]] ![![-2815, 1882, 1810, 122, -199]]
  ![![43, 0, 0, 0, 0]] where
 M := ![![![-43, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, -1, 0, 3, 2]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![5, -1, 0, 3, 2]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![26, 4, 1, 0, 0], ![37, 23, 0, 1, 0], ![41, 12, 0, 0, 1]] where
  M :=![![![5, -1, 0, 3, 2], ![-54, 62, 72, 35, 12], ![-118, 183, 231, 151, 64], ![-782, 1045, 1276, 746, 296], ![-2104, 2884, 3544, 2118, 851]]]
  hmulB := by decide  
  f := ![![![163, -73, -92, -7, 10]], ![![-314, 288, 268, 13, -28]], ![![76, -25, -37, -3, 4]], ![![-35, 90, 64, 0, -6]], ![![65, 7, -12, -1, 1]]]
  g := ![![![-4, -2, 0, 3, 2], ![-79, -25, 72, 35, 12], ![-305, -106, 231, 151, 64], ![-1568, -527, 1276, 746, 296], ![-4415, -1494, 3544, 2118, 851]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [32, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [42, 46], [0, 1]]
 g := ![![[31, 25], [33, 16], [17, 1], [7, 25], [1]], ![[0, 22], [0, 31], [12, 46], [23, 22], [1]]]
 h' := ![![[42, 46], [25, 5], [20, 4], [11, 1], [15, 42], [0, 1]], ![[0, 1], [0, 42], [0, 43], [6, 46], [40, 5], [42, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37]]
 b := ![[], [11, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [32, 5, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1386606, 2992761, 3402398, 2655253, 1597267]
  a := ![40, 24, -6, 1, 67]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5395346, -1933082, 3402398, 2655253, 1597267]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, -17, -16, -1, 2]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![23, -17, -16, -1, 2]] 
 ![![47, 0, 0, 0, 0], ![25, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![25, 0, 0, 0, 1]] where
  M :=![![![23, -17, -16, -1, 2], ![-62, 48, 48, 7, -4], ![98, -65, -63, 3, 16], ![-206, 193, 228, 84, 8], ![-32, 136, 168, 154, 93]]]
  hmulB := by decide  
  f := ![![![1041, -1757, -1508, -99, 170]], ![![441, -877, -728, -46, 82]], ![![278, -291, -283, -21, 32]], ![![-42, -127, -72, -2, 8]], ![![747, -1061, -948, -65, 107]]]
  g := ![![![10, -17, -16, -1, 2], ![-30, 48, 48, 7, -4], ![33, -65, -63, 3, 16], ![-145, 193, 228, 84, 8], ![-163, 136, 168, 154, 93]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1177, -864, -952, -78, 108]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![1177, -864, -952, -78, 108]] 
 ![![47, 0, 0, 0, 0], ![29, 1, 0, 0, 0], ![35, 0, 1, 0, 0], ![42, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![1177, -864, -952, -78, 108], ![-3396, 2493, 2748, 226, -312], ![6604, -4848, -5347, -442, 608], ![-7864, 5774, 6380, 537, -728], ![6476, -4754, -5264, -450, 605]]]
  hmulB := by decide  
  f := ![![![2583, 1836, 480, -46, -52]], ![![1625, 1205, 332, -28, -36]], ![![1967, 1344, 333, -36, -36]], ![![2250, 1642, 444, -39, -48]], ![![322, 182, 32, -6, -3]]]
  g := ![![![1323, -864, -952, -78, 108], ![-3819, 2493, 2748, 226, -312], ![7431, -4848, -5347, -442, 608], ![-8868, 5774, 6380, 537, -728], ![7316, -4754, -5264, -450, 605]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2

def I47N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![21, -15, -14, 1, 1]] i)))

def SI47N3: IdealEqSpanCertificate' Table ![![21, -15, -14, 1, 1]] 
 ![![47, 0, 0, 0, 0], ![33, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![28, 0, 0, 1, 0], ![13, 0, 0, 0, 1]] where
  M :=![![![21, -15, -14, 1, 1], ![-28, 21, 8, -10, 4], ![-56, 48, 107, 56, -22], ![400, -280, -452, -125, 110], ![-826, 676, 970, 324, -109]]]
  hmulB := by decide  
  f := ![![![-131131, 97947, 90476, 5871, -9945]], ![![-85473, 63854, 58980, 3827, -6483]], ![![-19459, 14523, 13419, 871, -1475]], ![![-68320, 51040, 47144, 3059, -5182]], ![![-43759, 32675, 30186, 1959, -3318]]]
  g := ![![![11, -15, -14, 1, 1], ![-11, 21, 8, -10, 4], ![-69, 48, 107, 56, -22], ![278, -280, -452, -125, 110], ![-717, 676, 970, 324, -109]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N3 : Nat.card (O ⧸ I47N3) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N3)

lemma isPrimeI47N3 : Ideal.IsPrime I47N3 := prime_ideal_of_norm_prime hp47.out _ NI47N3
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![5, -1, 0, 3, 2]] ![![23, -17, -16, -1, 2]]
  ![![-505, 718, 892, 548, 224]] where
 M := ![![![-505, 718, 892, 548, 224]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![-505, 718, 892, 548, 224]] ![![1177, -864, -952, -78, 108]]
  ![![-793, 1134, 1404, 870, 356]] where
 M := ![![![-793, 1134, 1404, 870, 356]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI47N2 : IdealMulLeCertificate' Table 
  ![![-793, 1134, 1404, 870, 356]] ![![21, -15, -14, 1, 1]]
  ![![47, 0, 0, 0, 0]] where
 M := ![![![-73085, 100157, 122482, 73085, 29751]]]
 hmul := by decide  
 g := ![![![![-1555, 2131, 2606, 1555, 633]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1, I47N2, I47N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
    exact isPrimeI47N2
    exact isPrimeI47N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0 ⊙ MulI47N1 ⊙ MulI47N2)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3131, 2333, 3282, 827, -560]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-3131, 2333, 3282, 827, -560]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![39, 30, 39, 6, 1]] where
  M :=![![![-3131, 2333, 3282, 827, -560], ![18454, -13756, -19388, -4903, 3308], ![-63750, 47499, 67001, 16941, -11460], ![179614, -133917, -188948, -47888, 32228], ![-251060, 186944, 263888, 66666, -45281]]]
  hmulB := by decide  
  f := ![![![297, -385, -354, -25, 40]], ![![-1250, 718, 880, 77, -100]], ![![2202, -1635, -1799, -147, 204]], ![![-2582, 1983, 2152, 174, -244]], ![![881, -884, -875, -66, 99]]]
  g := ![![![353, 361, 474, 79, -560], ![-2086, -2132, -2800, -467, 3308], ![7230, 7383, 9697, 1617, -11460], ![-20326, -20769, -27280, -4552, 32228], ![28583, 29158, 38299, 6384, -45281]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 4 2 5 [37, 14, 31, 41, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [50, 47, 52, 23], [22, 4, 2, 14], [46, 1, 52, 16], [0, 1]]
 g := ![![[23, 46], [14, 41, 4], [22, 7, 9, 44], [7, 12, 1], []], ![[26, 31, 14, 2, 4, 32], [47, 20, 6], [15, 27, 1, 7, 33, 5], [33, 14, 42], [31, 44, 49, 15, 45, 30]], ![[5, 29, 46, 22, 49, 31], [9, 17, 52], [40, 24, 32, 18, 31, 41], [33, 13, 10], [39, 6, 9, 12, 25, 41]], ![[1, 31, 15, 10, 25, 13], [7, 34, 49], [28, 4, 21, 2, 6, 42], [48, 37, 37], [52, 16, 31, 26, 48, 15]]]
 h' := ![![[50, 47, 52, 23], [2, 21, 24], [34, 52, 15, 51], [6, 41, 2, 16], [0, 0, 0, 1], [0, 1]], ![[22, 4, 2, 14], [19, 50, 29, 35], [50, 6, 28, 18], [9, 48, 6, 16], [45, 2, 22, 25], [50, 47, 52, 23]], ![[46, 1, 52, 16], [39, 18, 34, 35], [52, 11, 42, 30], [22, 0, 25, 14], [36, 5, 2, 13], [22, 4, 2, 14]], ![[0, 1], [48, 17, 19, 36], [25, 37, 21, 7], [11, 17, 20, 7], [12, 46, 29, 14], [46, 1, 52, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [43, 6, 50], []]
 b := ![[], [], [0, 30, 4, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 4
  hpos := by decide
  P := [37, 14, 31, 41, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1414926605385, 1943888890832, 2381906176702, 1425305061380, 578059447024]
  a := ![4, 1, -2, -1, 9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-452061227157, -290526311696, -380422872778, -38548143788, 578059447024]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 7890481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-297, 385, 354, 25, -40]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-297, 385, 354, 25, -40]] 
 ![![53, 0, 0, 0, 0], ![29, 1, 0, 0, 0], ![42, 0, 1, 0, 0], ![39, 0, 0, 1, 0], ![40, 0, 0, 0, 1]] where
  M :=![![![-297, 385, 354, 25, -40], ![1250, -718, -880, -77, 100], ![-2202, 1635, 1799, 147, -204], ![2582, -1983, -2152, -174, 244], ![-2224, 1510, 1720, 144, -195]]]
  hmulB := by decide  
  f := ![![![3131, -2333, -3282, -827, 560]], ![![1365, -1017, -1430, -360, 244]], ![![3684, -2745, -3865, -975, 660]], ![![-1085, 810, 1150, 295, -196]], ![![7100, -5288, -7456, -1882, 1277]]]
  g := ![![![-485, 385, 354, 25, -40], ![1095, -718, -880, -77, 100], ![-2316, 1635, 1799, 147, -204], ![2783, -1983, -2152, -174, 244], ![-2190, 1510, 1720, 144, -195]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-3131, 2333, 3282, 827, -560]] ![![-297, 385, 354, 25, -40]]
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


def P59P0 : CertificateIrreducibleZModOfList' 59 5 2 5 [15, 52, 3, 29, 30, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [39, 29, 39, 47, 7], [29, 38, 1, 32, 6], [51, 35, 20, 46, 43], [28, 15, 58, 52, 3], [0, 1]]
 g := ![![[21, 12, 29, 28, 15], [44, 38, 55, 14, 5], [56, 35, 54, 3], [45, 29, 1], []], ![[57, 9, 12, 25, 58, 19, 21, 9], [26, 7, 4, 20, 46, 36, 29, 46], [39, 7, 50, 21], [19, 4, 55, 24, 40, 47, 6, 19], [21, 10, 30, 36, 43, 58, 41, 48]], ![[58, 1, 34, 25, 46, 53, 5, 50], [50, 12, 33, 0, 36, 19, 45, 44], [17, 40, 57, 16], [32, 9, 27, 54, 14, 44, 17, 44], [3, 41, 46, 9, 1, 41, 44, 39]], ![[47, 54, 33, 49, 25, 6, 47, 14], [15, 16, 17, 54, 21, 52, 24, 34], [46, 6, 28, 25], [38, 13, 46, 3, 17, 8, 55, 42], [26, 31, 37, 2, 43, 23, 29, 34]], ![[9, 55, 25, 42, 51, 58, 27, 4], [11, 15, 56, 22, 8, 4, 26, 25], [13, 37, 35, 46], [8, 53, 6, 2, 27, 36, 50, 16], [0, 3, 20, 3, 29, 42, 4, 27]]]
 h' := ![![[39, 29, 39, 47, 7], [48, 25, 30, 53, 29], [13, 30, 55, 25, 8], [33, 57, 53, 31, 48], [0, 0, 0, 1], [0, 1]], ![[29, 38, 1, 32, 6], [11, 40, 53, 14, 25], [53, 10, 22, 50, 30], [44, 21, 28, 18, 32], [4, 46, 27, 32, 21], [39, 29, 39, 47, 7]], ![[51, 35, 20, 46, 43], [39, 1, 54, 32, 38], [30, 3, 22, 26, 26], [52, 16, 31, 45, 4], [36, 54, 4, 7, 26], [29, 38, 1, 32, 6]], ![[28, 15, 58, 52, 3], [14, 40, 17, 23, 53], [40, 25, 42, 50, 16], [9, 18, 13, 52, 54], [42, 6, 43, 25, 7], [51, 35, 20, 46, 43]], ![[0, 1], [38, 12, 23, 55, 32], [9, 50, 36, 26, 38], [33, 6, 52, 31, 39], [4, 12, 44, 53, 5], [28, 15, 58, 52, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51, 14, 54, 12], [], [], []]
 b := ![[], [50, 42, 55, 21, 32], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 5
  hpos := by decide
  P := [15, 52, 3, 29, 30, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1192851881570006909846, 1627731515626813822581, 1996951822743830483522, 1188564814244333670382, 476977952950898604176]
  a := ![49, 29, -10, -4, 95]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-20217828501186557794, 27588669756386674959, 33846641063454753958, 20145166343124299498, 8084372083913535664]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0, 0, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0, 0, 0]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![0, 0, 0, 0, 61]] where
  M :=![![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![0, 0, 0, 0, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 5 2 5 [24, 9, 25, 7, 33, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [59, 40, 53, 47, 44], [29, 32, 17, 29, 38], [47, 2, 60, 50, 11], [15, 47, 53, 57, 29], [0, 1]]
 g := ![![[56, 53, 26, 36, 47], [0, 40, 22, 15], [26, 59, 44, 42, 4], [45, 28, 1], []], ![[3, 52, 46, 31, 33, 38, 43, 23], [9, 58, 6, 14], [28, 45, 1, 49, 57, 13, 55, 17], [39, 6, 29, 9, 32, 21, 29, 53], [11, 43, 31, 35, 52, 33, 53, 28]], ![[48, 13, 44, 31, 38, 2, 13, 53], [54, 48, 3, 34], [1, 19, 24, 41, 30, 43, 36, 11], [59, 7, 41, 5, 0, 17, 16, 40], [59, 50, 39, 46, 3, 39, 38, 33]], ![[30, 1, 60, 12, 26, 48, 8, 26], [2, 48, 51, 60], [42, 20, 28, 34, 16, 7, 18, 51], [26, 13, 6, 22, 21, 33, 35, 26], [17, 7, 31, 32, 12, 33, 30, 50]], ![[33, 24, 16, 15, 47, 42, 32, 24], [60, 46, 24, 42], [42, 19, 0, 35, 48, 60, 15, 40], [41, 60, 54, 52, 35, 30, 50, 8], [30, 36, 37, 55, 4, 26, 31, 50]]]
 h' := ![![[59, 40, 53, 47, 44], [13, 56, 27, 7, 48], [47, 16, 44, 14, 25], [18, 21, 2, 13, 2], [0, 0, 0, 1], [0, 1]], ![[29, 32, 17, 29, 38], [23, 56, 25, 40, 47], [42, 32, 51, 46, 21], [58, 43, 22, 1, 11], [33, 20, 0, 9, 49], [59, 40, 53, 47, 44]], ![[47, 2, 60, 50, 11], [21, 34, 52, 14, 53], [6, 58, 31, 10, 41], [38, 31, 30, 32, 20], [37, 10, 42, 16, 30], [29, 32, 17, 29, 38]], ![[15, 47, 53, 57, 29], [10, 52, 5, 46, 18], [34, 9, 15, 38, 50], [59, 60, 5, 9, 7], [20, 1, 25, 53, 18], [47, 2, 60, 50, 11]], ![[0, 1], [2, 46, 13, 15, 17], [51, 7, 42, 14, 46], [41, 28, 2, 6, 21], [32, 30, 55, 43, 25], [15, 47, 53, 57, 29]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43, 4, 19, 47], [], [], []]
 b := ![[], [58, 0, 33, 20, 53], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 5
  hpos := by decide
  P := [24, 9, 25, 7, 33, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-23160605635221414724, 31601630961370000555, 38770459749120273596, 23074222020450906165, 9258583950687865545]
  a := ![22, 13, -6, -1, 43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-379682059593793684, 518059523956885255, 635581307362627436, 378265934761490265, 151780064765374845]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 844596301 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def PBC61 : ContainsPrimesAboveP 61 ![I61N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![61, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 61 (by decide) 𝕀



lemma PB3864I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB3864I1 : PrimesBelowBoundCertificateInterval O 23 61 3864 where
  m := 9
  g := ![3, 3, 4, 1, 2, 4, 2, 1, 1]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB3864I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1, I29N2]
    · exact ![I31N0, I31N1, I31N2]
    · exact ![I37N0, I37N1, I37N2, I37N3]
    · exact ![I41N0]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1, I47N2, I47N3]
    · exact ![I53N0, I53N1]
    · exact ![I59N0]
    · exact ![I61N0]
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
    · exact ![841, 841, 29]
    · exact ![29791, 31, 31]
    · exact ![1369, 37, 37, 37]
    · exact ![115856201]
    · exact ![3418801, 43]
    · exact ![2209, 47, 47, 47]
    · exact ![7890481, 53]
    · exact ![714924299]
    · exact ![844596301]
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
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
      exact NI47N2
      exact NI47N3
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
  β := ![I29N0, I29N1, I29N2, I31N1, I31N2, I37N0, I37N1, I37N2, I37N3, I43N1, I47N0, I47N1, I47N2, I47N3, I53N1]
  Il := ![[I29N0, I29N1, I29N2], [I31N1, I31N2], [I37N0, I37N1, I37N2, I37N3], [], [I43N1], [I47N0, I47N1, I47N2, I47N3], [I53N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
