
import IdealArithmetic.Examples.NF5_3_2025000000_3.RI5_3_2025000000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0, 0, 0]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0, 0, 0]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![0, 0, 0, 0, 29]] where
  M :=![![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![0, 0, 0, 0, 29]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 5 2 4 [22, 12, 7, 6, 12, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 26, 28, 2, 10], [16, 20, 14, 11, 14], [20, 13, 4, 12, 6], [5, 27, 12, 4, 28], [0, 1]]
 g := ![![[9, 22, 4, 4, 16], [22, 2, 24, 16], [22, 17, 1], []], ![[19, 9, 22, 0, 17, 11, 10, 3], [12, 15, 25, 16], [27, 26, 6, 14, 13, 17, 6, 26], [3, 5, 8, 22, 20, 4, 26, 14]], ![[1, 12, 0, 14, 12, 27, 23, 8], [15, 8, 16, 23], [10, 9, 13, 18, 9, 18, 26, 3], [17, 28, 2, 10, 14, 10, 17, 18]], ![[25, 1, 19, 1, 19, 12, 26, 20], [2, 7, 10, 23], [0, 20, 28, 27, 23, 23, 15, 16], [12, 5, 15, 1, 7, 25, 9, 13]], ![[22, 24, 18, 12, 25, 21, 16, 5], [15, 6, 15, 9], [18, 2, 12, 15, 22, 11, 7, 25], [7, 22, 25, 17, 0, 25, 24, 28]]]
 h' := ![![[5, 26, 28, 2, 10], [3, 11, 23, 19, 25], [9, 0, 26, 27, 4], [0, 0, 0, 1], [0, 1]], ![[16, 20, 14, 11, 14], [20, 12, 28, 15, 26], [20, 2, 5, 9, 4], [1, 6, 6, 15, 22], [5, 26, 28, 2, 10]], ![[20, 13, 4, 12, 6], [17, 18, 0, 14, 10], [17, 11, 11, 13, 9], [10, 11, 18, 11, 20], [16, 20, 14, 11, 14]], ![[5, 27, 12, 4, 28], [21, 19, 7, 13, 10], [23, 15, 11, 3, 9], [22, 5, 24, 24, 14], [20, 13, 4, 12, 6]], ![[0, 1], [2, 27, 0, 26, 16], [10, 1, 5, 6, 3], [0, 7, 10, 7, 2], [5, 27, 12, 4, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 15, 6, 7], [], [], []]
 b := ![[], [10, 18, 8, 1, 8], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 5
  hpos := by decide
  P := [22, 12, 7, 6, 12, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7237682560737542314, -4658323755790332297, 7503852675116975667, -5893191574010555016, -20506575593169572118]
  a := ![1566, -1159, 1784, -1386, -4887]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![249575260715087666, -160631853647942493, 258753540521275023, -203213502552088104, -707123296316192142]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 20511149 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def PBC29 : ContainsPrimesAboveP 29 ![I29N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![29, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 29 (by decide) 𝕀

instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1959, -1168, 921, -659, -2407]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![1959, -1168, 921, -659, -2407]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![15, 20, 1, 0, 0], ![5, 25, 0, 1, 0], ![8, 27, 0, 0, 1]] where
  M :=![![![1959, -1168, 921, -659, -2407], ![-6554, 6821, -9129, 6531, 23275], ![8162, -13016, 20814, -14891, -52759], ![9120, -3092, -584, 417, 1056], ![2546, -5836, 10183, -7285, -25746]]]
  hmulB := by decide  
  f := ![![![6833, -4160, 6749, -5347, -18449]], ![![52754, -32269, 52311, -41417, -142999]], ![![50219, -30676, 49737, -39388, -135964]], ![![92529, -56599, 91748, -72643, -250808]], ![![38608, -23597, 38258, -30294, -104583]]]
  g := ![![![345, 1996, 921, -659, -2407], ![-2854, -19429, -9129, 6531, 23275], ![6209, 44112, 20814, -14891, -52759], ![237, -979, -584, 417, 1056], ![2974, 21541, 10183, -7285, -25746]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [28, 28, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 30], [0, 1]]
 g := ![![[1, 10], [17, 2], [28, 20], [3, 1]], ![[0, 21], [23, 29], [26, 11], [6, 30]]]
 h' := ![![[3, 30], [20, 14], [22, 8], [9, 12], [0, 1]], ![[0, 1], [0, 17], [15, 23], [14, 19], [3, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [9, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [28, 28, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-177171443, 115365090, -185192987, 145354399, 506192998]
  a := ![1757, -1371, 1997, -1666, -5483]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-70180407, -434898261, -185192987, 145354399, 506192998]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![865, -528, 856, -678, -2340]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![865, -528, 856, -678, -2340]] 
 ![![31, 0, 0, 0, 0], ![19, 1, 0, 0, 0], ![11, 0, 1, 0, 0], ![10, 0, 0, 1, 0], ![30, 0, 0, 0, 1]] where
  M :=![![![865, -528, 856, -678, -2340], ![6624, -4045, 6558, -5194, -17928], ![50568, -30860, 50037, -39634, -136788], ![190392, -116276, 188512, -149301, -515340], ![-35288, 21560, -34952, 27680, 95549]]]
  hmulB := by decide  
  f := ![![![4879, -1640, 4040, -2962, -10380]], ![![3427, -1165, 2854, -2092, -7332]], ![![2915, -1004, 2429, -1780, -6240]], ![![2914, -988, 2424, -1777, -6228]], ![![4726, -1592, 3912, -2868, -10051]]]
  g := ![![![2531, -528, 856, -678, -2340], ![19391, -4045, 6558, -5194, -17928], ![147951, -30860, 50037, -39634, -136788], ![557394, -116276, 188512, -149301, -515340], ![-103346, 21560, -34952, 27680, 95549]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1

def I31N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-55, 255, -496, 355, 1251]] i)))

def SI31N2: IdealEqSpanCertificate' Table ![![-55, 255, -496, 355, 1251]] 
 ![![31, 0, 0, 0, 0], ![25, 1, 0, 0, 0], ![26, 0, 1, 0, 0], ![19, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-55, 255, -496, 355, 1251], ![-942, 612, -568, 407, 1473], ![2718, -2967, 4009, -2865, -10209], ![-1260, 2429, -4201, 3015, 10650], ![1550, -1832, 2627, -1881, -6686]]]
  hmulB := by decide  
  f := ![![![705143, -611827, 955054, -718479, -2605599]], ![![397115, -344563, 537858, -404626, -1467396]], ![![1885168, -1635689, 2553291, -1920819, -6965943]], ![![-4360609, 3783526, -5906043, 4443066, 16112991]], ![![1908986, -1656352, 2585547, -1945085, -7053944]]]
  g := ![![![-9, 255, -496, 355, 1251], ![-297, 612, -568, 407, 1473], ![874, -2967, 4009, -2865, -10209], ![-324, 2429, -4201, 3015, 10650], ![477, -1832, 2627, -1881, -6686]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N2 : Nat.card (O ⧸ I31N2) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N2)

lemma isPrimeI31N2 : Ideal.IsPrime I31N2 := prime_ideal_of_norm_prime hp31.out _ NI31N2

def I31N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, -224, 349, -245, -861]] i)))

def SI31N3: IdealEqSpanCertificate' Table ![![113, -224, 349, -245, -861]] 
 ![![31, 0, 0, 0, 0], ![29, 1, 0, 0, 0], ![27, 0, 1, 0, 0], ![28, 0, 0, 1, 0], ![20, 0, 0, 0, 1]] where
  M :=![![![113, -224, 349, -245, -861], ![882, -511, 609, -471, -1743], ![-6906, 5940, -8740, 6519, 23595], ![21408, -19296, 29964, -22423, -81144], ![-8886, 7796, -11887, 8897, 32216]]]
  hmulB := by decide  
  f := ![![![-41593, 22856, -39751, 30983, 107277]], ![![-47585, 26457, -45650, 35644, 123372]], ![![-98295, 57204, -95725, 75264, 260148]], ![![-264796, 158672, -260428, 205681, 710304]], ![![14746, -10636, 15509, -12607, -43294]]]
  g := ![![![686, -224, 349, -245, -861], ![1526, -511, 609, -471, -1743], ![-19278, 5940, -8740, 6519, 23595], ![65248, -19296, 29964, -22423, -81144], ![-26047, 7796, -11887, 8897, 32216]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N3 : Nat.card (O ⧸ I31N3) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N3)

lemma isPrimeI31N3 : Ideal.IsPrime I31N3 := prime_ideal_of_norm_prime hp31.out _ NI31N3
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![1959, -1168, 921, -659, -2407]] ![![865, -528, 856, -678, -2340]]
  ![![719, -888, 1293, -925, -3287]] where
 M := ![![![719, -888, 1293, -925, -3287]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI31N1 : IdealMulLeCertificate' Table 
  ![![719, -888, 1293, -925, -3287]] ![![-55, 255, -496, 355, 1251]]
  ![![381975, -421483, 582373, -416644, -1483160]] where
 M := ![![![381975, -421483, 582373, -416644, -1483160]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI31N2 : IdealMulLeCertificate' Table 
  ![![381975, -421483, 582373, -416644, -1483160]] ![![113, -224, 349, -245, -861]]
  ![![31, 0, 0, 0, 0]] where
 M := ![![![-90607761, 65958297, -67311788, 48158097, 173533505]]]
 hmul := by decide  
 g := ![![![![-2922831, 2127687, -2171348, 1553487, 5597855]]]]
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

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![153, -519, 400, -277, -1015]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![153, -519, 400, -277, -1015]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![35, 36, 19, 1, 0], ![32, 22, 23, 0, 1]] where
  M :=![![![153, -519, 400, -277, -1015], ![-3074, 2444, -4230, 3051, 10783], ![-5014, 427, -1107, 859, 3005], ![-684, -2081, 97, 9, -222], ![-886, 16, 669, -479, -1644]]]
  hmulB := by decide  
  f := ![![![-8395, 7281, -11366, 8551, 31009]], ![![63134, -54802, 85542, -64349, -233377]], ![![-477494, 414127, -646473, 486363, 1763725]], ![![-144043, 124847, -194904, 146645, 531744]], ![![-285544, 247633, -386570, 290832, 1054651]]]
  g := ![![![1144, 859, 784, -277, -1015], ![-12295, -9314, -8384, 3051, 10783], ![-3547, -2611, -2339, 859, 3005], ![165, 67, 136, 9, -222], ![1851, 1444, 1286, -479, -1644]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [29, 29, 26, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 6, 26], [8, 30, 11], [0, 1]]
 g := ![![[5, 18, 21], [21, 36], [29, 27, 28], [11, 1], []], ![[24, 23, 17, 36], [36, 3], [17, 11, 34, 30], [10, 12], [15, 10]], ![[9, 9, 3, 16], [24, 34], [12, 28, 20, 34], [6, 36], [30, 10]]]
 h' := ![![[3, 6, 26], [9, 16, 13], [10, 15, 6], [14, 22, 18], [0, 0, 1], [0, 1]], ![[8, 30, 11], [32, 19, 29], [15, 26, 15], [34, 14, 2], [18, 14, 30], [3, 6, 26]], ![[0, 1], [19, 2, 32], [30, 33, 16], [1, 1, 17], [8, 23, 6], [8, 30, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21, 19], []]
 b := ![[], [7, 21, 32], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [29, 29, 26, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7416010053, -4542100354, 7361048502, -5827299330, -20122854352]
  a := ![489, -365, 557, -438, -1526]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![23116292591, 17511985710, 15700145564, -5827299330, -20122854352]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 50653 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, 12, -21, 15, 53]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-5, 12, -21, 15, 53]] 
 ![![37, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![25, 0, 1, 0, 0], ![20, 0, 0, 1, 0], ![27, 0, 0, 0, 1]] where
  M :=![![![-5, 12, -21, 15, 53], ![-26, 13, -7, 5, 19], ![122, -116, 156, -113, -403], ![-72, 120, -192, 137, 492], ![70, -76, 107, -77, -276]]]
  hmulB := by decide  
  f := ![![![-873, 308, -739, 541, 1897]], ![![-229, 81, -194, 142, 498]], ![![-755, 264, -637, 466, 1634]], ![![-660, 232, -560, 409, 1436]], ![![-637, 224, -538, 394, 1381]]]
  g := ![![![-35, 12, -21, 15, 53], ![-15, 13, -7, 5, 19], ![275, -116, 156, -113, -403], ![-328, 120, -192, 137, 492], ![187, -76, 107, -77, -276]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3363, 2915, -4551, 3424, 12416]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![-3363, 2915, -4551, 3424, 12416]] 
 ![![37, 0, 0, 0, 0], ![29, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![31, 0, 0, 0, 1]] where
  M :=![![![-3363, 2915, -4551, 3424, 12416], ![25216, -21898, 34179, -25710, -93248], ![-191224, 165781, -258804, 194716, 706076], ![704532, -611795, 954931, -718311, -2605254], ![-281032, 243932, -380762, 286430, 1038801]]]
  hmulB := by decide  
  f := ![![![-10423, 7411, -7399, 5294, 19096]], ![![-7383, 4939, -4598, 3290, 11908]], ![![-3558, 3395, -4330, 3098, 11060]], ![![-3409, 2174, -1902, 1361, 4942]], ![![-8869, 6765, -7251, 5188, 18653]]]
  g := ![![![-12196, 2915, -4551, 3424, 12416], ![91598, -21898, 34179, -25710, -93248], ![-693573, 165781, -258804, 194716, 706076], ![2559144, -611795, 954931, -718311, -2605254], ![-1020413, 243932, -380762, 286430, 1038801]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![153, -519, 400, -277, -1015]] ![![-5, 12, -21, 15, 53]]
  ![![10423, -7411, 7399, -5294, -19096]] where
 M := ![![![10423, -7411, 7399, -5294, -19096]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![10423, -7411, 7399, -5294, -19096]] ![![-3363, 2915, -4551, 3424, 12416]]
  ![![37, 0, 0, 0, 0]] where
 M := ![![![-37, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1, I37N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
    exact isPrimeI37N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0 ⊙ MulI37N1)
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


def P41P0 : CertificateIrreducibleZModOfList' 41 5 2 5 [34, 1, 4, 23, 37, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 11, 17, 38, 9], [15, 36, 5, 20, 26], [12, 20, 30, 13, 28], [37, 14, 30, 11, 19], [0, 1]]
 g := ![![[9, 4, 14, 22, 2], [25, 21, 21, 5], [33, 18, 3, 16], [1], []], ![[17, 28, 2, 16, 21, 40, 17, 18], [40, 10, 34, 9], [0, 35, 24, 1], [3, 36, 1, 34, 28, 39, 36, 18], [13, 24, 24, 40]], ![[8, 29, 6, 30, 39, 34], [29, 24, 3, 36], [18, 3, 37, 39], [6, 40, 10, 22, 19, 3, 7, 34], [36, 6, 13, 20]], ![[13, 7, 24, 15, 1, 0, 25, 17], [9, 6, 12, 2], [40, 37, 17, 40], [8, 33, 3, 37, 20, 4, 36, 28], [13, 11, 10, 5]], ![[27, 17, 9, 21, 1, 10, 35, 13], [39, 3, 13, 4], [19, 23, 31, 25], [14, 6, 7, 21, 37, 8, 7, 14], [38, 37, 17, 33]]]
 h' := ![![[22, 11, 17, 38, 9], [19, 0, 28, 39, 17], [34, 38, 21, 30, 13], [7, 40, 37, 18, 4], [0, 0, 1], [0, 1]], ![[15, 36, 5, 20, 26], [9, 27, 3, 22, 24], [4, 15, 15, 27, 3], [2, 4, 28, 31, 40], [1, 24, 18, 21, 24], [22, 11, 17, 38, 9]], ![[12, 20, 30, 13, 28], [34, 27, 13, 35], [35, 23, 16, 19, 6], [14, 30, 38, 30, 11], [26, 20, 34, 30, 6], [15, 36, 5, 20, 26]], ![[37, 14, 30, 11, 19], [4, 40, 38, 22, 28], [33, 38, 29, 17, 17], [32, 26, 2, 33, 32], [30, 11, 20, 5, 1], [12, 20, 30, 13, 28]], ![[0, 1], [18, 29, 0, 5, 13], [14, 9, 1, 30, 2], [39, 23, 18, 11, 36], [36, 27, 9, 26, 10], [37, 14, 30, 11, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 38, 26, 4], [], [], []]
 b := ![[], [6, 37, 36, 20, 36], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 5
  hpos := by decide
  P := [34, 1, 4, 23, 37, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1486660645689686905392, 909775936094120281561, -1474599942179804151453, 1167493662997822661646, 4031100695295138421828]
  a := ![-3687, 2745, -4199, 3287, 11506]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-36260015748528948912, 22189656977905372721, -35965852248287906133, 28475455195068845406, 98319529153539961508]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4225, -1500, 3573, -2617, -9177]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![4225, -1500, 3573, -2617, -9177]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![29, 29, 1, 0, 0], ![31, 3, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  M :=![![![4225, -1500, 3573, -2617, -9177], ![11370, -4027, 9625, -7051, -24723], ![30894, -11056, 26244, -19229, -67425], ![36336, -13044, 30816, -22607, -79248], ![-222, 84, -171, 133, 460]]]
  hmulB := by decide  
  f := ![![![21619, -18756, 29277, -22025, -79875]], ![![-163050, 141471, -220831, 166129, 602475]], ![![-66787, 57949, -90456, 68049, 246783]], ![![-101723, 88263, -137778, 103649, 375888]], ![![46719, -40536, 63276, -47602, -172631]]]
  g := ![![![1496, -2262, 3573, -2617, -9177], ![4031, -6093, 9625, -7051, -24723], ![10994, -16615, 26244, -19229, -67425], ![12947, -19509, 30816, -22607, -79248], ![-82, 108, -171, 133, 460]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [14, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 42], [0, 1]]
 g := ![![[0, 40], [], [17], [], [1]], ![[0, 3], [], [17], [], [1]]]
 h' := ![![[0, 42], [0, 13], [20], [0, 24], [29], [0, 1]], ![[0, 1], [0, 30], [20], [0, 19], [29], [0, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40]]
 b := ![[], [0, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [14, 0, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-69138705, 50087222, -79600800, 61404983, 217390900]
  a := ![3745, -2764, 4267, -3300, -11687]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-37692746, 50565011, -79600800, 61404983, 217390900]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4301, -1035, -1107, 676, 1760]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-4301, -1035, -1107, 676, 1760]] 
 ![![43, 0, 0, 0, 0], ![11, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![15, 0, 0, 1, 0], ![16, 0, 0, 0, 1]] where
  M :=![![![-4301, -1035, -1107, 676, 1760], ![-62768, 41604, -72287, 53958, 193816], ![216584, -222601, 327670, -247644, -903124], ![-1131636, 941535, -1492767, 1121669, 4061934], ![419668, -363988, 568262, -427494, -1550307]]]
  hmulB := by decide  
  f := ![![![11385, -9373, 11387, -8250, -29408]], ![![2657, -1935, 2266, -1666, -5924]], ![![4144, -3545, 5214, -3890, -13668]], ![![12249, -8490, 11868, -9055, -31686]], ![![2828, -2876, 3418, -2386, -8599]]]
  g := ![![![-520, -1035, -1107, 676, 1760], ![-89594, 41604, -72287, 53958, 193816], ![423453, -222601, 327670, -247644, -903124], ![-1892148, 941535, -1492767, 1121669, 4061934], ![723134, -363988, 568262, -427494, -1550307]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1

def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1237, 427, -1037, 760, 2664]] i)))

def SI43N2: IdealEqSpanCertificate' Table ![![-1237, 427, -1037, 760, 2664]] 
 ![![43, 0, 0, 0, 0], ![18, 1, 0, 0, 0], ![20, 0, 1, 0, 0], ![26, 0, 0, 1, 0], ![37, 0, 0, 0, 1]] where
  M :=![![![-1237, 427, -1037, 760, 2664], ![-3408, 1238, -2925, 2142, 7512], ![-9240, 3297, -7792, 5712, 20028], ![-10812, 3849, -9153, 6725, 23562], ![60, -28, 74, -58, -199]]]
  hmulB := by decide  
  f := ![![![-317023, 275069, -429379, 323018, 1171440]], ![![-77106, 66902, -104433, 78564, 284916]], ![![-566780, 491773, -767652, 577498, 2094324]], ![![1361722, -1181513, 1844329, -1387473, -5031738]], ![![-891517, 773535, -1207479, 908376, 3294269]]]
  g := ![![![-2477, 427, -1037, 760, 2664], ![-6996, 1238, -2925, 2142, 7512], ![-18658, 3297, -7792, 5712, 20028], ![-21946, 3849, -9153, 6725, 23562], ![185, -28, 74, -58, -199]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2

def I43N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8639, 7494, -11699, 8801, 31917]] i)))

def SI43N3: IdealEqSpanCertificate' Table ![![-8639, 7494, -11699, 8801, 31917]] 
 ![![43, 0, 0, 0, 0], ![28, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![40, 0, 0, 1, 0], ![18, 0, 0, 0, 1]] where
  M :=![![![-8639, 7494, -11699, 8801, 31917], ![65118, -56505, 88201, -66353, -240633], ![-491190, 426174, -665260, 500469, 1814973], ![1819512, -1578734, 2464378, -1853931, -6723372], ![-724730, 628820, -981581, 738435, 2677970]]]
  hmulB := by decide  
  f := ![![![91, -410, 665, -459, -1641]], ![![34, -245, 387, -263, -945]], ![![-309, -60, 125, -54, -222]], ![![-968, 206, -342, 345, 1128]], ![![196, -248, 417, -307, -1078]]]
  g := ![![![-17650, 7494, -11699, 8801, 31917], ![133073, -56505, 88201, -66353, -240633], ![-1003692, 426174, -665260, 500469, 1814973], ![3718082, -1578734, 2464378, -1853931, -6723372], ![-1480939, 628820, -981581, 738435, 2677970]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N3 : Nat.card (O ⧸ I43N3) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N3)

lemma isPrimeI43N3 : Ideal.IsPrime I43N3 := prime_ideal_of_norm_prime hp43.out _ NI43N3
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![4225, -1500, 3573, -2617, -9177]] ![![-4301, -1035, -1107, 676, 1760]]
  ![![-39966917, 14188533, -33850800, 24791753, 86936009]] where
 M := ![![![-39966917, 14188533, -33850800, 24791753, 86936009]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![-39966917, 14188533, -33850800, 24791753, 86936009]] ![![-1237, 427, -1037, 760, 2664]]
  ![![51033674969, -18117308260, 43224016961, -31656538431, -111008410997]] where
 M := ![![![51033674969, -18117308260, 43224016961, -31656538431, -111008410997]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI43N2 : IdealMulLeCertificate' Table 
  ![![51033674969, -18117308260, 43224016961, -31656538431, -111008410997]] ![![-8639, 7494, -11699, 8801, 31917]]
  ![![43, 0, 0, 0, 0]] where
 M := ![![![-173540215323, 61607979014, -146983442112, 107648185224, 377484544448]]]
 hmul := by decide  
 g := ![![![![-4035818961, 1432743698, -3418219584, 2503446168, 8778710336]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1, I43N2, I43N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
    exact isPrimeI43N2
    exact isPrimeI43N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0 ⊙ MulI43N1 ⊙ MulI43N2)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4729, 1686, -4011, 2939, 10305]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-4729, 1686, -4011, 2939, 10305]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![25, 23, 30, 6, 1]] where
  M :=![![![-4729, 1686, -4011, 2939, 10305], ![-12882, 4623, -10937, 8021, 28119], ![-35646, 13010, -30386, 22339, 78273], ![-45168, 17406, -39030, 28901, 101112], ![1134, -660, 1107, -869, -3004]]]
  hmulB := by decide  
  f := ![![![1, 6, -15, 11, 39]], ![![-6, 5, 7, -7, -27]], ![![-210, 146, -240, 187, 687]], ![![1128, -930, 1422, -1073, -3900]], ![![-1, -13, 13, -7, -22]]]
  g := ![![![-5582, -5007, -6663, -1253, 10305], ![-15231, -13662, -18181, -3419, 28119], ![-42393, -38027, -50608, -9517, 78273], ![-54744, -49110, -65370, -12293, 101112], ![1622, 1456, 1941, 365, -3004]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 4 2 5 [45, 16, 2, 38, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 11, 22, 29], [35, 6, 13, 14], [19, 29, 12, 4], [0, 1]]
 g := ![![[1, 0, 46, 16], [18, 19, 43, 36], [23, 35, 37, 37], [9, 1], []], ![[38, 28, 33, 21, 26, 5], [17, 43, 9, 45, 13, 5], [40, 2, 31, 38, 22, 33], [38, 32, 22, 41, 28, 15], [38, 9, 42]], ![[42, 38, 28, 13, 19, 2], [35, 15, 27, 1], [27, 4, 31, 18, 6, 9], [41, 14, 30, 18, 16, 2], [15, 13, 8]], ![[18, 39, 22, 5, 18, 14], [19, 2, 0, 32, 22, 7], [35, 41, 21, 23, 31, 8], [37, 22, 0, 27, 35, 3], [13, 5, 16]]]
 h' := ![![[2, 11, 22, 29], [36, 33, 23, 4], [46, 26, 43, 41], [18, 46, 13, 32], [0, 0, 1], [0, 1]], ![[35, 6, 13, 14], [12, 8, 45, 21], [41, 28, 13, 21], [45, 40, 1, 10], [33, 18, 26, 17], [2, 11, 22, 29]], ![[19, 29, 12, 4], [5, 45, 1, 11], [5, 18, 32], [33, 16, 35, 45], [33, 18, 19, 36], [35, 6, 13, 14]], ![[0, 1], [14, 8, 25, 11], [16, 22, 6, 32], [23, 39, 45, 7], [11, 11, 1, 41], [19, 29, 12, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [42, 9, 13], []]
 b := ![[], [], [36, 46, 28, 36], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 4
  hpos := by decide
  P := [45, 16, 2, 38, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1685585908259699, 1455542344080272, -2273084439328000, 1711089197452664, 6201624901269328]
  a := ![-1624, 1190, -1850, 1414, 5068]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3334600179574317, -3003868731598176, -4006847478242720, -755290642769432, 6201624901269328]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 4879681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -6, 15, -11, -39]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-1, -6, 15, -11, -39]] 
 ![![47, 0, 0, 0, 0], ![42, 1, 0, 0, 0], ![22, 0, 1, 0, 0], ![34, 0, 0, 1, 0], ![31, 0, 0, 0, 1]] where
  M :=![![![-1, -6, 15, -11, -39], ![6, -5, -7, 7, 27], ![210, -146, 240, -187, -687], ![-1128, 930, -1422, 1073, 3900], ![402, -324, 507, -385, -1402]]]
  hmulB := by decide  
  f := ![![![4729, -1686, 4011, -2939, -10305]], ![![4500, -1605, 3817, -2797, -9807]], ![![2972, -1066, 2524, -1851, -6489]], ![![4382, -1590, 3732, -2741, -9606]], ![![3095, -1098, 2622, -1920, -6733]]]
  g := ![![![32, -6, 15, -11, -39], ![-15, -5, -7, 7, 27], ![611, -146, 240, -187, -687], ![-3538, 930, -1422, 1073, 3900], ![1264, -324, 507, -385, -1402]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-4729, 1686, -4011, 2939, 10305]] ![![-1, -6, 15, -11, -39]]
  ![![47, 0, 0, 0, 0]] where
 M := ![![![-47, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0, 0, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0, 0, 0]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![0, 0, 0, 0, 53]] where
  M :=![![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![0, 0, 0, 0, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 5 2 5 [3, 18, 46, 31, 34, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [24, 39, 5, 32, 8], [40, 48, 26, 24, 37], [10, 44, 25, 34, 29], [51, 27, 50, 16, 32], [0, 1]]
 g := ![![[45, 1, 7, 0, 16], [17, 31, 33, 25], [0, 28, 16, 4, 38], [19, 1], []], ![[0, 16, 23, 13, 20, 29, 14, 12], [40, 50, 28, 43], [2, 17, 21, 12, 6, 45, 49, 18], [14, 45, 1, 46], [40, 47, 21, 52, 10, 16, 25, 35]], ![[24, 26, 11, 18, 47, 0, 29, 11], [25, 4, 50, 13], [44, 42, 47, 22, 39, 11, 8, 4], [0, 4, 6, 52], [36, 31, 35, 11, 20, 21, 21, 38]], ![[18, 40, 24, 41, 17, 35, 48, 29], [13, 13, 47, 15], [2, 22, 36, 28, 14, 39, 2, 9], [31, 20, 17, 36], [31, 34, 49, 10, 45, 40, 40, 9]], ![[13, 33, 5, 30, 27, 18, 36, 3], [27, 20, 0, 42], [35, 26, 10, 5, 15, 41, 24, 35], [20, 4, 49, 38], [10, 32, 24, 51, 2, 27, 22, 14]]]
 h' := ![![[24, 39, 5, 32, 8], [2, 25, 5, 38, 49], [0, 38, 35, 23, 48], [49, 26, 9, 1, 12], [0, 0, 0, 1], [0, 1]], ![[40, 48, 26, 24, 37], [14, 20, 42, 21, 9], [9, 20, 31, 11, 34], [10, 43, 13, 40, 28], [30, 16, 22, 5, 24], [24, 39, 5, 32, 8]], ![[10, 44, 25, 34, 29], [40, 9, 7, 7, 7], [3, 52, 0, 26, 38], [40, 51, 40, 50, 38], [27, 10, 30, 4, 23], [40, 48, 26, 24, 37]], ![[51, 27, 50, 16, 32], [39, 10, 26, 12, 52], [48, 30, 6, 47, 11], [49, 31, 13, 39, 24], [6, 32, 7, 7, 47], [10, 44, 25, 34, 29]], ![[0, 1], [31, 42, 26, 28, 42], [35, 19, 34, 52, 28], [6, 8, 31, 29, 4], [15, 48, 47, 36, 12], [51, 27, 50, 16, 32]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26, 2, 16, 8], [], [], []]
 b := ![[], [52, 26, 36, 21, 52], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 5
  hpos := by decide
  P := [3, 18, 46, 31, 34, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-65504806886251254299, 40667680664058768930, -65797672599276319284, 51972905056322870320, 179853664729700784928]
  a := ![-2227, 1653, -2536, 1977, 6950]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1235939752570778383, 767314729510542810, -1241465520741062628, 980620850119299440, 3393465372258505376]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 418195493 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def PBC53 : ContainsPrimesAboveP 53 ![I53N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![53, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 53 (by decide) 𝕀

instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4626245, -2824250, 4579057, -3626821, -12517913]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![4626245, -2824250, 4579057, -3626821, -12517913]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![21, 15, 5, 1, 0], ![40, 30, 9, 0, 1]] where
  M :=![![![4626245, -2824250, 4579057, -3626821, -12517913], ![35378234, -21597959, 35017431, -27735415, -95728315], ![270549550, -165167310, 267790516, -212102453, -732067985], ![1016806440, -620748738, 1006437390, -797144957, -2751332124], ![-188266834, 114934788, -186346971, 147595425, 509423070]]]
  hmulB := by decide  
  f := ![![![-7257, 7230, -9447, 6759, 24109]], ![![10550, -15489, 24115, -17255, -61189]], ![![8218, 5738, -18422, 13199, 46093]], ![![61, -211, 394, -282, -995]], ![![1876, -2152, 3017, -2156, -7667]]]
  g := ![![![9856034, 7239245, 2294481, -3626821, -12517913], ![75372111, 55360724, 17546599, -27735415, -95728315], ![576396957, 423362865, 134184994, -212102453, -732067985], ![2166273483, 1591125243, 504307649, -797144957, -2751332124], ![-401096501, -294604893, -93375114, 147595425, 509423070]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [45, 18, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [52, 49, 25], [6, 9, 34], [0, 1]]
 g := ![![[29, 21, 49], [26, 1, 22], [29, 36], [7, 35, 1], [1]], ![[16, 49, 35, 16], [57, 52, 41, 12], [22, 12], [3, 13, 53, 36], [35, 20, 22, 49]], ![[47, 40, 49, 42], [12, 4, 22, 2], [37, 20], [2, 58, 30, 58], [22, 48, 50, 10]]]
 h' := ![![[52, 49, 25], [10, 5, 7], [39, 2, 50], [39, 29, 53], [14, 41, 58], [0, 1]], ![[6, 9, 34], [44, 26, 11], [29, 34, 28], [55, 41, 22], [29, 9, 13], [52, 49, 25]], ![[0, 1], [21, 28, 41], [8, 23, 40], [27, 48, 43], [52, 9, 47], [6, 9, 34]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56, 25], []]
 b := ![[], [48, 27, 58], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [45, 18, 1, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2112319085, 1836183348, -2865808194, 2155380550, 7818497422]
  a := ![-257, 185, -293, 219, 802]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6103647585, -4492363518, -1423884538, 2155380550, 7818497422]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 205379 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7257, -7230, 9447, -6759, -24109]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![7257, -7230, 9447, -6759, -24109]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![11, 49, 1, 0, 0], ![55, 15, 0, 1, 0], ![20, 43, 0, 0, 1]] where
  M :=![![![7257, -7230, 9447, -6759, -24109], ![-10550, 15489, -24115, 17255, 61189], ![-8218, -5738, 18422, -13199, -46093], ![43344, -39366, 47982, -34253, -122376], ![-10502, 3140, 1769, -1295, -4120]]]
  hmulB := by decide  
  f := ![![![-4626245, 2824250, -4579057, 3626821, 12517913]], ![![-35378234, 21597959, -35017431, 27735415, 95728315]], ![![-34830029, 21263289, -34474818, 27305641, 94244957]], ![![-30541075, 18644947, -30229610, 23943243, 82639696]], ![![-24161392, 14750211, -23914978, 18941760, 65377165]]]
  g := ![![![12835, 11321, 9447, -6759, -24109], ![-32510, -28692, -24115, 17255, 61189], ![24355, 21552, 18422, -13199, -46093], ![65203, 57381, 47982, -34253, -122376], ![2096, 1916, 1769, -1295, -4120]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P1 : CertificateIrreducibleZModOfList' 59 2 2 5 [4, 50, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 58], [0, 1]]
 g := ![![[42, 15], [38, 22], [49], [27, 29], [9, 1]], ![[0, 44], [0, 37], [49], [52, 30], [18, 58]]]
 h' := ![![[9, 58], [25, 30], [22, 50], [10, 7], [23, 18], [0, 1]], ![[0, 1], [0, 29], [0, 9], [14, 52], [8, 41], [9, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [31, 39]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N1 : CertifiedPrimeIdeal' SI59N1 59 where
  n := 2
  hpos := by decide
  P := [4, 50, 1]
  hirr := P59P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-19489573, 13973236, -22226869, 17173537, 60707408]
  a := ![-1955, 1444, -2226, 1724, 6101]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-32774351, -29914098, -22226869, 17173537, 60707408]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N1 B_one_repr
lemma NI59N1 : Nat.card (O ⧸ I59N1) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![4626245, -2824250, 4579057, -3626821, -12517913]] ![![7257, -7230, 9447, -6759, -24109]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0, 0, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0, 0, 0]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![0, 0, 0, 0, 61]] where
  M :=![![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![0, 0, 0, 0, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 5 2 5 [28, 37, 59, 51, 44, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [15, 33, 45, 28, 38], [42, 33, 19, 17, 31], [6, 10, 46, 54, 47], [15, 45, 12, 23, 6], [0, 1]]
 g := ![![[6, 58, 52, 12, 16], [9, 48, 57, 5], [10, 34, 40, 60, 20], [55, 17, 1], []], ![[27, 20, 51, 25, 43, 49, 25, 2], [10, 1, 49, 22], [60, 45, 42, 39, 59, 57, 37, 53], [5, 22, 8, 12, 38, 59, 49, 7], [40, 43, 29, 19, 39, 29, 40, 33]], ![[7, 42, 42, 31, 52, 42, 30, 24], [48, 22, 49, 20], [32, 21, 50, 60, 40, 7, 44, 37], [33, 58, 25, 21, 37, 36, 60, 35], [54, 18, 4, 58, 46, 8, 53, 23]], ![[48, 30, 12, 24, 2, 33, 37, 1], [54, 48, 31, 56], [15, 17, 16, 43, 5, 47, 20, 46], [7, 53, 43, 44, 15, 12, 51, 45], [47, 60, 36, 24, 37, 30, 49, 1]], ![[51, 44, 3, 23, 8, 42, 54, 28], [26, 39, 48, 52], [25, 28, 40, 29, 51, 47, 30, 35], [39, 23, 27, 56, 6, 60, 49, 30], [48, 36, 26, 28, 25, 22, 56, 33]]]
 h' := ![![[15, 33, 45, 28, 38], [7, 20, 9, 2, 57], [25, 1, 16, 37, 26], [46, 51, 2, 59, 9], [0, 0, 0, 1], [0, 1]], ![[42, 33, 19, 17, 31], [38, 42, 6, 51, 17], [14, 7, 35, 50, 12], [42, 12, 17, 47, 8], [59, 10, 14, 37, 26], [15, 33, 45, 28, 38]], ![[6, 10, 46, 54, 47], [50, 12, 5, 3, 29], [28, 56, 13, 55, 9], [49, 38, 55, 14, 47], [47, 53, 46, 35, 3], [42, 33, 19, 17, 31]], ![[15, 45, 12, 23, 6], [14, 59, 15, 45, 14], [1, 23, 35, 13, 42], [11, 21, 45, 10, 54], [59, 40, 35, 18, 6], [6, 10, 46, 54, 47]], ![[0, 1], [49, 50, 26, 21, 5], [44, 35, 23, 28, 33], [47, 0, 3, 53, 4], [18, 19, 27, 31, 26], [15, 45, 12, 23, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27, 48, 39, 39], [], [], []]
 b := ![[], [31, 42, 8, 53, 7], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 5
  hpos := by decide
  P := [28, 37, 59, 51, 44, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-45839144348957567468, 32168449194231403989, -51303810246220056765, 39758950620525479130, 140129491667662890282]
  a := ![-2411, 1781, -2747, 2127, 7524]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-751461382769796188, 527351626134941049, -841046069610164865, 651786075746319330, 2297204781437096562]
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



lemma PB2201I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB2201I1 : PrimesBelowBoundCertificateInterval O 23 61 2201 where
  m := 9
  g := ![1, 4, 3, 1, 4, 2, 1, 2, 1]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB2201I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0]
    · exact ![I31N0, I31N1, I31N2, I31N3]
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0]
    · exact ![I43N0, I43N1, I43N2, I43N3]
    · exact ![I47N0, I47N1]
    · exact ![I53N0]
    · exact ![I59N0, I59N1]
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
    · exact ![20511149]
    · exact ![961, 31, 31, 31]
    · exact ![50653, 37, 37]
    · exact ![115856201]
    · exact ![1849, 43, 43, 43]
    · exact ![4879681, 47]
    · exact ![418195493]
    · exact ![205379, 3481]
    · exact ![844596301]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
      exact NI43N2
      exact NI43N3
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
  β := ![I31N0, I31N1, I31N2, I31N3, I37N1, I37N2, I43N0, I43N1, I43N2, I43N3, I47N1]
  Il := ![[], [I31N0, I31N1, I31N2, I31N3], [I37N1, I37N2], [], [I43N0, I43N1, I43N2, I43N3], [I47N1], [], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
