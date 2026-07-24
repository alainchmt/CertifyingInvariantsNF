
import IdealArithmetic.Examples.NF5_1_421875000_2.RI5_1_421875000_2
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


def P29P0 : CertificateIrreducibleZModOfList' 29 5 2 4 [28, 13, 17, 14, 23, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 5, 27, 8, 20], [20, 3, 15, 5], [6, 28, 2, 21, 1], [8, 21, 14, 24, 8], [0, 1]]
 g := ![![[1, 14, 27, 25, 6], [11, 21, 14, 4], [22, 6, 1], []], ![[19, 13, 27, 27, 18, 16, 2, 25], [5, 6, 11, 1], [25, 14, 23, 17, 14, 11, 25, 24], [25, 9, 19, 5, 22, 24, 6, 25]], ![[22, 6, 21, 11, 15, 6, 23], [22, 26, 0, 16], [9, 25, 12, 23, 25, 4, 1], [24, 16, 21, 19, 9]], ![[7, 7, 11, 0, 17, 23, 13, 20], [12, 14, 19, 1], [22, 21, 24, 22, 8, 8, 4, 20], [14, 28, 1, 26, 22, 18, 11, 1]], ![[0, 1, 15, 19, 25, 12, 16, 12], [1, 2, 2, 4], [10, 11, 24, 13, 19, 16, 12, 10], [24, 6, 18, 18, 5, 5, 24, 19]]]
 h' := ![![[1, 5, 27, 8, 20], [2, 28, 23, 12, 8], [22, 10, 13, 12, 2], [0, 0, 0, 1], [0, 1]], ![[20, 3, 15, 5], [1, 0, 9, 11, 9], [5, 3, 21, 17, 1], [26, 18, 10, 11, 23], [1, 5, 27, 8, 20]], ![[6, 28, 2, 21, 1], [18, 11, 12, 12, 15], [5, 1, 23, 12, 25], [20, 27, 23, 9, 8], [20, 3, 15, 5]], ![[8, 21, 14, 24, 8], [11, 25, 3, 19, 22], [17, 16, 17, 8, 28], [27, 28, 10, 28, 7], [6, 28, 2, 21, 1]], ![[0, 1], [0, 23, 11, 4, 4], [12, 28, 13, 9, 2], [14, 14, 15, 9, 20], [8, 21, 14, 24, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 28, 2, 27], [], [], []]
 b := ![[], [17, 13, 15, 1, 3], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 5
  hpos := by decide
  P := [28, 13, 17, 14, 23, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-135573492, -1424964126, -423053914, -354493158, -2265397640]
  a := ![13, -21, -17, -22, -52]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4674948, -49136694, -14588066, -12223902, -78117160]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0], ![24, 9, 4, 3, 16]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0, 0, 0], ![24, 9, 4, 3, 16]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![17, 18, 8, 6, 1]] where
  M :=![![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]], ![![24, 9, 4, 3, 16], ![78, -25, -18, -29, -72], ![-258, 159, -12, -9, -48], ![-156, -43, 129, 58, 144], ![132, -28, -40, 1, -5]]]
  hmulB := by decide  
  f := ![![![-23, -9, -4, -3, -16], ![31, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![-1, 0, 0, 0, -1], ![2, 0, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![-17, -18, -8, -6, 31]], ![![-8, -9, -4, -3, 16], ![42, 41, 18, 13, -72], ![18, 33, 12, 9, -48], ![-84, -85, -33, -26, 144], ![7, 2, 0, 1, -5]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 4 2 4 [27, 4, 26, 21, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 14, 1, 1], [16, 13, 12, 19], [13, 3, 18, 11], [0, 1]]
 g := ![![[3, 14, 18, 1], [8, 24, 18, 7], [11, 12, 10, 1], []], ![[1, 8, 22, 4, 13, 16], [10, 16, 30, 27, 9, 19], [25, 25, 2, 14], [19, 15, 29, 25, 13, 1]], ![[14, 17, 2, 14, 17, 7], [6, 18, 20, 16, 10, 1], [7, 14, 26, 17, 9, 9], [29, 4, 9, 9, 25, 8]], ![[8, 24, 6, 8, 17, 30], [15, 6, 26, 11, 24, 24], [26, 19, 0, 21, 29, 23], [6, 10, 7, 0, 4, 29]]]
 h' := ![![[12, 14, 1, 1], [1, 16, 27, 30], [13, 4, 16, 10], [0, 0, 0, 1], [0, 1]], ![[16, 13, 12, 19], [30, 18, 1, 27], [5, 27, 18, 22], [6, 18, 13], [12, 14, 1, 1]], ![[13, 3, 18, 11], [21, 10, 13, 23], [5, 8, 12, 24], [27, 26, 9, 21], [16, 13, 12, 19]], ![[0, 1], [22, 18, 21, 13], [3, 23, 16, 6], [20, 18, 9, 9], [13, 3, 18, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [10, 28, 3], []]
 b := ![[], [], [20, 5, 13, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 4
  hpos := by decide
  P := [27, 4, 26, 21, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![36531425049, -472727543719, -282741669945, -319416083952, -1197043228884]
  a := ![183, -306, -242, -307, -729]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![657621494067, 679808083103, 299793682617, 221382041592, -1197043228884]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 923521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0], ![-11, 1, 0, 0, 0]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![31, 0, 0, 0, 0], ![-11, 1, 0, 0, 0]] 
 ![![31, 0, 0, 0, 0], ![20, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![22, 0, 0, 1, 0], ![10, 0, 0, 0, 1]] where
  M :=![![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]], ![![-11, 1, 0, 0, 0], ![0, -11, 1, 0, 0], ![0, 1, -11, 2, 0], ![-6, 9, 7, -2, 24], ![6, -5, -3, -4, -20]]]
  hmulB := by decide  
  f := ![![![-1005238, 120068, -234869, 42222, 14976], ![-2822395, 4712, -673785, -19344, 0]], ![![-670162, 80053, -156580, 28148, 9984], ![-1881606, 3162, -449190, -12896, 0]], ![![-125666, 15013, -29393, 5284, 1872], ![-352831, 590, -84320, -2418, 0]], ![![-712042, 85048, -166364, 29907, 10608], ![-1999192, 3338, -477260, -13702, 0]], ![![-324254, 38739, -75765, 13620, 4831], ![-910404, 1545, -217350, -6240, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-20, 31, 0, 0, 0], ![-3, 0, 31, 0, 0], ![-22, 0, 0, 31, 0], ![-10, 0, 0, 0, 31]], ![![-1, 1, 0, 0, 0], ![7, -11, 1, 0, 0], ![-1, 1, -11, 2, 0], ![-13, 9, 7, -2, 24], ![13, -5, -3, -4, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![31, 0, 0, 0, 0], ![24, 9, 4, 3, 16]] ![![31, 0, 0, 0, 0], ![-11, 1, 0, 0, 0]]
  ![![31, 0, 0, 0, 0]] where
 M := ![![![961, 0, 0, 0, 0], ![-341, 31, 0, 0, 0]], ![![744, 279, 124, 93, 496], ![-186, -124, -62, -62, -248]]]
 hmul := by decide  
 g := ![![![![31, 0, 0, 0, 0]], ![![-11, 1, 0, 0, 0]]], ![![![24, 9, 4, 3, 16]], ![![-6, -4, -2, -2, -8]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0)
instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0, 0, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0, 0, 0]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![0, 0, 0, 0, 37]] where
  M :=![![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![0, 0, 0, 0, 37]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 5 2 5 [20, 29, 31, 4, 1, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 29, 17, 17, 17], [4, 6, 0, 34, 31], [21, 13, 8, 4, 22], [32, 25, 12, 19, 4], [0, 1]]
 g := ![![[14, 1, 15, 8, 25], [17, 23, 19, 33], [1, 13, 34, 36, 1], [], []], ![[36, 34, 28, 24, 22, 1, 31, 31], [10, 10, 33, 1], [31, 34, 20, 29, 19, 10, 7, 15], [7, 8, 15, 28], [19, 14, 30, 30]], ![[36, 3, 23, 3, 15, 10, 5, 23], [18, 7, 18, 34], [22, 25, 1, 36, 35, 14, 11, 19], [34, 6, 10, 34], [20, 13, 0, 36]], ![[22, 26, 32, 22, 8, 20, 7, 13], [1, 5, 27, 9], [12, 27, 34, 34, 30, 10, 9, 15], [23, 2, 12, 3], [1, 35, 25, 3]], ![[3, 22, 10, 34, 20, 11, 11, 34], [8, 3], [2, 0, 7, 20, 36, 12, 14, 1], [9, 27, 23, 30], [25, 35, 25, 16]]]
 h' := ![![[16, 29, 17, 17, 17], [23, 25, 0, 30, 32], [17, 7, 22, 33, 12], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[4, 6, 0, 34, 31], [31, 13, 18, 1, 2], [34, 21, 27, 17, 1], [29, 1, 23, 29, 8], [24, 23, 12, 31, 18], [16, 29, 17, 17, 17]], ![[21, 13, 8, 4, 22], [19, 6, 12, 10, 29], [3, 25, 23, 3, 21], [34, 17, 27, 30, 15], [23, 22, 1, 31, 21], [4, 6, 0, 34, 31]], ![[32, 25, 12, 19, 4], [27, 9, 14, 1, 3], [26, 24, 30, 6, 3], [32, 15, 0, 24, 31], [14, 2, 32, 19, 15], [21, 13, 8, 4, 22]], ![[0, 1], [32, 21, 30, 32, 8], [28, 34, 9, 15], [4, 4, 24, 28, 19], [6, 27, 28, 30, 20], [32, 25, 12, 19, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 21, 16, 23], [], [], []]
 b := ![[], [0, 8, 23, 23, 3], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 5
  hpos := by decide
  P := [20, 29, 31, 4, 1, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1753317964, -405753692, 308681010, -92521682, -633218592]
  a := ![12, -20, -15, -21, -47]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-47386972, -10966316, 8342730, -2500586, -17114016]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 69343957 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def PBC37 : ContainsPrimesAboveP 37 ![I37N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![37, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 37 (by decide) 𝕀

instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10997457899, -3894760320, -2651564902, -3074989254, -6716999478]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![-10997457899, -3894760320, -2651564902, -3074989254, -6716999478]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![6, 0, 18, 1, 0], ![9, 27, 40, 0, 1]] where
  M :=![![![-10997457899, -3894760320, -2651564902, -3074989254, -6716999478], ![-21852061344, -7738928697, -5268686664, -6110035178, -13346746794], ![-43420269696, -15377330640, -10468934561, -12140702754, -26520123126], ![-32212230444, -11407992358, -7766596938, -9006833113, -19674505584], ![27522072156, 9746968524, 6635766564, 7695422034, 16809862165]]]
  hmulB := by decide  
  f := ![![![188453, -306516, 352886, 34866, 429474]], ![![2367648, -1292237, -1350876, -698330, -3028482]], ![![-13980912, 9874212, 2904899, 3127206, 10496418]], ![![-5600046, 3874054, 1346796, 1288599, 4471200]], ![![-12179391, 8841045, 1989874, 2618022, 8356417]]]
  g := ![![![1656231047, 4328395746, 7838493190, -3074989254, -6716999478], ![3290948070, 8600566701, 15575166300, -6110035178, -13346746794], ![6539147682, 17089414482, 30948015611, -12140702754, -26520123126], ![4851202890, 12678138010, 22959429816, -9006833113, -19674505584], ![-4144859013, -10832178291, -19616495528, 7695422034, 16809862165]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [27, 20, 13, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 12, 36], [25, 28, 5], [0, 1]]
 g := ![![[9, 26, 1], [18, 18], [36, 37], [26, 28, 1], []], ![[33, 28, 2, 8], [35, 21], [39, 16], [19, 20, 39, 16], [6, 25]], ![[27, 8, 15, 40], [4, 33], [35, 32], [7, 26, 6, 23], [37, 25]]]
 h' := ![![[3, 12, 36], [22, 1, 40], [37, 12, 31], [36, 36, 18], [0, 0, 1], [0, 1]], ![[25, 28, 5], [14, 38, 8], [4, 35, 29], [14, 5, 37], [11, 15, 28], [3, 12, 36]], ![[0, 1], [11, 2, 34], [18, 35, 22], [26, 0, 27], [36, 26, 12], [25, 28, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 14], []]
 b := ![[], [15, 5, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [27, 20, 13, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5357757, 18055618, 20924672, 17115744, 63593674]
  a := ![-72, 117, 96, 116, 289]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-16595007, -41438380, -69046480, 17115744, 63593674]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 68921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1909, -1606, 970, 1068, 2268]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![1909, -1606, 970, 1068, 2268]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![26, 5, 1, 0, 0], ![17, 1, 0, 1, 0], ![24, 11, 0, 0, 1]] where
  M :=![![![1909, -1606, 970, 1068, 2268], ![7200, 1151, -934, 2480, 5220], ![16440, 2486, 2851, -428, 12540], ![35304, -24206, -18598, -25395, -64176], ![-29952, 12062, 6342, 8608, 17689]]]
  hmulB := by decide  
  f := ![![![91638247715381, 32453773733238, 22094629983606, 25622887810748, 55970577389460]], ![![182086137472272, 64485981048419, 43902256240094, 50912940706104, 111214110952812]], ![![89142247547354, 31569812868525, 21492826680657, 24924983454484, 54446076713688]], ![![48984156339989, 17347786170127, 11810426719994, 13696415783745, 29918419236912]], ![![96900803876664, 34317513068883, 23363469513500, 27094346393600, 59184828144301]]]
  g := ![![![-2339, -792, 970, 1068, 2268], ![-3316, -1319, -934, 2480, 5220], ![-8570, -3641, 2851, -428, 12540], ![60751, 19515, -18598, -25395, -64176], ![-18676, -5435, 6342, 8608, 17689]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P1 : CertificateIrreducibleZModOfList' 41 2 2 5 [5, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 40], [0, 1]]
 g := ![![[20, 33], [21], [33], [6, 37], [1]], ![[0, 8], [21], [33], [37, 4], [1]]]
 h' := ![![[23, 40], [27, 22], [38, 29], [11, 19], [36, 23], [0, 1]], ![[0, 1], [0, 19], [8, 12], [38, 22], [32, 18], [23, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [11, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N1 : CertifiedPrimeIdeal' SI41N1 41 where
  n := 2
  hpos := by decide
  P := [5, 18, 1]
  hirr := P41P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2736, -2415, -4704, -2057, -10623]
  a := ![19, -27, -24, -25, -77]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![10121, 3415, -4704, -2057, -10623]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N1 B_one_repr
lemma NI41N1 : Nat.card (O ⧸ I41N1) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![-10997457899, -3894760320, -2651564902, -3074989254, -6716999478]] ![![1909, -1606, 970, 1068, 2268]]
  ![![41, 0, 0, 0, 0]] where
 M := ![![![-680231, 89790, -102336, -252970, -658050]]]
 hmul := by decide  
 g := ![![![![-16591, 2190, -2496, -6170, -16050]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0, 0, 0], ![-30, -34, -15, -15, -29]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0, 0, 0], ![-30, -34, -15, -15, -29]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![7, 28, 3, 1, 0], ![33, 3, 39, 0, 1]] where
  M :=![![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![0, 0, 0, 0, 43]], ![![-30, -34, -15, -15, -29], ![-84, -35, -52, -49, -99], ![-300, -82, -81, -149, -285], ![-366, -131, -109, -157, -456], ![174, 94, 86, 125, 298]]]
  hmulB := by decide  
  f := ![![![10675, -5120, 8197, 7339, 15409], ![-19135, 12298, 0, 0, 0]], ![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![-462, 259, -360, -322, -678], ![903, -559, 0, 0, 0]], ![![1723, -795, 1318, 1181, 2478], ![-3027, 1963, 0, 0, 0]], ![![7749, -3722, 5952, 5328, 11187], ![-13901, 8931, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-7, -28, -3, 43, 0], ![-33, -3, -39, 0, 43]], ![![24, 11, 27, -15, -29], ![82, 38, 92, -49, -99], ![236, 115, 267, -149, -285], ![367, 131, 422, -157, -456], ![-245, -100, -277, 125, 298]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [2, 10, 21, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 9, 17], [1, 33, 26], [0, 1]]
 g := ![![[11, 34, 10], [37, 22, 21], [19, 10], [1, 22, 1], []], ![[5, 6, 39, 10], [3, 36, 12, 23], [40, 6], [9, 28, 1, 23], [42, 31]], ![[18, 38, 11, 42], [33, 8, 29, 18], [34, 11], [5, 22, 24, 42], [33, 31]]]
 h' := ![![[21, 9, 17], [12, 11, 15], [9, 6, 35], [41, 32, 15], [0, 0, 1], [0, 1]], ![[1, 33, 26], [8, 1, 37], [31, 26, 10], [5, 18, 7], [13, 25, 33], [21, 9, 17]], ![[0, 1], [37, 31, 34], [19, 11, 41], [1, 36, 21], [21, 18, 9], [1, 33, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20, 21], []]
 b := ![[], [35, 12, 19], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [2, 10, 21, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![26564930, -18572032, -836600, -3977552, -10053312]
  a := ![-12, 8, 16, -2, 48]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![8980630, 2859520, 9376168, -3977552, -10053312]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 79507 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0, 0, 0], ![17, -16, 1, 1, 2]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0, 0, 0], ![17, -16, 1, 1, 2]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![24, 37, 1, 0, 0], ![29, 16, 0, 1, 0], ![25, 30, 0, 0, 1]] where
  M :=![![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![0, 0, 0, 0, 43]], ![![17, -16, 1, 1, 2], ![6, 17, -15, 3, 6], ![18, -12, 20, -27, 18], ![132, -156, -120, -139, -408], ![-120, 85, 49, 65, 160]]]
  hmulB := by decide  
  f := ![![![-4823431, -10620231, 9991827, -2053495, -4112462], ![2038114, 28783469, 3268, 0, 0]], ![![-27754747, -61110422, 57494490, -11816129, -23663722], ![11727605, 165624433, 18791, 0, 0]], ![![-26546092, -58449152, 54990702, -11301557, -22633210], ![11216930, 158411773, 17974, 0, 0]], ![![-13580370, -29901233, 28131972, -5781615, -11578628], ![5738329, 81039803, 9196, 0, 0]], ![![-22168108, -48809721, 45921636, -9437704, -18900541], ![9367027, 132286505, 15010, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-24, -37, 43, 0, 0], ![-29, -16, 0, 43, 0], ![-25, -30, 0, 0, 43]], ![![-2, -3, 1, 1, 2], ![3, 8, -15, 3, 6], ![-3, -20, 20, -27, 18], ![401, 436, -120, -139, -408], ![-167, -176, 49, 65, 160]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P1 : CertificateIrreducibleZModOfList' 43 2 2 5 [22, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 42], [0, 1]]
 g := ![![[16, 9], [15, 36], [15], [12, 21], [1]], ![[30, 34], [28, 7], [15], [16, 22], [1]]]
 h' := ![![[35, 42], [14, 40], [7, 37], [37, 12], [21, 35], [0, 1]], ![[0, 1], [38, 3], [12, 6], [27, 31], [42, 8], [35, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [29, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N1 : CertifiedPrimeIdeal' SI43N1 43 where
  n := 2
  hpos := by decide
  P := [22, 8, 1]
  hirr := P43P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2956, -383, 461, 734, 1719]
  a := ![4, 1, 5, 2, -3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1683, -1878, 461, 734, 1719]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N1 B_one_repr
lemma NI43N1 : Nat.card (O ⧸ I43N1) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0, 0, 0], ![-30, -34, -15, -15, -29]] ![![43, 0, 0, 0, 0], ![17, -16, 1, 1, 2]]
  ![![43, 0, 0, 0, 0]] where
 M := ![![![1849, 0, 0, 0, 0], ![731, -688, 43, 43, 86]], ![![-1290, -1462, -645, -645, -1247], ![516, -43, 559, 473, 946]]]
 hmul := by decide  
 g := ![![![![43, 0, 0, 0, 0]], ![![17, -16, 1, 1, 2]]], ![![![-30, -34, -15, -15, -29]], ![![12, -1, 13, 11, 22]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13471, 8187, -1201, 3270, 3050]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-13471, 8187, -1201, 3270, 3050]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![21, 9, 1, 0, 0], ![23, 41, 0, 1, 0], ![2, 13, 0, 0, 1]] where
  M :=![![![-13471, 8187, -1201, 3270, 3050], ![-1320, -492, 21927, 14828, 51030], ![217212, -101091, -49786, -26814, -103398], ![-229092, 221791, -261, 28933, 118008], ![41952, -74747, 9025, -16612, -47789]]]
  hmulB := by decide  
  f := ![![![29159153532838363, 10326742322121553, 7030478255588529, 8153164625635784, 17809754115878230]], ![![57939536941454676, 20519342839757798, 13969632353937351, 16200421678386194, 35388163972354746]], ![![26572861923968277, 9410804656626954, 6406905047323238, 7430013961016142, 16230105462015138]], ![![66629585089417663, 23596931765299838, 16064864455770045, 18630238204961713, 40695849622285156]], ![![15714021891199906, 5565135995180679, 3788761875049162, 4393783491194720, 9597770584753877]]]
  g := ![![![-1480, -3292, -1201, 3270, 3050], ![-19253, -31259, 21927, 14828, 51030], ![44388, 59373, -49786, -26814, -103398], ![-23938, -53111, -261, 28933, 118008], ![7023, 24391, 9025, -16612, -47789]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [29, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 46], [0, 1]]
 g := ![![[40, 7], [29, 34], [26, 14], [14, 37], [1]], ![[4, 40], [22, 13], [1, 33], [5, 10], [1]]]
 h' := ![![[15, 46], [5, 17], [45, 38], [17, 25], [18, 15], [0, 1]], ![[0, 1], [25, 30], [4, 9], [16, 22], [8, 32], [15, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [1, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [29, 32, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![779, -15, -330, -568, -823]
  a := ![4, -9, -6, -10, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![477, 786, -330, -568, -823]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8318365727, -2945957238, -2005616840, -2325890740, -5080670400]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-8318365727, -2945957238, -2005616840, -2325890740, -5080670400]] 
 ![![47, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![31, 0, 1, 0, 0], ![30, 0, 0, 1, 0], ![18, 0, 0, 0, 1]] where
  M :=![![![-8318365727, -2945957238, -2005616840, -2325890740, -5080670400], ![-16528677960, -5853647227, -3985181218, -4621568740, -10095344160], ![-32842652520, -11631257038, -7918595927, -9183104456, -20059552320], ![-24365004612, -8628889862, -5874575026, -6812676969, -14881595952], ![20817416772, 7372508210, 5019226494, 5820739132, 12714809215]]]
  hmulB := by decide  
  f := ![![![12911, -9470, -2316, -2900, -9408]], ![![268, -135, -230, -100, -480]], ![![9559, -7392, -791, -1940, -5568]], ![![10650, -7206, -3086, -2585, -9360]], ![![3462, -2702, -342, -748, -2177]]]
  g := ![![![4826986695, -2945957238, -2005616840, -2325890740, -5080670400], ![9591272038, -5853647227, -3985181218, -4621568740, -10095344160], ![19057955847, -11631257038, -7918595927, -9183104456, -20059552320], ![14138540784, -8628889862, -5874575026, -6812676969, -14881595952], ![-12079944196, 7372508210, 5019226494, 5820739132, 12714809215]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0, 0, 0], ![11, 1, 0, 0, 0]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![47, 0, 0, 0, 0], ![11, 1, 0, 0, 0]] 
 ![![47, 0, 0, 0, 0], ![11, 1, 0, 0, 0], ![20, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![41, 0, 0, 0, 1]] where
  M :=![![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![0, 0, 0, 0, 47]], ![![11, 1, 0, 0, 0], ![0, 11, 1, 0, 0], ![0, 1, 11, 2, 0], ![-6, 9, 7, 20, 24], ![6, -5, -3, -4, 2]]]
  hmulB := by decide  
  f := ![![![-1347399, -202052, -968196, -161680, 18432], ![5737384, -6956, 4160440, -36096, 0]], ![![-336861, -50514, -242049, -40420, 4608], ![1434394, -1739, 1040110, -9024, 0]], ![![-617548, -92609, -443684, -74090, 8448], ![2629592, -3148, 1906555, -16544, 0]], ![![-56152, -8426, -40344, -6737, 768], ![239102, -264, 173360, -1504, 0]], ![![-1175385, -176263, -844597, -141040, 16079], ![5004928, -6045, 3629320, -31488, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-11, 47, 0, 0, 0], ![-20, 0, 47, 0, 0], ![-2, 0, 0, 47, 0], ![-41, 0, 0, 0, 47]], ![![0, 1, 0, 0, 0], ![-3, 11, 1, 0, 0], ![-5, 1, 11, 2, 0], ![-27, 9, 7, 20, 24], ![1, -5, -3, -4, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2

def I47N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0, 0, 0], ![23, 1, 0, 0, 0]] i)))

def SI47N3: IdealEqSpanCertificate' Table ![![47, 0, 0, 0, 0], ![23, 1, 0, 0, 0]] 
 ![![47, 0, 0, 0, 0], ![23, 1, 0, 0, 0], ![35, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![12, 0, 0, 0, 1]] where
  M :=![![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![0, 0, 0, 0, 47]], ![![23, 1, 0, 0, 0], ![0, 23, 1, 0, 0], ![0, 1, 23, 2, 0], ![-6, 9, 7, 32, 24], ![6, -5, -3, -4, 14]]]
  hmulB := by decide  
  f := ![![![-17489188, -1376883, -22310980, -1926906, 11088], ![35733113, -715387, 45629715, -21714, 0]], ![![-9160880, -721209, -11686523, -1009316, 5808], ![18717093, -374731, 23900910, -11374, 0]], ![![-13324896, -1049033, -16998579, -1468096, 8448], ![27224821, -545058, 34764960, -16544, 0]], ![![-3331310, -262277, -4249726, -367031, 2112], ![6806381, -136241, 8691405, -4136, 0]], ![![-4465352, -351559, -5696421, -491976, 2831], ![9123404, -182625, 11650140, -5544, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-23, 47, 0, 0, 0], ![-35, 0, 47, 0, 0], ![-9, 0, 0, 47, 0], ![-12, 0, 0, 0, 47]], ![![0, 1, 0, 0, 0], ![-12, 23, 1, 0, 0], ![-18, 1, 23, 2, 0], ![-22, 9, 7, 32, 24], ![2, -5, -3, -4, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N3 : Nat.card (O ⧸ I47N3) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N3)

lemma isPrimeI47N3 : Ideal.IsPrime I47N3 := prime_ideal_of_norm_prime hp47.out _ NI47N3
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-13471, 8187, -1201, 3270, 3050]] ![![-8318365727, -2945957238, -2005616840, -2325890740, -5080670400]]
  ![![-223, 47, -119, -214, -490]] where
 M := ![![![-223, 47, -119, -214, -490]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![-223, 47, -119, -214, -490]] ![![47, 0, 0, 0, 0], ![11, 1, 0, 0, 0]]
  ![![47, 0, 0, 0, 0], ![67, 6, 21, 20, 53]] where
 M := ![![![-10481, 2209, -5593, -10058, -23030], ![-4109, 699, -1290, -2558, -6116]]]
 hmul := by decide  
 g := ![![![![45, 71, -35, -134, -278], ![-188, 0, 0, 0, 0]], ![![-19, 21, -6, -34, -76], ![-48, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI47N2 : IdealMulLeCertificate' Table 
  ![![47, 0, 0, 0, 0], ![67, 6, 21, 20, 53]] ![![47, 0, 0, 0, 0], ![23, 1, 0, 0, 0]]
  ![![47, 0, 0, 0, 0]] where
 M := ![![![2209, 0, 0, 0, 0], ![1081, 47, 0, 0, 0]], ![![3149, 282, 987, 940, 2491], ![1739, 141, 470, 470, 1222]]]
 hmul := by decide  
 g := ![![![![47, 0, 0, 0, 0]], ![![23, 1, 0, 0, 0]]], ![![![67, 6, 21, 20, 53]], ![![37, 3, 10, 10, 26]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0, 0, 0], ![-30, -20, -9, -9, -17]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0, 0, 0], ![-30, -20, -9, -9, -17]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![3, 10, 39, 1, 0], ![22, 52, 36, 0, 1]] where
  M :=![![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![0, 0, 0, 0, 53]], ![![-30, -20, -9, -9, -17], ![-48, -35, -32, -31, -63], ![-192, -44, -63, -91, -177], ![-234, -77, -59, -103, -264], ![114, 54, 50, 75, 166]]]
  hmulB := by decide  
  f := ![![![15025, 11960, 15912, 15264, 31712], ![-28408, 34344, 0, 0, 0]], ![![-414, -329, -441, -423, -879], ![795, -954, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![795, 630, 825, 791, 1642], ![-1418, 1764, 0, 0, 0]], ![![5834, 4644, 6174, 5922, 12303], ![-11006, 13320, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-3, -10, -39, 53, 0], ![-22, -52, -36, 0, 53]], ![![7, 18, 18, -9, -17], ![27, 67, 65, -31, -63], ![75, 190, 186, -91, -177], ![111, 277, 254, -103, -264], ![-71, -176, -167, 75, 166]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [29, 27, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 8, 45], [28, 44, 8], [0, 1]]
 g := ![![[3, 19, 17], [24, 38], [33, 15, 10], [2, 36], [1]], ![[37, 47, 0, 12], [40, 29], [25, 29, 19, 8], [31, 25], [30, 1, 50, 18]], ![[11, 10, 0, 2], [22, 17], [40, 46, 37, 33], [33, 1], [4, 36, 23, 35]]]
 h' := ![![[19, 8, 45], [2, 42, 21], [50, 37, 12], [41, 44, 40], [24, 26, 47], [0, 1]], ![[28, 44, 8], [16, 44, 5], [40, 8, 20], [2, 28, 30], [0, 34, 5], [19, 8, 45]], ![[0, 1], [47, 20, 27], [46, 8, 21], [50, 34, 36], [0, 46, 1], [28, 44, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 6], []]
 b := ![[], [50, 17, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [29, 27, 6, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6531063, -5498720, 560824, -1097596, -2157532]
  a := ![-17, 23, 27, 19, 71]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1080935, 2220168, 2283740, -1097596, -2157532]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 148877 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0, 0, 0], ![-10, 22, 1, 1, 2]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0, 0, 0], ![-10, 22, 1, 1, 2]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![23, 28, 1, 0, 0], ![49, 44, 0, 1, 0], ![12, 28, 0, 0, 1]] where
  M :=![![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![0, 0, 0, 0, 53]], ![![-10, 22, 1, 1, 2], ![6, -10, 23, 3, 6], ![18, 26, -7, 49, 18], ![-96, 186, 146, 176, 504], ![108, -105, -65, -87, -209]]]
  hmulB := by decide  
  f := ![![![66192617, -105525240, 288720000, 38473352, 76883344], ![-47217382, -663271150, -41976, 0, 0]], ![![25739364, -41034075, 112270322, 14960570, 29896500], ![-18360684, -257916550, -16324, 0, 0]], ![![42288559, -67417040, 184454899, 24579518, 49118556], ![-30165822, -423744850, -26818, 0, 0]], ![![82565473, -131627088, 360135362, 47989799, 95900564], ![-58896656, -827332350, -52360, 0, 0]], ![![28585162, -45570886, 124683189, 16614645, 33201927], ![-20390713, -286432400, -18128, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-23, -28, 53, 0, 0], ![-49, -44, 0, 53, 0], ![-12, -28, 0, 0, 53]], ![![-2, -2, 1, 1, 2], ![-14, -18, 23, 3, 6], ![-46, -46, -7, 49, 18], ![-342, -486, 146, 176, 504], ![158, 215, -65, -87, -209]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P1 : CertificateIrreducibleZModOfList' 53 2 2 5 [43, 37, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [16, 52], [0, 1]]
 g := ![![[44, 37], [9], [15, 6], [1], [16, 1]], ![[0, 16], [9], [5, 47], [1], [32, 52]]]
 h' := ![![[16, 52], [12, 39], [44, 50], [11, 18], [1, 1], [0, 1]], ![[0, 1], [0, 14], [49, 3], [34, 35], [17, 52], [16, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [33, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N1 : CertifiedPrimeIdeal' SI53N1 53 where
  n := 2
  hpos := by decide
  P := [43, 37, 1]
  hirr := P53P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![879, -618, -1280, -408, -2958]
  a := ![-14, 21, 18, 20, 57]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1619, 2566, -1280, -408, -2958]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N1 B_one_repr
lemma NI53N1 : Nat.card (O ⧸ I53N1) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0, 0, 0], ![-30, -20, -9, -9, -17]] ![![53, 0, 0, 0, 0], ![-10, 22, 1, 1, 2]]
  ![![53, 0, 0, 0, 0]] where
 M := ![![![2809, 0, 0, 0, 0], ![-530, 1166, 53, 53, 106]], ![![-1590, -1060, -477, -477, -901], ![-954, -583, -636, -636, -1325]]]
 hmul := by decide  
 g := ![![![![53, 0, 0, 0, 0]], ![![-10, 22, 1, 1, 2]]], ![![![-30, -20, -9, -9, -17]], ![![-18, -11, -12, -12, -25]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-271807, 52709, 259311, 77938, 433562]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-271807, 52709, 259311, 77938, 433562]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![58, 15, 30, 1, 0], ![10, 15, 13, 0, 1]] where
  M :=![![![-271807, 52709, 259311, 77938, 433562], ![2133744, -1478864, -702411, -514184, -2031546], ![-9104172, 6961407, 1016486, 2093706, 5943498], ![10482504, -8741479, 2244633, -1191741, -605496], ![-1997100, 2024935, -1446113, -110392, -1600919]]]
  hmulB := by decide  
  f := ![![![-67531026968220338513, -23916178275329041149, -16282208471619540035, -18882289555836616824, -41246430015270528362]], ![![-134184842756603469228, -47521691366016788154, -32352915120373773831, -37519302884686518038, -81957079202644048518]], ![![-266626657907745182880, -94426087825935662811, -64285573950890268866, -74551239392350015932, -162849556408679996250]], ![![-239426685973031785846, -84793191554704923833, -57727468242359898328, -66945879766713290057, -146236426278874058374]], ![![-101444531066696641570, -35926678431678669704, -24458994291778477330, -28364813855990275216, -61960034356407890319]]]
  g := ![![![-154709, -129149, -130765, 77938, 433562], ![885964, 622154, 697173, -514184, -2031546], ![-3219900, -1925367, -2356952, 2093706, 5943498], ![1451838, 308764, 777429, -1191741, -605496], ![346014, 469400, 384366, -110392, -1600919]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [54, 27, 21, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [24, 19, 20], [14, 39, 39], [0, 1]]
 g := ![![[52, 9, 9], [29, 57, 29], [37, 45], [38, 15, 28], [1]], ![[55, 4, 43, 53], [40, 20, 38, 53], [11, 4], [48, 31, 57, 21], [40, 35, 58, 35]], ![[22, 57, 30, 42], [13, 58, 48, 14], [26, 12], [8, 9, 10, 40], [57, 44, 40, 24]]]
 h' := ![![[24, 19, 20], [27, 33, 3], [0, 48, 18], [13, 18, 24], [5, 32, 38], [0, 1]], ![[14, 39, 39], [47, 30, 10], [1, 44, 10], [51, 50, 57], [41, 8, 57], [24, 19, 20]], ![[0, 1], [3, 55, 46], [57, 26, 31], [35, 50, 37], [20, 19, 23], [14, 39, 39]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48, 15], []]
 b := ![[], [42, 43, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [54, 27, 21, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1868, 4066, 5949, 6647, 12744]
  a := ![-2, 6, 5, 7, 12]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-8726, -4861, -6087, 6647, 12744]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 205379 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1375125923, 933881211, 370087473, 324158524, 1155273006]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![-1375125923, 933881211, 370087473, 324158524, 1155273006]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![31, 58, 1, 0, 0], ![45, 45, 0, 1, 0], ![46, 49, 0, 0, 1]] where
  M :=![![![-1375125923, 933881211, 370087473, 324158524, 1155273006], ![4986686892, -3863976764, -262828139, -963490362, -2617652478], ![-9924972696, 9140707885, -2755451864, 1273540376, 435103614], ![-5008653732, 234948759, 8506503907, 2587017781, 14633344488], ![5570821464, -3004422005, -3260014761, -1659116182, -7244457875]]]
  hmulB := by decide  
  f := ![![![7934949846648683, 2810170134500629, 1913172558086267, 2218684171439802, 4846488617424714]], ![![15766826675909472, 5583836860569598, 3801493482305101, 4408548189431896, 9630022557732822]], ![![20199800655231595, 7153778867067690, 4870314877758721, 5648048046444912, 12337583203651524]], ![![18471557617657197, 6541719929933848, 4453623251839043, 5164815569117145, 11282011288060152]], ![![18944479900004578, 6709205811946569, 4567648160651394, 5297048942036148, 11570861564699443]]]
  g := ![![![-1365720838, -1554689883, 370087473, 324158524, 1155273006], ![2998363381, 3101730390, -262828139, -963490362, -2617652478], ![-31017764, 1530974949, -2755451864, 1273540376, 435103614], ![-17936608838, -22484609456, 8506503907, 2587017781, 14633344488], ![8720958805, 10435849122, -3260014761, -1659116182, -7244457875]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P1 : CertificateIrreducibleZModOfList' 59 2 2 5 [6, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [40, 58], [0, 1]]
 g := ![![[13, 41], [42, 21], [5], [32, 1], [40, 1]], ![[1, 18], [56, 38], [5], [13, 58], [21, 58]]]
 h' := ![![[40, 58], [43, 49], [18, 27], [44, 51], [55, 1], [0, 1]], ![[0, 1], [56, 10], [36, 32], [19, 8], [36, 58], [40, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [15, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N1 : CertifiedPrimeIdeal' SI59N1 59 where
  n := 2
  hpos := by decide
  P := [6, 19, 1]
  hirr := P59P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1974, 3032, -11920, -5558, -23308]
  a := ![33, -45, -48, -45, -125]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![28708, 35366, -11920, -5558, -23308]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N1 B_one_repr
lemma NI59N1 : Nat.card (O ⧸ I59N1) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-271807, 52709, 259311, 77938, 433562]] ![![-1375125923, 933881211, 370087473, 324158524, 1155273006]]
  ![![59, 0, 0, 0, 0]] where
 M := ![![![87889577380985, 628492523842414, -1579403370762882, -326352879267296, -2339586023649796]]]
 hmul := by decide  
 g := ![![![![1489653853915, 10652415658346, -26769548656998, -5531404733344, -39654000400844]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0, 0, 0], ![169, 50, 57, 56, 140]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0, 0, 0], ![169, 50, 57, 56, 140]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![6, 57, 54, 37, 1]] where
  M :=![![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![0, 0, 0, 0, 61]], ![![169, 50, 57, 56, 140], ![504, 30, 22, 58, 84], ![156, 628, 184, 230, 636], ![966, -400, 154, -82, -144], ![-570, 14, -128, -38, -156]]]
  hmulB := by decide  
  f := ![![![-168, -50, -57, -56, -140], ![61, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![-47, -13, -15, -15, -39], ![17, 0, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![-6, -57, -54, -37, 61]], ![![-11, -130, -123, -84, 140], ![0, -78, -74, -50, 84], ![-60, -584, -560, -382, 636], ![30, 128, 130, 86, -144], ![6, 146, 136, 94, -156]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 4 2 5 [1, 46, 37, 21, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [55, 11, 27, 3], [19, 4, 40, 1], [27, 45, 55, 57], [0, 1]]
 g := ![![[6, 52, 41, 4], [36, 31, 14], [4, 32, 1, 39], [55, 38, 40, 1], []], ![[14, 15, 18, 18, 34, 60], [0, 55, 36], [47, 16, 8, 55, 36, 25], [16, 16, 59, 3, 31, 48], [48, 44, 11, 17, 40, 27]], ![[35, 9, 9, 34, 18, 60], [53, 32, 41], [0, 2, 13, 35, 47, 34], [5, 0, 41, 12, 23, 41], [1, 4, 56, 12, 38, 1]], ![[16, 35, 12, 52], [32, 21, 3], [7, 48, 57, 31, 17, 25], [16, 51, 29, 41, 38, 46], [39, 43, 57, 37, 19, 58]]]
 h' := ![![[55, 11, 27, 3], [41, 58, 45, 59], [57, 3, 15, 21], [6, 55, 20, 51], [0, 0, 0, 1], [0, 1]], ![[19, 4, 40, 1], [5, 22, 38, 52], [35, 56, 29, 55], [24, 35, 53, 54], [41, 34, 38, 4], [55, 11, 27, 3]], ![[27, 45, 55, 57], [17, 48, 10, 11], [58, 48, 27, 38], [29, 56, 14, 20], [26, 12, 35, 38], [19, 4, 40, 1]], ![[0, 1], [10, 55, 29], [15, 15, 51, 8], [31, 37, 35, 58], [2, 15, 49, 18], [27, 45, 55, 57]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [43, 6, 60], []]
 b := ![[], [], [1, 11, 36, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 4
  hpos := by decide
  P := [1, 46, 37, 21, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3372551, 2395906, -385489, 154689, 132627]
  a := ![6, -8, -9, -9, -23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-68333, -84653, -123727, -77910, 132627]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 13845841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0, 0, 0], ![-25, 1, 0, 0, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0, 0, 0], ![-25, 1, 0, 0, 0]] 
 ![![61, 0, 0, 0, 0], ![36, 1, 0, 0, 0], ![46, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![29, 0, 0, 0, 1]] where
  M :=![![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![0, 0, 0, 0, 61]], ![![-25, 1, 0, 0, 0], ![0, -25, 1, 0, 0], ![0, 1, -25, 2, 0], ![-6, 9, 7, -16, 24], ![6, -5, -3, -4, -34]]]
  hmulB := by decide  
  f := ![![![-7285815, 1029873, -25749135, 2058384, 3864], ![-17775034, -716018, -62859280, -9821, 0]], ![![-4434912, 626890, -15673669, 1252952, 2352], ![-10819752, -435845, -38262860, -5978, 0]], ![![-5701970, 805993, -20151432, 1610904, 3024], ![-13910964, -560345, -49194060, -7686, 0]], ![![-950298, 134349, -3358585, 268485, 504], ![-2318420, -93348, -8199040, -1281, 0]], ![![-3463735, 489610, -12241392, 978576, 1837], ![-8450394, -340405, -29883920, -4669, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-36, 61, 0, 0, 0], ![-46, 0, 61, 0, 0], ![-8, 0, 0, 61, 0], ![-29, 0, 0, 0, 61]], ![![-1, 1, 0, 0, 0], ![14, -25, 1, 0, 0], ![18, 1, -25, 2, 0], ![-20, 9, 7, -16, 24], ![22, -5, -3, -4, -34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0, 0, 0], ![169, 50, 57, 56, 140]] ![![61, 0, 0, 0, 0], ![-25, 1, 0, 0, 0]]
  ![![61, 0, 0, 0, 0]] where
 M := ![![![3721, 0, 0, 0, 0], ![-1525, 61, 0, 0, 0]], ![![10309, 3050, 3477, 3416, 8540], ![-3721, -1220, -1403, -1342, -3416]]]
 hmul := by decide  
 g := ![![![![61, 0, 0, 0, 0]], ![![-25, 1, 0, 0, 0]]], ![![![169, 50, 57, 56, 140]], ![![-61, -20, -23, -22, -56]]]]
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


lemma PB1279I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB1279I1 : PrimesBelowBoundCertificateInterval O 23 61 1279 where
  m := 9
  g := ![1, 2, 1, 2, 2, 4, 2, 2, 2]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB1279I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0]
    · exact ![I31N0, I31N1]
    · exact ![I37N0]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1, I47N2, I47N3]
    · exact ![I53N0, I53N1]
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
    · exact ![20511149]
    · exact ![923521, 31]
    · exact ![69343957]
    · exact ![68921, 1681]
    · exact ![79507, 1849]
    · exact ![2209, 47, 47, 47]
    · exact ![148877, 2809]
    · exact ![205379, 3481]
    · exact ![13845841, 61]
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
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
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
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
  β := ![I31N1, I47N1, I47N2, I47N3, I61N1]
  Il := ![[], [I31N1], [], [], [], [I47N1, I47N2, I47N3], [], [], [I61N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
