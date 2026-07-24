
import IdealArithmetic.Examples.NF5_3_729000000_1.RI5_3_729000000_1
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


def P29P0 : CertificateIrreducibleZModOfList' 29 5 2 4 [10, 20, 15, 11, 21, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 16, 0, 13, 23], [2, 18, 18, 13, 11], [11, 10, 19, 20, 18], [13, 13, 21, 12, 6], [0, 1]]
 g := ![![[25, 1, 11, 7, 1], [24, 16, 11, 4], [24, 8, 1], []], ![[27, 21, 5, 8, 21, 22, 7, 28], [6, 11, 9, 28], [19, 9, 28, 20, 10, 26, 13, 4], [26, 12, 3, 22, 6, 19, 24, 16]], ![[0, 10, 19, 0, 21, 16, 7, 14], [10, 13, 3, 1], [27, 26, 21, 25, 23, 3, 27, 8], [21, 5, 2, 12, 22, 27, 26, 26]], ![[23, 19, 24, 11, 20, 16, 23, 18], [5, 11, 28, 13], [11, 2, 9, 27, 11, 22, 23, 2], [15, 24, 9, 25, 27, 26, 5, 3]], ![[10, 9, 10, 11, 16, 16, 13, 28], [0, 7, 13, 7], [1, 20, 2, 0, 14, 7, 3, 16], [10, 4, 5, 22, 28, 25, 8, 13]]]
 h' := ![![[11, 16, 0, 13, 23], [27, 26, 28, 15, 28], [21, 20, 21, 2, 2], [0, 0, 0, 1], [0, 1]], ![[2, 18, 18, 13, 11], [28, 8, 18, 15, 18], [28, 26, 13, 14, 12], [27, 6, 16, 7, 3], [11, 16, 0, 13, 23]], ![[11, 10, 19, 20, 18], [7, 18, 2, 25, 24], [22, 0, 14, 17, 28], [1, 7, 14, 14, 21], [2, 18, 18, 13, 11]], ![[13, 13, 21, 12, 6], [1, 2, 23, 13, 1], [14, 20, 5, 2, 10], [21, 16, 6, 9, 19], [11, 10, 19, 20, 18]], ![[0, 1], [1, 4, 16, 19, 16], [28, 21, 5, 23, 6], [9, 0, 22, 27, 15], [13, 13, 21, 12, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26, 23, 1, 2], [], [], []]
 b := ![[], [16, 26, 5, 24, 10], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 5
  hpos := by decide
  P := [10, 20, 15, 11, 21, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-13418471091590, -18932182324598, -1459542161682, -6166555348632, -7424336977158]
  a := ![0, -9, 16, 2, -39]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-462705899710, -652833873262, -50329040058, -212639839608, -256011619902]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![12749, 5150, 918, 1469, -2739]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![12749, 5150, 918, 1469, -2739]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![23, 17, 7, 1, 0], ![30, 21, 20, 0, 1]] where
  M :=![![![12749, 5150, 918, 1469, -2739], ![-27390, -11321, -1996, -3245, 6075], ![60750, 26210, 4489, 7585, -13395], ![300, 4, 4, -5, 174], ![35280, 15364, 2610, 4456, -7657]]]
  hmulB := by decide  
  f := ![![![-1261, -830, -204, 421, 159]], ![![1590, -111, -1934, -1825, 2685]], ![![26850, 19630, 8049, -6775, -8265]], ![![5707, 3659, 739, -2014, -477]], ![![17220, 11815, 3696, -5211, -3370]]]
  g := ![![![1972, 1216, 1465, 1469, -2739], ![-4355, -2701, -3251, -3245, 6075], ![9295, 5760, 7074, 7585, -13395], ![-155, -115, -111, -5, 174], ![5242, 3239, 4018, 4456, -7657]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 3 2 4 [7, 17, 18, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 18, 25], [13, 12, 6], [0, 1]]
 g := ![![[0, 26, 28], [7, 0, 2], [23, 19, 14], [1]], ![[7, 24, 15, 20], [20, 6, 2, 5], [22, 21, 6, 20], [22, 0, 4, 1]], ![[23, 26, 20, 11], [21, 28, 6, 22], [2, 6, 20, 12], [26, 15, 12, 30]]]
 h' := ![![[0, 18, 25], [13, 10, 11], [25, 21, 23], [24, 14, 13], [0, 1]], ![[13, 12, 6], [15, 8, 10], [1, 24, 26], [1, 29, 10], [0, 18, 25]], ![[0, 1], [14, 13, 10], [17, 17, 13], [0, 19, 8], [13, 12, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 23], []]
 b := ![[], [18, 3, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 3
  hpos := by decide
  P := [7, 17, 18, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-15811479493, -21996430357, -636742721, -6901252308, -10377705386]
  a := ![3, -125, 119, -69, -298]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![14653176941, 10105053935, 8233101005, -6901252308, -10377705386]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 29791 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1261, 830, 204, -421, -159]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![1261, 830, 204, -421, -159]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![23, 23, 1, 0, 0], ![6, 15, 0, 1, 0], ![17, 30, 0, 0, 1]] where
  M :=![![![1261, 830, 204, -421, -159], ![-1590, 111, 1934, 1825, -2685], ![-26850, -19630, -8049, 6775, 8265], ![9060, 3004, -4136, -6333, 6234], ![-1260, -896, -330, 346, 325]]]
  hmulB := by decide  
  f := ![![![-12749, -5150, -918, -1469, 2739]], ![![27390, 11321, 1996, 3245, -6075]], ![![8903, 3733, 655, 1073, -2043]], ![![10776, 4481, 788, 1286, -2415]], ![![18377, 7636, 1344, 2191, -4130]]]
  g := ![![![58, 233, 204, -421, -159], ![-367, 284, 1934, 1825, -2685], ![-738, -5938, -8049, 6775, 8265], ![1168, 197, -4136, -6333, 6234], ![-41, -266, -330, 346, 325]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P1 : CertificateIrreducibleZModOfList' 31 2 2 4 [6, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 30], [0, 1]]
 g := ![![[23, 8], [7, 5], [14, 16], [17, 1]], ![[4, 23], [30, 26], [7, 15], [3, 30]]]
 h' := ![![[17, 30], [20, 15], [9, 6], [22, 4], [0, 1]], ![[0, 1], [27, 16], [18, 25], [28, 27], [17, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [1, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N1 : CertifiedPrimeIdeal' SI31N1 31 where
  n := 2
  hpos := by decide
  P := [6, 14, 1]
  hirr := P31P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![12801, 16036, -1250, 3752, 10068]
  a := ![1, -9, 11, -3, -27]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4907, -10114, -1250, 3752, 10068]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N1 B_one_repr
lemma NI31N1 : Nat.card (O ⧸ I31N1) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![12749, 5150, 918, 1469, -2739]] ![![1261, 830, 204, -421, -159]]
  ![![31, 0, 0, 0, 0]] where
 M := ![![![-31, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![581, 291, -77, -297, 151]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![581, 291, -77, -297, 151]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![29, 26, 1, 0, 0], ![6, 32, 0, 1, 0], ![15, 35, 0, 0, 1]] where
  M :=![![![581, 291, -77, -297, 151], ![1510, 1560, 1333, 131, -1631], ![-16310, -9635, -464, 6675, -845], ![-1600, -2905, -3717, -1535, 4736], ![-780, -499, -1, 278, -107]]]
  hmulB := by decide  
  f := ![![![46585617, 22032095, 3604905, 6489199, -11338477]], ![![-113384770, -53623906, -8773979, -15794057, 27596717]], ![![-35704161, -16885828, -2762871, -4973448, 8690032]], ![![-90791194, -42938555, -7025635, -12646859, 22097666]], ![![-84062115, -39756120, -6504923, -11709524, 20459875]]]
  g := ![![![63, 176, -77, -297, 151], ![-364, 535, 1333, 131, -1631], ![-817, -4908, -464, 6675, -845], ![1199, -619, -3717, -1535, 4736], ![-22, -152, -1, 278, -107]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [26, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 36], [0, 1]]
 g := ![![[32, 10], [26], [25, 33], [28], [1]], ![[0, 27], [26], [23, 4], [28], [1]]]
 h' := ![![[19, 36], [24, 26], [16, 27], [22, 25], [11, 19], [0, 1]], ![[0, 1], [0, 11], [11, 10], [16, 12], [2, 18], [19, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [9, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [26, 18, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![351825, 433168, -35548, 90523, 273342]
  a := ![1, 45, -57, 10, 141]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-88123, -300170, -35548, 90523, 273342]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![49, 16, 6, 5, -13]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![49, 16, 6, 5, -13]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![13, 28, 1, 0, 0], ![8, 27, 0, 1, 0], ![11, 5, 0, 0, 1]] where
  M :=![![![49, 16, 6, 5, -13], ![-130, -59, -12, 3, 17], ![170, 0, -51, -55, 35], ![100, 54, 26, -33, -38], ![60, -18, 0, -10, -31]]]
  hmulB := by decide  
  f := ![![![112533, 53220, 8708, 15675, -27389]], ![![-273890, -129531, -21194, -38151, 66661]], ![![-149713, -70804, -11585, -20854, 36438]], ![![-176218, -83339, -13636, -24546, 42889]], ![![6849, 3239, 530, 954, -1667]]]
  g := ![![![2, -6, 6, 5, -13], ![-5, 3, -12, 3, 17], ![24, 74, -51, -55, 35], ![12, 11, 26, -33, -38], ![13, 11, 0, -10, -31]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P1 : CertificateIrreducibleZModOfList' 37 2 2 5 [28, 28, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 36], [0, 1]]
 g := ![![[1, 4], [28], [20, 9], [7], [1]], ![[0, 33], [28], [27, 28], [7], [1]]]
 h' := ![![[9, 36], [18, 35], [32, 18], [33, 3], [9, 9], [0, 1]], ![[0, 1], [0, 2], [9, 19], [23, 34], [16, 28], [9, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [20, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N1 : CertifiedPrimeIdeal' SI37N1 37 where
  n := 2
  hpos := by decide
  P := [28, 28, 1]
  hirr := P37P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![41761, 39228, -163, -2507, 15910]
  a := ![-1, -6, 21, 13, -50]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3002, 863, -163, -2507, 15910]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N1 B_one_repr
lemma NI37N1 : Nat.card (O ⧸ I37N1) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8023, -2492, -520, -663, 1429]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![-8023, -2492, -520, -663, 1429]] 
 ![![37, 0, 0, 0, 0], ![20, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![13, 0, 0, 1, 0], ![33, 0, 0, 0, 1]] where
  M :=![![![-8023, -2492, -520, -663, 1429], ![14290, 4433, 926, 1179, -2549], ![-25490, -7940, -1653, -2115, 4525], ![-2620, -826, -170, -221, 458], ![-14800, -4622, -960, -1232, 2619]]]
  hmulB := by decide  
  f := ![![![-13419, -6344, -1038, -1877, 3269]], ![![-6370, -3011, -492, -891, 1551]], ![![-4699, -2224, -365, -652, 1144]], ![![-4631, -2190, -360, -650, 1131]], ![![-13211, -6246, -1022, -1847, 3218]]]
  g := ![![![187, -2492, -520, -663, 1429], ![-326, 4433, 926, 1179, -2549], ![623, -7940, -1653, -2115, 4525], ![77, -826, -170, -221, 458], ![377, -4622, -960, -1232, 2619]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![581, 291, -77, -297, 151]] ![![49, 16, 6, 5, -13]]
  ![![-43091, -26629, -3801, 16304, 1304]] where
 M := ![![![-43091, -26629, -3801, 16304, 1304]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![-43091, -26629, -3801, 16304, 1304]] ![![-8023, -2492, -520, -663, 1429]]
  ![![37, 0, 0, 0, 0]] where
 M := ![![![62493, 22163, 8399, 3145, -16835]]]
 hmul := by decide  
 g := ![![![![1689, 599, 227, 85, -455]]]]
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


def P41P0 : CertificateIrreducibleZModOfList' 41 5 2 5 [13, 33, 24, 28, 4, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 29, 23, 21, 29], [4, 4, 36, 16, 29], [30, 17, 7, 29, 10], [37, 31, 16, 16, 14], [0, 1]]
 g := ![![[31, 23, 18, 15, 5], [8, 0, 7, 37], [21, 11, 37, 16], [1], []], ![[7, 24, 8, 7, 31, 37, 30, 13], [27, 17, 37, 25], [4, 16, 24, 25], [24, 33, 7, 8, 32, 6, 30, 17], [24, 13, 27, 21]], ![[18, 30, 16, 26, 29, 29, 4, 3], [6, 29, 37, 31], [35, 3, 31, 33], [11, 24, 35, 20, 2, 16, 30, 35], [5, 20, 24, 21]], ![[35, 16, 8, 38, 37, 0, 19, 23], [3, 13, 17, 21], [7, 32, 14, 9], [12, 16, 16, 17, 22, 24, 1, 31], [18, 3, 16, 18]], ![[6, 34, 23, 3, 14, 30, 39, 38], [9, 33, 1, 20], [13, 29, 36, 37], [12, 36, 25, 3, 24, 34, 27, 19], [0, 4, 33, 32]]]
 h' := ![![[7, 29, 23, 21, 29], [11, 39, 8, 25, 13], [19, 22, 37, 31, 23], [28, 8, 17, 13, 37], [0, 0, 1], [0, 1]], ![[4, 4, 36, 16, 29], [23, 33, 38, 17, 37], [28, 8, 18, 15, 36], [30, 14, 14, 37, 5], [24, 19, 12, 13, 24], [7, 29, 23, 21, 29]], ![[30, 17, 7, 29, 10], [36, 40, 37, 15, 25], [14, 0, 30, 3, 20], [31, 10, 2, 14, 19], [33, 17, 32, 2, 12], [4, 4, 36, 16, 29]], ![[37, 31, 16, 16, 14], [0, 36, 7, 36, 21], [11, 25, 1, 18, 29], [15, 6, 17, 22, 3], [10, 18, 11, 25, 9], [30, 17, 7, 29, 10]], ![[0, 1], [1, 16, 33, 30, 27], [35, 27, 37, 15, 15], [9, 3, 32, 37, 18], [16, 28, 26, 1, 37], [37, 31, 16, 16, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 0, 13, 30], [], [], []]
 b := ![[], [30, 4, 34, 24, 23], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 5
  hpos := by decide
  P := [13, 33, 24, 28, 4, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2113395375347, -930069693634, -825739651090, 1176081408646, 1463250650988]
  a := ![0, -2, -18, -26, 44]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-51546228667, -22684626674, -20139991490, 28684912406, 35689040268]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-66611, -31509, -5155, -9281, 16215]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![-66611, -31509, -5155, -9281, 16215]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![42, 24, 12, 34, 1]] where
  M :=![![![-66611, -31509, -5155, -9281, 16215], ![162150, 76698, 12549, 22591, -39471], ![-394710, -186695, -30546, -54985, 96075], ![15000, 7091, 1159, 2087, -3648], ![-227960, -107823, -17641, -31758, 55487]]]
  hmulB := by decide  
  f := ![![![7, 1, 1, 1, -3]], ![![-30, -20, -5, -3, 3]], ![![30, -25, -8, -35, -15]], ![![0, -11, 9, -9, -24]], ![![-2, -27, 3, -18, -25]]]
  g := ![![![-17387, -9783, -4645, -13037, 16215], ![42324, 23814, 11307, 31735, -39471], ![-103020, -57965, -27522, -77245, 96075], ![3912, 2201, 1045, 2933, -3648], ![-59498, -33477, -15895, -44612, 55487]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 4 2 5 [8, 34, 2, 1, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 10, 18, 20], [5, 22, 39, 1], [20, 10, 29, 22], [0, 1]]
 g := ![![[14, 1, 42, 15], [42, 0, 30, 25], [4, 20, 1], [42, 1], []], ![[6, 19, 16, 13, 40, 42], [19, 3, 28, 20, 33, 32], [35, 34, 17], [9, 27, 14, 38, 13, 22], [34, 19, 13]], ![[30, 14, 39, 26, 2, 24], [18, 15, 29, 12, 31, 9], [33, 2, 23], [28, 6, 14, 1, 4, 38], [24, 34, 1]], ![[41, 28, 42, 30, 24, 12], [17, 30, 6, 6, 11, 12], [9], [19, 26, 40, 25, 1, 30], [37, 18, 11]]]
 h' := ![![[17, 10, 18, 20], [8, 26, 3, 31], [32, 34, 27, 5], [8, 26, 11, 42], [0, 0, 1], [0, 1]], ![[5, 22, 39, 1], [37, 29, 10, 12], [1, 19, 30, 6], [25, 15, 7, 19], [17, 21, 23, 10], [17, 10, 18, 20]], ![[20, 10, 29, 22], [3, 20, 32, 14], [34, 21, 27, 3], [30, 10, 22, 25], [5, 35, 6, 9], [5, 22, 39, 1]], ![[0, 1], [38, 11, 41, 29], [20, 12, 2, 29], [7, 35, 3], [18, 30, 13, 24], [20, 10, 29, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [13, 14, 29], []]
 b := ![[], [], [31, 17, 13, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 4
  hpos := by decide
  P := [8, 34, 2, 1, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![13581052096, 18283052993, 2152354033, 5335216638, 5660826382]
  a := ![13, -7, 18, 8, -43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5213340836, -2734343725, -1529710757, -4351927450, 5660826382]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 3418801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, -1, -1, -1, 3]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-7, -1, -1, -1, 3]] 
 ![![43, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![29, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![28, 0, 0, 0, 1]] where
  M :=![![![-7, -1, -1, -1, 3], ![30, 20, 5, 3, -3], ![-30, 25, 8, 35, 15], ![0, 11, -9, 9, 24], ![20, 49, 3, 18, 25]]]
  hmulB := by decide  
  f := ![![![66611, 31509, 5155, 9281, -16215]], ![![11720, 5544, 907, 1633, -2853]], ![![54103, 25592, 4187, 7538, -13170]], ![![13593, 6430, 1052, 1894, -3309]], ![![48676, 23025, 3767, 6782, -11849]]]
  g := ![![![-1, -1, -1, -1, 3], ![-6, 20, 5, 3, -3], ![-29, 25, 8, 35, 15], ![-14, 11, -9, 9, 24], ![-33, 49, 3, 18, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![-66611, -31509, -5155, -9281, 16215]] ![![-7, -1, -1, -1, 3]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1303, 386, 84, 101, -247]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![1303, 386, 84, 101, -247]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![37, 34, 40, 1, 0], ![7, 19, 32, 0, 1]] where
  M :=![![![1303, 386, 84, 101, -247], ![-2470, -893, -164, -249, 359], ![3590, 410, 213, 45, -1135], ![100, -332, -4, -121, -266], ![1780, -196, 94, -120, -837]]]
  hmulB := by decide  
  f := ![![![9, -2, -10, -3, 11]], ![![110, 77, 18, -53, -7]], ![![-70, 70, 229, 205, -325]], ![![19, 108, 198, 136, -271]], ![![-1, 79, 162, 118, -223]]]
  g := ![![![-15, 35, 84, 101, -247], ![90, 16, -36, -249, 359], ![210, 435, 739, 45, -1135], ![137, 188, 284, -121, -266], ![257, 421, 674, -120, -837]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [16, 35, 35, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 34, 3], [30, 12, 44], [0, 1]]
 g := ![![[7, 45, 2], [22, 38, 3], [45, 15, 18], [15, 12, 1], []], ![[27, 13, 45, 32], [21, 25, 46, 17], [38, 1, 16, 14], [43, 14, 14, 9], [30, 9]], ![[15, 35, 21, 5], [18, 2, 37, 22], [28, 45, 6, 22], [22, 10, 26, 10], [36, 9]]]
 h' := ![![[29, 34, 3], [24, 22, 40], [32, 43, 35], [42, 35, 26], [0, 0, 1], [0, 1]], ![[30, 12, 44], [15, 2, 29], [2, 22, 32], [9, 33, 41], [32, 26, 12], [29, 34, 3]], ![[0, 1], [14, 23, 25], [19, 29, 27], [22, 26, 27], [42, 21, 34], [30, 12, 44]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22, 4], []]
 b := ![[], [43, 39, 30], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [16, 35, 35, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-68425, -11645, 49033, 50119, -66802]
  a := ![-1, -3, -3, -8, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-30962, -9499, 3871, 50119, -66802]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 103823 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, -2, -10, -3, 11]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![9, -2, -10, -3, 11]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![6, 23, 1, 0, 0], ![5, 14, 0, 1, 0], ![29, 16, 0, 0, 1]] where
  M :=![![![9, -2, -10, -3, 11], ![110, 77, 18, -53, -7], ![-70, 70, 229, 205, -325], ![-380, -268, -96, 105, 94], ![40, 24, 14, 14, -25]]]
  hmulB := by decide  
  f := ![![![1303, 386, 84, 101, -247]], ![![-2470, -893, -164, -249, 359]], ![![-966, -379, -65, -108, 120]], ![![-595, -232, -40, -66, 75]], ![![1, -70, -2, -25, -48]]]
  g := ![![![-5, 2, -10, -3, 11], ![10, 11, 18, -53, -7], ![148, -61, 229, 205, -325], ![-65, -22, -96, 105, 94], ![13, -2, 14, 14, -25]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P1 : CertificateIrreducibleZModOfList' 47 2 2 5 [44, 30, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 46], [0, 1]]
 g := ![![[37, 4], [30, 8], [20, 24], [33, 7], [1]], ![[11, 43], [25, 39], [5, 23], [11, 40], [1]]]
 h' := ![![[17, 46], [43, 45], [13, 14], [5, 27], [3, 17], [0, 1]], ![[0, 1], [9, 2], [16, 33], [41, 20], [10, 30], [17, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [38, 37]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N1 : CertifiedPrimeIdeal' SI47N1 47 where
  n := 2
  hpos := by decide
  P := [44, 30, 1]
  hirr := P47P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![81343, 82950, -2408, -5, 40810]
  a := ![3, 10, -28, -15, 70]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-23142, -10948, -2408, -5, 40810]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N1 B_one_repr
lemma NI47N1 : Nat.card (O ⧸ I47N1) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![1303, 386, 84, 101, -247]] ![![9, -2, -10, -3, 11]]
  ![![47, 0, 0, 0, 0]] where
 M := ![![![47, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![943, -804, 28, -313, -889]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![943, -804, 28, -313, -889]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![17, 8, 30, 1, 0], ![45, 18, 34, 0, 1]] where
  M :=![![![943, -804, 28, -313, -889], ![-8890, -9009, -754, -2963, -2767], ![-27670, -46060, -2887, -15645, -20545], ![-16100, -23870, -1590, -8059, -10058], ![-31800, -49298, -3208, -16684, -21223]]]
  hmulB := by decide  
  f := ![![![771, 392, -94, -387, 191]], ![![1910, 2015, 1744, 211, -2131]], ![![-21310, -12600, -749, 8705, -865]], ![![-11561, -6770, -282, 4796, -633]], ![![-12385, -7076, 32, 5335, -1118]]]
  g := ![![![873, 334, 748, -313, -889], ![3132, 1217, 3438, -2963, -2767], ![21940, 8470, 21981, -15645, -20545], ![10821, 4182, 10984, -8059, -10058], ![22771, 8796, 22998, -16684, -21223]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [13, 17, 36, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [38, 2, 29], [32, 50, 24], [0, 1]]
 g := ![![[46, 34, 1], [31, 16], [52, 41, 36], [42, 24], [1]], ![[11, 14, 10, 36], [28, 7], [21, 22, 39, 11], [20, 37], [37, 12, 5, 9]], ![[48, 10, 13, 16], [25, 40], [10, 7, 28, 46], [49, 9], [19, 30, 16, 44]]]
 h' := ![![[38, 2, 29], [31, 35, 1], [13, 50, 49], [47, 52, 47], [40, 36, 17], [0, 1]], ![[32, 50, 24], [35, 46, 5], [9, 37, 31], [15, 36, 42], [13, 35, 39], [38, 2, 29]], ![[0, 1], [29, 25, 47], [6, 19, 26], [16, 18, 17], [32, 35, 50], [32, 50, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 2], []]
 b := ![[], [22, 22, 31], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [13, 17, 36, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8965887, 10159455, 908413, 1465828, 3136292]
  a := ![1, 5, -13, -6, 31]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2963893, -1094725, -2824535, 1465828, 3136292]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 148877 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-443, -245, -37, -74, 122]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-443, -245, -37, -74, 122]] 
 ![![53, 0, 0, 0, 0], ![25, 1, 0, 0, 0], ![11, 0, 1, 0, 0], ![13, 0, 0, 1, 0], ![20, 0, 0, 0, 1]] where
  M :=![![![-443, -245, -37, -74, 122], ![1220, 640, 99, 192, -322], ![-3220, -1635, -258, -490, 830], ![220, 93, 17, 27, -50], ![-1860, -945, -149, -282, 479]]]
  hmulB := by decide  
  f := ![![![-1191, -1713, -117, -580, -706]], ![![-695, -999, -68, -338, -412]], ![![-1037, -1486, -101, -500, -612]], ![![-691, -992, -68, -335, -408]], ![![-1280, -1837, -125, -620, -757]]]
  g := ![![![87, -245, -37, -74, 122], ![-225, 640, 99, 192, -322], ![571, -1635, -258, -490, 830], ![-31, 93, 17, 27, -50], ![330, -945, -149, -282, 479]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1

def I53N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1157, 357, 75, 96, -206]] i)))

def SI53N2: IdealEqSpanCertificate' Table ![![1157, 357, 75, 96, -206]] 
 ![![53, 0, 0, 0, 0], ![46, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![31, 0, 0, 0, 1]] where
  M :=![![![1157, 357, 75, 96, -206], ![-2060, -638, -137, -170, 370], ![3700, 1155, 242, 280, -650], ![380, 123, 35, 39, -82], ![2120, 653, 137, 172, -375]]]
  hmulB := by decide  
  f := ![![![-15831, -22679, -1541, -7642, -9338]], ![![-15502, -22210, -1509, -7484, -9146]], ![![-11608, -16637, -1130, -5606, -6854]], ![![-5567, -7980, -542, -2689, -3288]], ![![-20237, -29000, -1970, -9772, -11945]]]
  g := ![![![-175, 357, 75, 96, -206], ![312, -638, -137, -170, 370], ![-576, 1155, 242, 280, -650], ![-55, 123, 35, 39, -82], ![-321, 653, 137, 172, -375]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N2 : Nat.card (O ⧸ I53N2) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N2)

lemma isPrimeI53N2 : Ideal.IsPrime I53N2 := prime_ideal_of_norm_prime hp53.out _ NI53N2
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![943, -804, 28, -313, -889]] ![![-443, -245, -37, -74, 122]]
  ![![95891, 19621, 5429, 4377, -13007]] where
 M := ![![![95891, 19621, 5429, 4377, -13007]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![95891, 19621, 5429, 4377, -13007]] ![![1157, 357, 75, 96, -206]]
  ![![53, 0, 0, 0, 0]] where
 M := ![![![64702347, 20030184, 4188802, 5323585, -11503915]]]
 hmul := by decide  
 g := ![![![![1220799, 377928, 79034, 100445, -217055]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1741, 984, -26, -764, 186]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![1741, 984, -26, -764, 186]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![23, 11, 43, 20, 1]] where
  M :=![![![1741, 984, -26, -764, 186], ![1860, 2893, 3462, 1248, -4398], ![-43980, -27960, -5249, 15780, 3090], ![2160, -3492, -8952, -6215, 11976], ![-1980, -1224, -172, 746, 55]]]
  hmulB := by decide  
  f := ![![![-841, -360, -62, -104, 186]], ![![1860, 791, 138, 228, -438]], ![![-4380, -2040, -331, -600, 930]], ![![0, -36, 0, -13, -48]], ![![-3217, -1513, -243, -446, 661]]]
  g := ![![![-43, -18, -136, -76, 186], ![1746, 869, 3264, 1512, -4398], ![-1950, -1050, -2341, -780, 3090], ![-4632, -2292, -8880, -4165, 11976], ![-55, -31, -43, -6, 55]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 4 2 5 [22, 31, 50, 23, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [13, 53, 40, 48], [48, 13, 2, 19], [34, 51, 17, 51], [0, 1]]
 g := ![![[45, 41, 41, 28], [3, 9, 25, 48], [33, 33, 7], [14, 7, 36, 1], []], ![[3, 41, 38, 45, 33, 48], [53, 37, 14, 43, 13, 1], [50, 56, 25], [37, 49, 6, 53, 20, 49], [21, 20, 11, 54, 57, 26]], ![[51, 5, 54, 14, 13, 4], [20, 30, 37, 48, 58, 21], [50, 40, 21], [57, 43, 58, 43, 15, 22], [18, 7, 41, 53, 51, 15]], ![[42, 21, 29, 40, 3, 45], [41, 49, 18, 9, 54, 48], [42, 0, 29], [57, 5, 29, 25, 9, 48], [58, 46, 57, 15, 54, 19]]]
 h' := ![![[13, 53, 40, 48], [52, 31, 43, 21], [33, 28, 16, 15], [46, 2, 2, 19], [0, 0, 0, 1], [0, 1]], ![[48, 13, 2, 19], [53, 33, 44, 1], [11, 36, 31, 4], [7, 58, 49, 54], [24, 56, 7, 28], [13, 53, 40, 48]], ![[34, 51, 17, 51], [18, 56, 20, 17], [22, 0, 47, 23], [1, 35, 37, 27], [43, 54, 33, 47], [48, 13, 2, 19]], ![[0, 1], [15, 57, 11, 20], [42, 54, 24, 17], [50, 23, 30, 18], [32, 8, 19, 42], [34, 51, 17, 51]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [13, 36, 36], []]
 b := ![[], [], [42, 15, 42, 54], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 4
  hpos := by decide
  P := [22, 31, 50, 23, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![19011974, 29336735, 4372722, 11467835, 8495248]
  a := ![4, -1, 4, 3, -10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2989470, -1086627, -6117338, -2685375, 8495248]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 12117361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![841, 360, 62, 104, -186]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![841, 360, 62, 104, -186]] 
 ![![59, 0, 0, 0, 0], ![56, 1, 0, 0, 0], ![50, 0, 1, 0, 0], ![46, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![841, 360, 62, 104, -186], ![-1860, -791, -138, -228, 438], ![4380, 2040, 331, 600, -930], ![0, 36, 0, 13, 48], ![2580, 1248, 196, 370, -509]]]
  hmulB := by decide  
  f := ![![![-1741, -984, 26, 764, -186]], ![![-1684, -983, -34, 704, -102]], ![![-730, -360, 111, 380, -210]], ![![-1394, -708, 172, 701, -348]], ![![-173, -96, 6, 78, -23]]]
  g := ![![![-439, 360, 62, 104, -186], ![962, -791, -138, -228, 438], ![-2500, 2040, 331, 600, -930], ![-50, 36, 0, 13, 48], ![-1535, 1248, 196, 370, -509]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![1741, 984, -26, -764, 186]] ![![841, 360, 62, 104, -186]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-561, -454, -58, -144, 212]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-561, -454, -58, -144, 212]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![22, 42, 1, 0, 0], ![54, 52, 0, 1, 0], ![53, 51, 0, 0, 1]] where
  M :=![![![-561, -454, -58, -144, 212], ![2120, 1337, 190, 412, -652], ![-6520, -3690, -551, -1120, 1820], ![760, 294, 54, 83, -164], ![-3760, -2134, -318, -648, 1047]]]
  hmulB := by decide  
  f := ![![![179, 78, -46, -104, 76]], ![![760, 681, 466, -52, -548]], ![![498, 448, 309, -32, -364]], ![![786, 626, 334, -141, -372]], ![![787, 635, 350, -132, -393]]]
  g := ![![![-45, -22, -58, -144, 212], ![168, 85, 190, 412, -652], ![-498, -248, -551, -1120, 1820], ![62, 34, 54, 83, -164], ![-283, -139, -318, -648, 1047]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [2, 44, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 60], [0, 1]]
 g := ![![[22, 41], [19], [6, 52], [22, 19], [17, 1]], ![[48, 20], [19], [36, 9], [40, 42], [34, 60]]]
 h' := ![![[17, 60], [45, 23], [49, 43], [17, 28], [27, 43], [0, 1]], ![[0, 1], [9, 38], [48, 18], [5, 33], [26, 18], [17, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [12, 56]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [2, 44, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![870719, 949384, -41479, 86173, 501798]
  a := ![7, -44, 91, 25, -228]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-483039, -448872, -41479, 86173, 501798]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 6, -28, -24, 36]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![41, 6, -28, -24, 36]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![23, 32, 1, 0, 0], ![24, 59, 0, 1, 0], ![13, 0, 0, 0, 1]] where
  M :=![![![41, 6, -28, -24, 36], ![360, 273, 114, -112, -108], ![-1080, -370, 501, 820, -780], ![-960, -770, -418, 163, 468], ![20, 18, 30, 44, -53]]]
  hmulB := by decide  
  f := ![![![-2059, -454, -128, -104, 492]], ![![4920, 2609, 350, 792, -132]], ![![1783, 1296, 137, 412, 192]], ![![3984, 2409, 292, 747, 96]], ![![-407, 24, -22, 20, 175]]]
  g := ![![![13, 38, -28, -24, 36], ![30, 53, 114, -112, -108], ![-363, -1062, 501, 820, -780], ![-22, 49, -418, 163, 468], ![-17, -58, 30, 44, -53]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P1 : CertificateIrreducibleZModOfList' 61 2 2 5 [27, 44, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 60], [0, 1]]
 g := ![![[31, 52], [5], [9, 14], [25, 19], [17, 1]], ![[0, 9], [5], [3, 47], [43, 42], [34, 60]]]
 h' := ![![[17, 60], [49, 33], [1, 35], [57, 21], [29, 18], [0, 1]], ![[0, 1], [0, 28], [47, 26], [48, 40], [30, 43], [17, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [22, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N1 : CertifiedPrimeIdeal' SI61N1 61 where
  n := 2
  hpos := by decide
  P := [27, 44, 1]
  hirr := P61P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![53412, 55618, -1340, 2906, 26406]
  a := ![1, -9, 23, 9, -57]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5390, -1196, -1340, 2906, 26406]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N1 B_one_repr
lemma NI61N1 : Nat.card (O ⧸ I61N1) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![21, 24, 2, 8, 8]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![21, 24, 2, 8, 8]] 
 ![![61, 0, 0, 0, 0], ![48, 1, 0, 0, 0], ![14, 0, 1, 0, 0], ![43, 0, 0, 1, 0], ![18, 0, 0, 0, 1]] where
  M :=![![![21, 24, 2, 8, 8], ![80, 127, 8, 44, 56], ![560, 780, 51, 260, 320], ![280, 396, 28, 131, 160], ![580, 820, 56, 276, 335]]]
  hmulB := by decide  
  f := ![![![-18679, -8848, -1446, -2608, 4552]], ![![-13952, -6609, -1080, -1948, 3400]], ![![-6106, -2892, -473, -852, 1488]], ![![-13097, -6204, -1014, -1829, 3192]], ![![-6562, -3108, -508, -916, 1599]]]
  g := ![![![-27, 24, 2, 8, 8], ![-148, 127, 8, 44, 56], ![-894, 780, 51, 260, 320], ![-453, 396, 28, 131, 160], ![-942, 820, 56, 276, 335]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-561, -454, -58, -144, 212]] ![![41, 6, -28, -24, 36]]
  ![![18679, 8848, 1446, 2608, -4552]] where
 M := ![![![18679, 8848, 1446, 2608, -4552]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![18679, 8848, 1446, 2608, -4552]] ![![21, 24, 2, 8, 8]]
  ![![61, 0, 0, 0, 0]] where
 M := ![![![-61, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1, I61N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
    exact isPrimeI61N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0 ⊙ MulI61N1)


lemma PB1321I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB1321I1 : PrimesBelowBoundCertificateInterval O 23 61 1321 where
  m := 9
  g := ![1, 2, 3, 1, 2, 2, 3, 2, 3]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB1321I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0]
    · exact ![I31N0, I31N1]
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1, I53N2]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1, I61N2]
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
    · exact ![29791, 961]
    · exact ![1369, 1369, 37]
    · exact ![115856201]
    · exact ![3418801, 43]
    · exact ![103823, 2209]
    · exact ![148877, 53, 53]
    · exact ![12117361, 59]
    · exact ![3721, 3721, 61]
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
      exact NI37N1
      exact NI37N2
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
      exact NI61N2
  β := ![I31N1, I37N2, I43N1, I53N1, I53N2, I59N1, I61N2]
  Il := ![[], [I31N1], [I37N2], [], [I43N1], [], [I53N1, I53N2], [I59N1], [I61N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
