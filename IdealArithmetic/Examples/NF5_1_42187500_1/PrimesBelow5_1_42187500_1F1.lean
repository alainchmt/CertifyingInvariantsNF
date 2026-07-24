
import IdealArithmetic.Examples.NF5_1_42187500_1.RI5_1_42187500_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-100231, -66093, -110147, 122372, 199988]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![-100231, -66093, -110147, 122372, 199988]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![20, 14, 6, 27, 1]] where
  M :=![![![-100231, -66093, -110147, 122372, 199988], ![522348, -132762, -200361, -8410, 468524], ![928638, 798921, 1323270, -1379820, -2443540], ![-3394624, 660475, 973791, 321465, -2404332], ![1556694, -310179, -458405, -137788, 1125683]]]
  hmulB := by decide  
  f := ![![![-9569, -5733, -1077, -4506, -7876]], ![![-20258, -14016, -2325, -8932, -14692]], ![![-38316, -28343, -4500, -19926, -33724]], ![![-33558, -21299, -3817, -16125, -27900]], ![![-55966, -36762, -6400, -26773, -45833]]]
  g := ![![![-141379, -98825, -45175, -181976, 199988], ![-305108, -230762, -103845, -436502, 468524], ![1717222, 1207189, 551190, 2227440, -2443540], ![1541104, 1183487, 531027, 2249601, -2404332], ![-722654, -554129, -248707, -1052801, 1125683]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 4 2 4 [24, 3, 10, 18, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [18, 19, 20, 5], [10, 23, 17, 10], [12, 15, 21, 14], [0, 1]]
 g := ![![[21, 12, 26, 22], [26, 2, 1], [6, 24, 11, 1], []], ![[10, 17, 19, 8, 21, 28], [14, 27, 5], [13, 21, 2, 20, 11, 9], [5, 15, 4, 13, 4, 9]], ![[0, 0, 14, 1, 24, 21], [26, 2, 1], [1, 3, 11, 26, 14, 8], [24, 25, 8, 28, 5, 14]], ![[12, 16, 26, 10, 12, 11], [14, 27, 5], [0, 22, 1, 22, 15, 3], [6, 3, 27, 13, 18, 18]]]
 h' := ![![[18, 19, 20, 5], [15, 20, 13, 14], [1, 15, 10, 1], [0, 0, 0, 1], [0, 1]], ![[10, 23, 17, 10], [28, 28, 17, 20], [25, 19, 4, 11], [28, 26, 28, 24], [18, 19, 20, 5]], ![[12, 15, 21, 14], [23, 22, 24, 18], [26, 14, 19, 28], [18, 22, 18, 13], [10, 23, 17, 10]], ![[0, 1], [16, 17, 4, 6], [2, 10, 25, 18], [18, 10, 12, 20], [12, 15, 21, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [12, 16, 1], []]
 b := ![[], [], [9, 2, 22, 26], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 4
  hpos := by decide
  P := [24, 3, 10, 18, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![174766282, -503272645, -814104685, 606417708, 1616297028]
  a := ![-5, 3, 27, -28, -60]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1108661182, -797635553, -362478857, -1483917312, 1616297028]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 707281 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9569, 5733, 1077, 4506, 7876]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![9569, 5733, 1077, 4506, 7876]] 
 ![![29, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![17, 0, 0, 0, 1]] where
  M :=![![![9569, 5733, 1077, 4506, 7876], ![20258, 14016, 2325, 8932, 14692], ![38316, 28343, 4500, 19926, 33724], ![33558, 21299, 3817, 16125, 27900], ![12060, 10083, 1451, 6318, 10305]]]
  hmulB := by decide  
  f := ![![![100231, 66093, 110147, -122372, -199988]], ![![-18012, 4578, 6909, 290, -16156]], ![![-32022, -27549, -45630, 47580, 84260]], ![![117056, -22775, -33579, -11085, 82908]], ![![5077, 49440, 80376, -66984, -156051]]]
  g := ![![![-4287, 5733, 1077, 4506, 7876], ![-7914, 14016, 2325, 8932, 14692], ![-18448, 28343, 4500, 19926, 33724], ![-15198, 21299, 3817, 16125, 27900], ![-5625, 10083, 1451, 6318, 10305]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![-100231, -66093, -110147, 122372, 199988]] ![![9569, 5733, 1077, 4506, 7876]]
  ![![29, 0, 0, 0, 0]] where
 M := ![![![-29, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0)
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3589965, 131261, 316649, -1434212, -84154]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![3589965, 131261, 316649, -1434212, -84154]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![15, 26, 7, 20, 1]] where
  M :=![![![3589965, 131261, 316649, -1434212, -84154], ![-1602520, 5256672, 8484071, -6369454, -16789774], ![-39949002, -3538769, -6895926, 18700420, 7515422], ![17666892, -31643299, -50839547, 35524429, 101808852], ![-7839902, 14601755, 23468857, -16502460, -46950705]]]
  hmulB := by decide  
  f := ![![![10673281, 7346943, 1230557, 5119266, 8651266]], ![![22421798, 15435838, 2585145, 10754912, 18174862]], ![![47104636, 32426893, 5430952, 22595126, 38184634]], ![![38271298, 26344629, 4412447, 18356677, 31021740]], ![![59790625, 41159347, 6893550, 28678982, 48465607]]]
  g := ![![![156525, 74815, 29217, 8028, -84154], ![8072390, 14251316, 4064919, 10626646, -16789774], ![-4925172, -6417411, -1919480, -4245420, 7515422], ![-48692448, -86408821, -24629081, -64537181, 101808852], ![22465183, 39849035, 11358832, 29758440, -46950705]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 4 2 4 [30, 13, 25, 20, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [18, 25, 2, 9], [2, 11, 4, 16], [22, 25, 25, 6], [0, 1]]
 g := ![![[18, 9, 26, 19], [23, 1, 18, 8], [24, 3, 11, 1], []], ![[17, 22, 14, 24, 4, 7], [29, 11, 23, 24, 23, 1], [18, 25, 28, 14, 27, 18], [22, 18, 26, 14, 11, 16]], ![[6, 12, 19, 1, 4, 14], [12, 24, 14, 2, 1, 2], [5, 8, 2, 16, 2, 8], [20, 0, 14, 23, 16, 4]], ![[5, 0, 1, 29, 16, 22], [30, 24, 7, 27, 24, 12], [18, 24, 16, 21, 11, 22], [26, 26, 0, 30, 23, 30]]]
 h' := ![![[18, 25, 2, 9], [23, 30, 5, 22], [24, 1, 23, 16], [0, 0, 0, 1], [0, 1]], ![[2, 11, 4, 16], [5, 2, 23, 7], [3, 24, 10, 21], [26, 7, 30, 8], [18, 25, 2, 9]], ![[22, 25, 25, 6], [16, 17, 21, 20], [23, 28, 28, 2], [28, 27, 9, 4], [2, 11, 4, 16]], ![[0, 1], [2, 13, 13, 13], [17, 9, 1, 23], [10, 28, 23, 18], [22, 25, 25, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [16, 16, 12], []]
 b := ![[], [], [24, 1, 21, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 4
  hpos := by decide
  P := [30, 13, 25, 20, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-127531790526, -74778093436, -126363049151, 145538691463, 228568906191]
  a := ![6, -68, -31, -33, 69]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-114711786561, -194115150142, -55688561048, -142769013947, 228568906191]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 923521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10673281, -7346943, -1230557, -5119266, -8651266]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![-10673281, -7346943, -1230557, -5119266, -8651266]] 
 ![![31, 0, 0, 0, 0], ![13, 1, 0, 0, 0], ![17, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![25, 0, 0, 0, 1]] where
  M :=![![![-10673281, -7346943, -1230557, -5119266, -8651266], ![-22421798, -15435838, -2585145, -10754912, -18174862], ![-47104636, -32426893, -5430952, -22595126, -38184634], ![-38271298, -26344629, -4412447, -18356677, -31021740], ![-15285000, -10522993, -1762321, -7332318, -12391177]]]
  hmulB := by decide  
  f := ![![![-3589965, -131261, -316649, 1434212, 84154]], ![![-1453775, -224615, -406468, 806910, 576896]], ![![-680013, 42172, 48803, 183264, -196284]], ![![-1380537, 991112, 1568484, -822095, -3265154]], ![![-2642233, -576880, -1012422, 1688960, 1582405]]]
  g := ![![![11544289, -7346943, -1230557, -5119266, -8651266], ![24253145, -15435838, -2585145, -10754912, -18174862], ![50953319, -32426893, -5430952, -22595126, -38184634], ![41395507, -26344629, -4412447, -18356677, -31021740], ![16534807, -10522993, -1762321, -7332318, -12391177]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![3589965, 131261, 316649, -1434212, -84154]] ![![-10673281, -7346943, -1230557, -5119266, -8651266]]
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

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0, 0, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0, 0, 0]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![0, 0, 0, 0, 37]] where
  M :=![![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![0, 0, 0, 0, 37]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 5 2 5 [14, 24, 4, 18, 10, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 24, 28, 6, 31], [12, 32, 36, 36, 28], [1, 33, 26, 16, 29], [30, 21, 21, 16, 23], [0, 1]]
 g := ![![[17, 14, 27, 25, 28], [16, 27, 29, 3], [22, 22, 8, 27, 1], [], []], ![[21, 35, 17, 4, 0, 26, 0, 23], [30, 1, 26, 28], [7, 28, 20, 12, 10, 18, 8, 6], [1, 31, 29, 9], [8, 5, 12, 36]], ![[14, 8, 15, 2, 22, 12, 31, 4], [5, 22, 16, 25], [14, 3, 1, 5, 18, 5, 17, 26], [19, 24, 22, 34], [15, 6, 22, 7]], ![[14, 31, 4, 27, 25, 0, 18, 23], [1, 15, 32, 21], [34, 11, 2, 13, 10, 29, 22, 14], [23, 29, 16, 30], [6, 26, 29, 27]], ![[29, 22, 10, 26, 24, 12, 21, 29], [11, 1, 24, 34], [5, 22, 16, 14, 23, 20, 4, 24], [26, 8, 28, 4], [25, 18, 34, 11]]]
 h' := ![![[21, 24, 28, 6, 31], [31, 25, 3, 28, 18], [25, 15, 12, 19, 22], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[12, 32, 36, 36, 28], [35, 18, 29, 30, 29], [23, 26, 1, 27, 18], [2, 12, 6, 0, 6], [33, 6, 26, 11, 34], [21, 24, 28, 6, 31]], ![[1, 33, 26, 16, 29], [1, 11, 9, 12, 33], [16, 1, 29, 34, 5], [20, 26, 10, 27, 20], [8, 28, 7, 28, 21], [12, 32, 36, 36, 28]], ![[30, 21, 21, 16, 23], [2, 26, 8, 36, 23], [33, 23, 33, 15, 13], [18, 5, 16, 22, 27], [28, 2, 13, 18, 17], [1, 33, 26, 16, 29]], ![[0, 1], [4, 31, 25, 5, 8], [11, 9, 36, 16, 16], [31, 31, 5, 25, 20], [32, 1, 27, 17, 2], [30, 21, 21, 16, 23]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 12, 20, 6], [], [], []]
 b := ![[], [9, 36, 23, 2, 1], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 5
  hpos := by decide
  P := [14, 24, 4, 18, 10, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![240515725, -311101106, -495153758, 321151453, 999387205]
  a := ![-1, -2, 6, -9, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![6500425, -8408138, -13382534, 8679769, 27010465]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-216147371, -148793542, -24920684, -103677922, -175209724]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![-216147371, -148793542, -24920684, -103677922, -175209724]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![36, 19, 0, 1, 0], ![9, 36, 25, 0, 1]] where
  M :=![![![-216147371, -148793542, -24920684, -103677922, -175209724], ![-454097370, -312599857, -52355182, -217811530, -368086444], ![-953984418, -656727466, -109990009, -457595126, -773306140], ![-775055018, -533542792, -89359974, -371765919, -628262184], ![-309572642, -213114034, -35692376, -148491662, -250940229]]]
  hmulB := by decide  
  f := ![![![-1986811, 306482, 439988, 293758, -1153684]], ![![-2013610, -2994265, -4917118, 4656134, 9293516]], ![![23243166, -2293346, -3050521, -5140598, 9406028]], ![![-2486372, -658315, -1140072, 1741603, 1854604]], ![![11876153, -4171758, -6426909, 1329698, 14303483]]]
  g := ![![![124223057, 198259440, 106227376, -103677922, -175209724], ![260973066, 416510517, 223165998, -217811530, -368086444], ![548273058, 875039048, 468845451, -457595126, -773306140], ![445436042, 710913373, 380907186, -371765919, -628262184], ![177916811, 283953068, 152141789, -148491662, -250940229]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [8, 33, 23, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 0, 30], [9, 40, 11], [0, 1]]
 g := ![![[4, 0, 23], [24, 25], [23, 9], [4, 18, 1], []], ![[12, 25, 13, 12], [13, 21], [10, 1], [7, 27, 9, 30], [5, 39]], ![[1, 21, 35, 14], [2, 8], [9, 4], [21, 15], [24, 39]]]
 h' := ![![[9, 0, 30], [3, 10, 8], [20, 23, 5], [9, 11, 3], [0, 0, 1], [0, 1]], ![[9, 40, 11], [11, 38, 5], [22, 34, 29], [26, 4, 40], [0, 15, 40], [9, 0, 30]], ![[0, 1], [25, 34, 28], [0, 25, 7], [21, 26, 39], [12, 26], [9, 40, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 15], []]
 b := ![[], [34, 34, 20], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [8, 33, 23, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-21369690, -4110594, -8549330, 15051358, 14615819]
  a := ![8, 11, -43, 58, 95]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-16945389, -19908680, -9120605, 15051358, 14615819]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 68921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1986811, -306482, -439988, -293758, 1153684]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![1986811, -306482, -439988, -293758, 1153684]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![14, 0, 1, 0, 0], ![0, 28, 0, 1, 0], ![12, 19, 0, 0, 1]] where
  M :=![![![1986811, -306482, -439988, -293758, 1153684], ![2013610, 2994265, 4917118, -4656134, -9293516], ![-23243166, 2293346, 3050521, 5140598, -9406028], ![-7842534, -18866768, -30842722, 27636111, 59005416], ![3785618, 8673226, 14183888, -12767922, -27108683]]]
  hmulB := by decide  
  f := ![![![216147371, 148793542, 24920684, 103677922, 175209724]], ![![454097370, 312599857, 52355182, 217811530, 368086444]], ![![97074332, 66825294, 11192185, 46563074, 78688836]], ![![329019058, 226496068, 37934270, 157816799, 266699576]], ![![281248564, 193610581, 32426562, 134903556, 227978033]]]
  g := ![![![-138965, -341494, -439988, -293758, 1153684], ![1090150, 7559581, 4917118, -4656134, -9293516], ![1144436, 904174, 3050521, 5140598, -9406028], ![-6929498, -46677580, -30842722, 27636111, 59005416], ![3183302, 21493659, 14183888, -12767922, -27108683]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P1 : CertificateIrreducibleZModOfList' 41 2 2 5 [6, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 40], [0, 1]]
 g := ![![[30, 36], [2], [9], [32, 10], [1]], ![[28, 5], [2], [9], [36, 31], [1]]]
 h' := ![![[25, 40], [11, 35], [33, 24], [13, 38], [35, 25], [0, 1]], ![[0, 1], [25, 6], [18, 17], [20, 3], [4, 16], [25, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [7, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N1 : CertifiedPrimeIdeal' SI41N1 41 where
  n := 2
  hpos := by decide
  P := [6, 16, 1]
  hirr := P41P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![27180, -19075, -29835, 16481, 63579]
  a := ![-10, 11, 55, -47, -119]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7758, -41184, -29835, 16481, 63579]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N1 B_one_repr
lemma NI41N1 : Nat.card (O ⧸ I41N1) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![-216147371, -148793542, -24920684, -103677922, -175209724]] ![![1986811, -306482, -439988, -293758, 1153684]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![439, -30, 34, -82, -162]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![439, -30, 34, -82, -162]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![31, 40, 12, 9, 1]] where
  M :=![![![439, -30, 34, -82, -162], ![-406, 393, -24, -18, -174], ![-366, -586, -21, 210, 654], ![962, -168, 70, -141, -288], ![-714, -114, -60, 170, 425]]]
  hmulB := by decide  
  f := ![![![-363, -250, -42, -174, -294]], ![![-762, -525, -88, -366, -618]], ![![-1602, -1102, -183, -770, -1302]], ![![-1306, -896, -150, -623, -1056]], ![![-1703, -1172, -196, -817, -1381]]]
  g := ![![![127, 150, 46, 32, -162], ![116, 171, 48, 36, -174], ![-480, -622, -183, -132, 654], ![230, 264, 82, 57, -288], ![-323, -398, -120, -85, 425]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 4 2 5 [30, 32, 8, 22, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 6, 28, 5], [2, 2, 12, 28], [22, 34, 3, 10], [0, 1]]
 g := ![![[13, 36, 42, 24], [1, 10, 16, 38], [37, 21, 9], [21, 1], []], ![[40, 15, 17, 30, 32, 3], [39, 42, 31, 22, 33, 20], [12, 37, 38], [41, 9, 42, 3, 1, 19], [5, 31, 25]], ![[28, 8, 26, 17, 31, 32], [42, 3, 8, 36, 20, 37], [6, 33, 40], [32, 11, 21, 18, 8, 5], [36, 22, 10]], ![[21, 32, 38, 42, 40, 16], [39, 6, 4, 10, 14, 38], [20, 37, 1], [3, 25, 23, 16, 36, 40], [13, 10, 14]]]
 h' := ![![[40, 6, 28, 5], [13, 35, 38, 29], [18, 2, 10, 34], [15, 29, 15, 3], [0, 0, 1], [0, 1]], ![[2, 2, 12, 28], [12, 19, 17, 11], [37, 20, 40, 41], [15, 39, 27, 9], [31, 35, 21, 8], [40, 6, 28, 5]], ![[22, 34, 3, 10], [42, 9, 9, 9], [7, 25, 12, 3], [31, 16, 36, 30], [42, 2, 7, 33], [2, 2, 12, 28]], ![[0, 1], [20, 23, 22, 37], [12, 39, 24, 8], [28, 2, 8, 1], [8, 6, 14, 2], [22, 34, 3, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [37, 3, 40], []]
 b := ![[], [], [26, 38, 18, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 4
  hpos := by decide
  P := [30, 32, 8, 22, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7727724194, 3698675808, 5780851808, -2163757824, -12426796416]
  a := ![6, -16, -32, 10, 72]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![8779138714, 11645826336, 3602381600, 2550637440, -12426796416]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 3418801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![363, 250, 42, 174, 294]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![363, 250, 42, 174, 294]] 
 ![![43, 0, 0, 0, 0], ![26, 1, 0, 0, 0], ![12, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![22, 0, 0, 0, 1]] where
  M :=![![![363, 250, 42, 174, 294], ![762, 525, 88, 366, 618], ![1602, 1102, 183, 770, 1302], ![1306, 896, 150, 623, 1056], ![518, 358, 60, 250, 421]]]
  hmulB := by decide  
  f := ![![![-439, 30, -34, 82, 162]], ![![-256, 9, -20, 50, 102]], ![![-114, 22, -9, 18, 30]], ![![-53, 6, -4, 9, 18]], ![![-208, 18, -16, 38, 73]]]
  g := ![![![-317, 250, 42, 174, 294], ![-666, 525, 88, 366, 618], ![-1400, 1102, 183, 770, 1302], ![-1137, 896, 150, 623, 1056], ![-454, 358, 60, 250, 421]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![439, -30, 34, -82, -162]] ![![363, 250, 42, 174, 294]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![95, 10, 8, -22, -50]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![95, 10, 8, -22, -50]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![17, 3, 14, 1, 0], ![16, 6, 20, 0, 1]] where
  M :=![![![95, 10, 8, -22, -50], ![-122, 75, -8, 6, -14], ![-22, -150, -3, 42, 142], ![224, 0, 16, -43, -96], ![-142, -54, -12, 42, 111]]]
  hmulB := by decide  
  f := ![![![9, 6, 0, 6, 10]], ![![26, 13, 0, 10, 22]], ![![54, 38, 19, 6, 10]], ![![21, 15, 6, 5, 8]], ![![30, 20, 8, 6, 11]]]
  g := ![![![27, 8, 28, -22, -50], ![0, 3, 4, 6, -14], ![-64, -24, -73, 42, 142], ![53, 15, 54, -43, -96], ![-56, -18, -60, 42, 111]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [42, 31, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 25, 8], [13, 21, 39], [0, 1]]
 g := ![![[34, 4, 42], [1, 42, 7], [44, 13, 4], [41, 42, 1], []], ![[8, 9, 42, 36], [30, 0, 27, 2], [2, 11, 36, 17], [26, 45, 24, 3], [33, 17]], ![[45, 12, 36, 20], [25, 1, 26, 41], [40, 0, 18, 20], [1, 33, 29, 29], [2, 17]]]
 h' := ![![[29, 25, 8], [5, 28, 29], [32, 24, 30], [17, 20, 2], [0, 0, 1], [0, 1]], ![[13, 21, 39], [5, 38, 34], [29, 27, 23], [24, 20, 14], [19, 42, 21], [29, 25, 8]], ![[0, 1], [14, 28, 31], [27, 43, 41], [24, 7, 31], [38, 5, 25], [13, 21, 39]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 13], []]
 b := ![[], [13, 32, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [42, 31, 5, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9873322, 3037767, 4021086, 484318, -8812387]
  a := ![6, 7, -26, 44, 59]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2614712, 1158705, 3691242, 484318, -8812387]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 103823 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-58542945, -40300902, -6749718, -28080896, -47454902]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-58542945, -40300902, -6749718, -28080896, -47454902]] 
 ![![47, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![45, 0, 1, 0, 0], ![27, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![-58542945, -40300902, -6749718, -28080896, -47454902], ![-122990700, -84666669, -14180232, -58994112, -99696242], ![-258386596, -177873062, -29790723, -123938540, -209448134], ![-209922054, -144510122, -24202996, -100691883, -170162784], ![-83847876, -57720790, -9667254, -40218740, -67967075]]]
  hmulB := by decide  
  f := ![![![2809, -1038, 178, -336, -146]], ![![405, -87, 38, -72, -92]], ![![2527, -1044, 159, -268, -52]], ![![1735, -700, 42, -147, 54]], ![![128, -50, 38, -36, -43]]]
  g := ![![![31389457, -40300902, -6749718, -28080896, -47454902], ![65944945, -84666669, -14180232, -58994112, -99696242], ![138541287, -177873062, -29790723, -123938540, -209448134], ![112555651, -144510122, -24202996, -100691883, -170162784], ![44957412, -57720790, -9667254, -40218740, -67967075]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![75, -32, -30, 6, 72]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![75, -32, -30, 6, 72]] 
 ![![47, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![44, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![10, 0, 0, 0, 1]] where
  M :=![![![75, -32, -30, 6, 72], ![150, 111, 148, -174, -288], ![-750, 184, 291, 2, -648], ![-722, -610, -960, 1031, 1776], ![314, 280, 438, -470, -803]]]
  hmulB := by decide  
  f := ![![![-47900555, -32974692, -5522702, -22976134, -38828184]], ![![-14371046, -9893013, -1656912, -6893262, -11649168]], ![![-49341266, -33966476, -5688809, -23667190, -39996024]], ![![-15884414, -10934814, -1831396, -7619169, -12875904]], ![![-11651296, -8020740, -1343338, -5588698, -9444539]]]
  g := ![![![21, -32, -30, 6, 72], ![-58, 111, 148, -174, -288], ![-198, 184, 291, 2, -648], ![398, -610, -960, 1031, 1776], ![-184, 280, 438, -470, -803]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![95, 10, 8, -22, -50]] ![![-58542945, -40300902, -6749718, -28080896, -47454902]]
  ![![-47900555, -32974692, -5522702, -22976134, -38828184]] where
 M := ![![![-47900555, -32974692, -5522702, -22976134, -38828184]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![-47900555, -32974692, -5522702, -22976134, -38828184]] ![![75, -32, -30, 6, 72]]
  ![![47, 0, 0, 0, 0]] where
 M := ![![![47, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1, I47N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
    exact isPrimeI47N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0 ⊙ MulI47N1)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3218149, -2219514, -371176, -1544754, -2609614]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-3218149, -2219514, -371176, -1544754, -2609614]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![49, 12, 11, 1, 0], ![40, 0, 42, 0, 1]] where
  M :=![![![-3218149, -2219514, -371176, -1544754, -2609614], ![-6763982, -4654185, -779832, -3246894, -5488978], ![-14224850, -9785898, -1639755, -6816178, -11517838], ![-11543936, -7956040, -1331256, -5538915, -9357984], ![-4619178, -3172010, -532284, -2212146, -3739461]]]
  hmulB := by decide  
  f := ![![![-84105, 158118, 254160, -178978, -508342]], ![![-1195662, -159309, -293040, 630114, 393974]], ![![1418062, -1724842, -2758071, 1776542, 5591498]], ![![79381, -223020, -359617, 266229, 713376]], ![![998562, -1258726, -2013786, 1309202, 4077119]]]
  g := ![![![3336969, 307878, 2381602, -1544754, -2609614], ![7016848, 647331, 5008926, -3246894, -5488978], ![14726064, 1358646, 10511083, -6816178, -11517838], ![11965703, 1103980, 8540229, -5538915, -9357984], ![4780272, 441014, 3412428, -2212146, -3739461]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [28, 7, 34, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 31, 37], [19, 21, 16], [0, 1]]
 g := ![![[0, 1, 38], [5, 17], [20, 42, 44], [21, 43], [1]], ![[5, 21, 52, 49], [30, 24], [30, 45, 51, 29], [9, 43], [5, 22, 44, 38]], ![[5, 12, 12, 49], [43, 13], [6, 25, 28, 42], [], [51, 34, 36, 15]]]
 h' := ![![[0, 31, 37], [18, 19, 41], [23, 0, 21], [37, 48, 37], [25, 46, 19], [0, 1]], ![[19, 21, 16], [19, 43, 27], [8, 28, 17], [3, 18, 9], [19, 38, 34], [0, 31, 37]], ![[0, 1], [30, 44, 38], [11, 25, 15], [42, 40, 7], [25, 22], [19, 21, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36, 30], []]
 b := ![[], [6, 19, 35], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [28, 7, 34, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![395960, 299704, 497728, -533150, -913146]
  a := ![2, -7, -11, 4, 25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1189550, 126368, 843670, -533150, -913146]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 148877 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-84105, 158118, 254160, -178978, -508342]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-84105, 158118, 254160, -178978, -508342]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![47, 31, 1, 0, 0], ![40, 47, 0, 1, 0], ![26, 50, 0, 0, 1]] where
  M :=![![![-84105, 158118, 254160, -178978, -508342], ![-1195662, -159309, -293040, 630114, 393974], ![1418062, -1724842, -2758071, 1776542, 5591498], ![7077600, 1317128, 2341720, -4223271, -3516480], ![-3270618, -593834, -1058076, 1932062, 1578071]]]
  hmulB := by decide  
  f := ![![![-3218149, -2219514, -371176, -1544754, -2609614]], ![![-6763982, -4654185, -779832, -3246894, -5488978]], ![![-7078515, -4875147, -816223, -3397610, -5742038]], ![![-8644850, -5952515, -996800, -4149681, -7013670]], ![![-8046984, -5539408, -927820, -3862650, -6529025]]]
  g := ![![![157479, 492608, 254160, -178978, -508342], ![-431522, -762059, -293040, 630114, 393974], ![-1611193, -5269755, -2758071, 1776542, 5591498], ![2969360, 5717765, 2341720, -4223271, -3516480], ![-1355724, -2594414, -1058076, 1932062, 1578071]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P1 : CertificateIrreducibleZModOfList' 53 2 2 5 [44, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [50, 52], [0, 1]]
 g := ![![[35, 47], [4], [50, 24], [6], [50, 1]], ![[0, 6], [4], [31, 29], [6], [47, 52]]]
 h' := ![![[50, 52], [23, 43], [26, 51], [41, 17], [26, 18], [0, 1]], ![[0, 1], [0, 10], [32, 2], [43, 36], [25, 35], [50, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [7, 40]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N1 : CertifiedPrimeIdeal' SI53N1 53 where
  n := 2
  hpos := by decide
  P := [44, 3, 1]
  hirr := P53P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![28376, -14728, -23984, 11864, 52548]
  a := ![10, -11, -50, 45, 117]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-12928, -46344, -23984, 11864, 52548]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N1 B_one_repr
lemma NI53N1 : Nat.card (O ⧸ I53N1) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-3218149, -2219514, -371176, -1544754, -2609614]] ![![-84105, 158118, 254160, -178978, -508342]]
  ![![53, 0, 0, 0, 0]] where
 M := ![![![53, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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


def P59P0 : CertificateIrreducibleZModOfList' 59 5 2 5 [28, 44, 5, 1, 41, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [57, 22, 54, 48, 19], [58, 34, 56, 12, 39], [40, 3, 34, 25, 40], [40, 58, 33, 33, 20], [0, 1]]
 g := ![![[38, 22, 34, 31, 51], [57, 57, 27], [30, 44, 17, 22], [28, 18, 1], []], ![[13, 29, 57, 45, 47, 47, 16, 49], [37, 8, 45, 2, 56, 1, 23, 12], [45, 48, 9, 29], [12, 37, 33, 1, 7, 39, 21, 4], [43, 34, 45, 55, 20, 45, 39, 15]], ![[30, 42, 33, 42, 48, 17, 41, 43], [33, 47, 50, 20, 18, 13, 16, 31], [10, 48, 8, 21], [28, 30, 26, 10, 37, 25, 36, 47], [29, 33, 46, 7, 21, 9, 23, 24]], ![[0, 8, 4, 17, 55, 3, 51, 42], [28, 29, 48, 21, 10, 5, 18, 18], [49, 43, 50, 41], [40, 54, 10, 54, 25, 41, 46, 23], [13, 53, 30, 37, 34, 20, 19, 44]], ![[40, 15, 39, 48, 48, 40, 31, 51], [19, 58, 5, 34, 56, 46, 39, 1], [7, 52, 38, 48], [31, 2, 3, 58, 55, 24, 1, 45], [7, 45, 10, 7, 49, 36, 51, 35]]]
 h' := ![![[57, 22, 54, 48, 19], [56, 13, 44, 50, 46], [39, 9, 23, 33], [42, 34, 43, 15, 9], [0, 0, 0, 1], [0, 1]], ![[58, 34, 56, 12, 39], [54, 8, 32, 19, 30], [24, 2, 46, 19, 10], [35, 2, 30, 30, 18], [27, 16, 24, 20, 42], [57, 22, 54, 48, 19]], ![[40, 3, 34, 25, 40], [8, 13, 54, 7, 15], [37, 7, 18, 52, 5], [50, 48, 1, 15, 27], [13, 26, 10, 14, 53], [58, 34, 56, 12, 39]], ![[40, 58, 33, 33, 20], [1, 47, 49, 30, 2], [33, 43, 15, 30, 33], [44, 38, 32, 58, 49], [34, 13, 32, 37, 51], [40, 3, 34, 25, 40]], ![[0, 1], [38, 37, 57, 12, 25], [41, 57, 16, 43, 11], [1, 55, 12, 0, 15], [25, 4, 52, 46, 31], [40, 58, 33, 33, 20]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36, 4, 10, 35], [], [], []]
 b := ![[], [2, 43, 27, 18, 23], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 5
  hpos := by decide
  P := [28, 44, 5, 1, 41, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![939800143056, -277654155996, -423651602760, 36389731844, 966376941092]
  a := ![6, -5, -33, 30, 71]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![15928815984, -4706002644, -7180535640, 616775116, 16379270188]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![405909, 29445, 59501, -181422, -55748]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![405909, 29445, 59501, -181422, -55748]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![7, 22, 1, 0, 0], ![45, 6, 0, 1, 0], ![22, 52, 0, 0, 1]] where
  M :=![![![405909, 29445, 59501, -181422, -55748], ![-292918, 591084, 950733, -676612, -1898324], ![-4473260, -563897, -1044216, 2315054, 1372276], ![2676262, -3525669, -5644063, 3709449, 11408796], ![-1199388, 1628179, 2607523, -1725882, -5265291]]]
  hmulB := by decide  
  f := ![![![261627, 194069, 30571, 125468, 207092]], ![![539652, 373822, 62537, 274298, 470156]], ![![244563, 170174, 28333, 122444, 208752]], ![![261643, 191114, 30510, 126935, 211320]], ![![560908, 392645, 65071, 282092, 480693]]]
  g := ![![![153768, 44391, 59501, -181422, -55748], ![1069879, 1351598, 950733, -676612, -1898324], ![-2156250, -1030161, -1044216, 2315054, 1372276], ![-6159574, -8112629, -5644063, 3709449, 11408796], ![2853263, 3744477, 2607523, -1725882, -5265291]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [58, 42, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 60], [0, 1]]
 g := ![![[47, 20], [45], [37, 49], [31, 4], [19, 1]], ![[0, 41], [45], [53, 12], [46, 57], [38, 60]]]
 h' := ![![[19, 60], [12, 9], [50, 44], [32, 7], [57, 59], [0, 1]], ![[0, 1], [0, 52], [32, 17], [43, 54], [19, 2], [19, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43]]
 b := ![[], [55, 52]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [58, 42, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4381, -703, -2880, 4775, 5568]
  a := ![3, 2, -15, 21, 32]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5272, -4189, -2880, 4775, 5568]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![27, 18, 2, 14, 24]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![27, 18, 2, 14, 24]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![34, 9, 1, 0, 0], ![30, 38, 0, 1, 0], ![24, 49, 0, 0, 1]] where
  M :=![![![27, 18, 2, 14, 24], ![62, 39, 6, 26, 48], ![122, 90, 27, 46, 72], ![64, 68, 12, 57, 72], ![54, 26, 4, 14, 35]]]
  hmulB := by decide  
  f := ![![![135, -38, 10, -18, -24]], ![![-66, 139, -2, -22, -96]], ![![62, -3, 5, -12, -24]], ![![30, 66, 4, -23, -72]], ![![-4, 97, 2, -24, -85]]]
  g := ![![![-17, -28, 2, 14, 24], ![-34, -55, 6, 26, 48], ![-64, -89, 27, 46, 72], ![-62, -94, 12, 57, 72], ![-22, -37, 4, 14, 35]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P1 : CertificateIrreducibleZModOfList' 61 2 2 5 [47, 42, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 60], [0, 1]]
 g := ![![[58, 13], [39], [49, 13], [44, 20], [19, 1]], ![[0, 48], [39], [52, 48], [58, 41], [38, 60]]]
 h' := ![![[19, 60], [39, 14], [15, 51], [6, 14], [22, 9], [0, 1]], ![[0, 1], [0, 47], [8, 10], [28, 47], [10, 52], [19, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37]]
 b := ![[], [53, 49]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N1 : CertifiedPrimeIdeal' SI61N1 61 where
  n := 2
  hpos := by decide
  P := [47, 42, 1]
  hirr := P61P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![95173, -29033, -46053, 10219, 104621]
  a := ![-16, 25, 79, -71, -199]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-18959, -84087, -46053, 10219, 104621]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N1 B_one_repr
lemma NI61N1 : Nat.card (O ⧸ I61N1) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-38527, -26522, -4442, -18480, -31230]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![-38527, -26522, -4442, -18480, -31230]] 
 ![![61, 0, 0, 0, 0], ![30, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![34, 0, 0, 0, 1]] where
  M :=![![![-38527, -26522, -4442, -18480, -31230], ![-80940, -55719, -9332, -38824, -65610], ![-170044, -117058, -19605, -81564, -137838], ![-138150, -95102, -15928, -66265, -111984], ![-55180, -37986, -6362, -26468, -44729]]]
  hmulB := by decide  
  f := ![![![773, -70, 42, -128, -246]], ![![370, -23, 20, -64, -126]], ![![179, -32, 13, -28, -48]], ![![70, -10, 4, -9, -24]], ![![414, -42, 22, -68, -125]]]
  g := ![![![32123, -26522, -4442, -18480, -31230], ![67486, -55719, -9332, -38824, -65610], ![141779, -117058, -19605, -81564, -137838], ![115186, -95102, -15928, -66265, -111984], ![46008, -37986, -6362, -26468, -44729]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![405909, 29445, 59501, -181422, -55748]] ![![27, 18, 2, 14, 24]]
  ![![5422855, 23663, 194959, -1936184, 425684]] where
 M := ![![![5422855, 23663, 194959, -1936184, 425684]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![5422855, 23663, 194959, -1936184, 425684]] ![![-38527, -26522, -4442, -18480, -31230]]
  ![![61, 0, 0, 0, 0]] where
 M := ![![![1350479, -11285, 20923, -459940, 159698]]]
 hmul := by decide  
 g := ![![![![22139, -185, 343, -7540, 2618]]]]
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


lemma PB405I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB405I1 : PrimesBelowBoundCertificateInterval O 23 61 405 where
  m := 9
  g := ![2, 2, 1, 2, 2, 3, 2, 1, 3]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB405I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1]
    · exact ![I31N0, I31N1]
    · exact ![I37N0]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1, I47N2]
    · exact ![I53N0, I53N1]
    · exact ![I59N0]
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
    · exact ![707281, 29]
    · exact ![923521, 31]
    · exact ![69343957]
    · exact ![68921, 1681]
    · exact ![3418801, 43]
    · exact ![103823, 47, 47]
    · exact ![148877, 2809]
    · exact ![714924299]
    · exact ![3721, 3721, 61]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
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
      exact NI61N1
      exact NI61N2
  β := ![I29N1, I31N1, I43N1, I47N1, I47N2, I61N2]
  Il := ![[I29N1], [I31N1], [], [], [I43N1], [I47N1, I47N2], [], [], [I61N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
