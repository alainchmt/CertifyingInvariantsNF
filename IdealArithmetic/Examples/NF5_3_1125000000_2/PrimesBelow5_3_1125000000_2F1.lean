
import IdealArithmetic.Examples.NF5_3_1125000000_2.RI5_3_1125000000_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![84, -60, 2, 5, -1]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![84, -60, 2, 5, -1]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![19, 7, 7, 1, 0], ![11, 8, 4, 0, 1]] where
  M :=![![![84, -60, 2, 5, -1], ![-10, 103, -130, 2, 22], ![110, -145, 101, 4, -18], ![-85, 121, -84, -4, 15], ![140, -255, 220, 4, -39]]]
  hmulB := by decide  
  f := ![![![-4, 2, 4, -1, -1]], ![![-10, 5, 6, -6, -2]], ![![-10, -1, 11, -12, -10]], ![![-9, 3, 7, -7, -4]], ![![-6, 1, 6, -5, -4]]]
  g := ![![![0, -3, -1, 5, -1], ![-10, -3, -8, 2, 22], ![8, -1, 5, 4, -18], ![-6, 1, -4, -4, 15], ![17, 1, 12, 4, -39]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [6, 22, 19, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [21, 14, 24], [18, 14, 5], [0, 1]]
 g := ![![[11, 20, 16], [15, 22], [23, 9, 13], [1]], ![[15, 9, 23, 25], [28, 28], [14, 4, 6, 4], [0, 23, 3, 20]], ![[8, 23, 15, 24], [25, 9], [26, 23, 14, 5], [20, 6, 9, 9]]]
 h' := ![![[21, 14, 24], [17, 3, 25], [7, 27, 15], [23, 7, 10], [0, 1]], ![[18, 14, 5], [28, 24, 16], [15, 25, 17], [10, 27, 18], [21, 14, 24]], ![[0, 1], [15, 2, 17], [7, 6, 26], [28, 24, 1], [18, 14, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26], []]
 b := ![[], [23, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 3
  hpos := by decide
  P := [6, 22, 19, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16205344, -8723445, 20859438, -32594826, -27088816]
  a := ![0, -7, 2, -8, -11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![31071494, 15039685, 12323396, -32594826, -27088816]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 24389 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-21, 182, -256, 208, -110]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![-21, 182, -256, 208, -110]] 
 ![![29, 0, 0, 0, 0], ![18, 1, 0, 0, 0], ![12, 0, 1, 0, 0], ![28, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![-21, 182, -256, 208, -110], ![-1100, 909, -52, -1416, 1052], ![5260, -5674, 2325, 4844, -3884], ![-18870, 21776, -10492, -15427, 13046], ![45230, -52064, 25036, 37022, -30941]]]
  hmulB := by decide  
  f := ![![![-852229, 582278, 918368, -130868, -147634]], ![![-579878, 390305, 619204, -88008, -99504]], ![![-391992, 260842, 415685, -58964, -66780]], ![![-825838, 561020, 886820, -126247, -142542]], ![![-51492, 35584, 55876, -7978, -8985]]]
  g := ![![![-201, 182, -256, 208, -110], ![714, 909, -52, -1416, 1052], ![-1668, -5674, 2325, 4844, -3884], ![4170, 21776, -10492, -15427, 13046], ![-10096, -52064, 25036, 37022, -30941]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1

def I29N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-30861, 6298, 19008, -2134, -2962]] i)))

def SI29N2: IdealEqSpanCertificate' Table ![![-30861, 6298, 19008, -2134, -2962]] 
 ![![29, 0, 0, 0, 0], ![26, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![-30861, 6298, 19008, -2134, -2962], ![-29620, 4613, 16864, -1796, -2612], ![-13060, 968, 6409, -604, -980], ![9910, -2806, -6860, 823, 1078], ![6020, -1132, -3612, 400, 561]]]
  hmulB := by decide  
  f := ![![![531, -2986, 3360, -1994, -1398]], ![![-6, -2343, 2944, -2272, -1432]], ![![-710, -1164, 1977, -2312, -1272]], ![![-3672, 730, 1756, -5441, -2466]], ![![-4147, -474, 3612, -7398, -3577]]]
  g := ![![![-12403, 6298, 19008, -2134, -2962], ![-10218, 4613, 16864, -1796, -2612], ![-3250, 968, 6409, -604, -980], ![4906, -2806, -6860, 823, 1078], ![2305, -1132, -3612, 400, 561]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N2 : Nat.card (O ⧸ I29N2) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N2)

lemma isPrimeI29N2 : Ideal.IsPrime I29N2 := prime_ideal_of_norm_prime hp29.out _ NI29N2
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![84, -60, 2, 5, -1]] ![![-21, 182, -256, 208, -110]]
  ![![-64824, 110344, -91230, -2037, 16043]] where
 M := ![![![-64824, 110344, -91230, -2037, 16043]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI29N1 : IdealMulLeCertificate' Table 
  ![![-64824, 110344, -91230, -2037, 16043]] ![![-30861, 6298, 19008, -2134, -2962]]
  ![![29, 0, 0, 0, 0]] where
 M := ![![![174, -174, 58, 261, -203]]]
 hmul := by decide  
 g := ![![![![6, -6, 2, 9, -7]]]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2104, 994, 1840, -245, -293]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![-2104, 994, 1840, -245, -293]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![30, 5, 1, 0, 0], ![5, 6, 0, 1, 0], ![0, 25, 0, 0, 1]] where
  M :=![![![-2104, 994, 1840, -245, -293], ![-2930, 1297, 2478, -326, -394], ![-1970, 827, 1623, -212, -258], ![175, -131, -200, 26, 31], ![470, -217, -406, 50, 63]]]
  hmulB := by decide  
  f := ![![![96, -124, 74, 59, -55]], ![![-550, 673, -366, -394, 346]], ![![60, -78, 47, 36, -34]], ![![-265, 315, -162, -203, 174]], ![![-30, 56, -50, 6, 3]]]
  g := ![![![-1809, 19, 1840, -245, -293], ![-2440, 23, 2478, -326, -394], ![-1600, 14, 1623, -212, -258], ![195, -2, -200, 26, 31], ![400, -2, -406, 50, 63]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [16, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 30], [0, 1]]
 g := ![![[21, 2], [18, 19], [19, 19], [5, 1]], ![[0, 29], [20, 12], [21, 12], [10, 30]]]
 h' := ![![[5, 30], [22, 8], [6, 22], [13, 9], [0, 1]], ![[0, 1], [0, 23], [23, 9], [27, 22], [5, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [11, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [16, 26, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![532743, 66661, -441897, 919705, 589782]
  a := ![3, -62, -1, -63, -58]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![296488, -580214, -441897, 919705, 589782]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25224, -10420, -20616, 2673, 3271]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![25224, -10420, -20616, 2673, 3271]] 
 ![![31, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![30, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![11, 0, 0, 0, 1]] where
  M :=![![![25224, -10420, -20616, 2673, 3271], ![32710, -12943, -26186, 3366, 4150], ![20750, -7897, -16309, 2080, 2582], ![-3445, 1735, 3116, -420, -497], ![-5500, 2233, 4458, -576, -707]]]
  hmulB := by decide  
  f := ![![![-256, 262, -102, -239, 149]], ![![-18, 7, 6, -26, -2]], ![![-450, 471, -195, -406, 256]], ![![535, -685, 376, 382, -441]], ![![-1586, 1765, -822, -1325, 952]]]
  g := ![![![22293, -10420, -20616, 2673, 3271], ![28264, -12943, -26186, 3366, 4150], ![17574, -7897, -16309, 2080, 2582], ![-3398, 1735, 3116, -420, -497], ![-4817, 2233, 4458, -576, -707]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1

def I31N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![614, -972, 764, 103, -147]] i)))

def SI31N2: IdealEqSpanCertificate' Table ![![614, -972, 764, 103, -147]] 
 ![![31, 0, 0, 0, 0], ![19, 1, 0, 0, 0], ![21, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![21, 0, 0, 0, 1]] where
  M :=![![![614, -972, 764, 103, -147], ![-1470, 2613, -2150, -30, 706], ![3530, -4311, 2643, 2056, -766], ![-3095, 6517, -5292, 118, 4525], ![15360, -16677, 8242, 11972, -5143]]]
  hmulB := by decide  
  f := ![![![567834, 1002622, 727958, -157773, -125833]], ![![307436, 674545, 521032, -108623, -89363]], ![![323464, 727247, 565091, -117375, -96849]], ![![108797, 264233, 208976, -42936, -35739]], ![![385064, 670907, 484978, -105405, -83880]]]
  g := ![![![171, -972, 764, 103, -147], ![-663, 2613, -2150, -30, 706], ![954, -4311, 2643, 2056, -766], ![-3605, 6517, -5292, 118, 4525], ![5528, -16677, 8242, 11972, -5143]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N2 : Nat.card (O ⧸ I31N2) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N2)

lemma isPrimeI31N2 : Ideal.IsPrime I31N2 := prime_ideal_of_norm_prime hp31.out _ NI31N2

def I31N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-14, 14, -4, -9, 7]] i)))

def SI31N3: IdealEqSpanCertificate' Table ![![-14, 14, -4, -9, 7]] 
 ![![31, 0, 0, 0, 0], ![25, 1, 0, 0, 0], ![13, 0, 1, 0, 0], ![11, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![-14, 14, -4, -9, 7], ![70, -85, 46, 58, -50], ![-250, 291, -143, -196, 166], ![795, -931, 464, 628, -533], ![-1890, 2215, -1106, -1494, 1269]]]
  hmulB := by decide  
  f := ![![![286, -116, -182, 27, 29]], ![![240, -95, -156, 23, 25]], ![![128, -53, -79, 13, 13]], ![![101, -39, -66, 13, 12]], ![![50, -23, -26, 9, 6]]]
  g := ![![![-8, 14, -4, -9, 7], ![39, -85, 46, 58, -50], ![-140, 291, -143, -196, 166], ![445, -931, 464, 628, -533], ![-1058, 2215, -1106, -1494, 1269]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N3 : Nat.card (O ⧸ I31N3) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N3)

lemma isPrimeI31N3 : Ideal.IsPrime I31N3 := prime_ideal_of_norm_prime hp31.out _ NI31N3
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![-2104, 994, 1840, -245, -293]] ![![25224, -10420, -20616, 2673, 3271]]
  ![![20077969, -6551486, -14730994, 1820680, 2322712]] where
 M := ![![![20077969, -6551486, -14730994, 1820680, 2322712]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI31N1 : IdealMulLeCertificate' Table 
  ![![20077969, -6551486, -14730994, 1820680, 2322712]] ![![614, -972, 764, 103, -147]]
  ![![286, -116, -182, 27, 29]] where
 M := ![![![286, -116, -182, 27, 29]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI31N2 : IdealMulLeCertificate' Table 
  ![![286, -116, -182, 27, 29]] ![![-14, 14, -4, -9, 7]]
  ![![31, 0, 0, 0, 0]] where
 M := ![![![31, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![407, -958, 906, -244, -260]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![407, -958, 906, -244, -260]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![13, 2, 6, 1, 0], ![10, 26, 35, 0, 1]] where
  M :=![![![407, -958, 906, -244, -260], ![-2600, 2645, -1428, -1796, -456], ![-2280, -2214, 4441, -5960, -3136], ![-14380, 4774, 4460, -19437, -8556], ![-14040, -2042, 12810, -25520, -12221]]]
  hmulB := by decide  
  f := ![![![-131789, 48846, 102322, -12980, -16188]], ![![-161880, 57889, 123652, -15572, -19544]], ![![-97720, 33718, 73461, -9184, -11600]], ![![-70281, 25498, 54036, -6825, -8544]], ![![-241050, 85498, 183449, -23064, -28989]]]
  g := ![![![167, 170, 310, -244, -260], ![684, 489, 684, -1796, -456], ![2880, 2466, 4053, -5960, -3136], ![8753, 7192, 11366, -19437, -8556], ![11890, 9912, 16045, -25520, -12221]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [1, 17, 28, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 2, 9], [5, 34, 28], [0, 1]]
 g := ![![[33, 3, 9], [14, 34], [0, 21, 26], [9, 1], []], ![[33, 6, 18, 27], [30, 16], [32, 3, 15, 4], [24, 9], [25, 7]], ![[15, 15, 29, 36], [1, 30], [27, 22, 18, 30], [35, 4], [6, 7]]]
 h' := ![![[4, 2, 9], [23, 24, 3], [0, 23, 21], [28, 31, 27], [0, 0, 1], [0, 1]], ![[5, 34, 28], [18, 21, 22], [14, 5, 33], [20, 4, 13], [28, 28, 34], [4, 2, 9]], ![[0, 1], [15, 29, 12], [33, 9, 20], [30, 2, 34], [19, 9, 2], [5, 34, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 17], []]
 b := ![[], [27, 9, 31], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [1, 17, 28, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9235108, 122051, 6311954, -14937213, -8459497]
  a := ![1, -6, 1, -7, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![7284963, 6755227, 10595071, -14937213, -8459497]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 50653 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131789, -48846, -102322, 12980, 16188]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![131789, -48846, -102322, 12980, 16188]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![7, 31, 1, 0, 0], ![5, 5, 0, 1, 0], ![2, 2, 0, 0, 1]] where
  M :=![![![131789, -48846, -102322, 12980, 16188], ![161880, -57889, -123652, 15572, 19544], ![97720, -33718, -73461, 9184, 11600], ![-22940, 9658, 18924, -2463, -3004], ![-28120, 10278, 21694, -2744, -3431]]]
  hmulB := by decide  
  f := ![![![-407, 958, -906, 244, 260]], ![![2600, -2645, 1428, 1796, 456]], ![![2163, -1975, 905, 1712, 516]], ![![685, -357, -50, 801, 328]], ![![498, -36, -318, 800, 369]]]
  g := ![![![20291, 81780, -102322, 12980, 16188], ![24608, 98875, -123652, 15572, 19544], ![14671, 58769, -73461, 9184, 11600], ![-3705, -15099, 18924, -2463, -3004], ![-4308, -17342, 21694, -2744, -3431]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P1 : CertificateIrreducibleZModOfList' 37 2 2 5 [15, 34, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 36], [0, 1]]
 g := ![![[22, 10], [36], [12, 10], [9], [1]], ![[15, 27], [36], [5, 27], [9], [1]]]
 h' := ![![[3, 36], [3, 11], [5, 31], [16, 11], [22, 3], [0, 1]], ![[0, 1], [36, 26], [24, 6], [12, 26], [31, 34], [3, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32]]
 b := ![[], [13, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N1 : CertifiedPrimeIdeal' SI37N1 37 where
  n := 2
  hpos := by decide
  P := [15, 34, 1]
  hirr := P37P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![66635, 78135, -130507, 164937, 169602]
  a := ![1, 25, -3, 24, 33]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4965, 79999, -130507, 164937, 169602]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N1 B_one_repr
lemma NI37N1 : Nat.card (O ⧸ I37N1) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![407, -958, 906, -244, -260]] ![![131789, -48846, -102322, 12980, 16188]]
  ![![37, 0, 0, 0, 0]] where
 M := ![![![-37, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![51, -16, -36, 4, 6]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![51, -16, -36, 4, 6]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![15, 10, 1, 0, 0], ![14, 31, 0, 1, 0], ![14, 23, 0, 0, 1]] where
  M :=![![![51, -16, -36, 4, 6], ![60, -19, -40, 8, 4], ![20, 4, -27, -8, 12], ![30, -44, 32, 33, -30], ![-110, 118, -48, -82, 67]]]
  hmulB := by decide  
  f := ![![![-9, 4, 12, 8, 2]], ![![20, 5, -8, 64, 28]], ![![5, 2, 1, 24, 10]], ![![24, 3, -8, 69, 30]], ![![24, 1, -8, 62, 27]]]
  g := ![![![11, 2, -36, 4, 6], ![12, 1, -40, 8, 4], ![9, 6, -27, -8, 12], ![-12, -17, 32, 33, -30], ![20, 39, -48, -82, 67]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [28, 31, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 40], [0, 1]]
 g := ![![[26, 8], [9], [36], [30, 18], [1]], ![[24, 33], [9], [36], [5, 23], [1]]]
 h' := ![![[10, 40], [2, 7], [7, 38], [21, 6], [13, 10], [0, 1]], ![[0, 1], [31, 34], [18, 3], [40, 35], [31, 31], [10, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [6, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [28, 31, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-17922, 45960, -37794, 3528, 46404]
  a := ![-1, -7, 5, -5, -18]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3660, -18360, -37794, 3528, 46404]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6396, 2354, 4950, -627, -783]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-6396, 2354, 4950, -627, -783]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![24, 6, 1, 0, 0], ![20, 38, 0, 1, 0], ![38, 19, 0, 0, 1]] where
  M :=![![![-6396, 2354, 4950, -627, -783], ![-7830, 2781, 5962, -750, -942], ![-4710, 1613, 3531, -440, -558], ![1125, -467, -928, 118, 149], ![1370, -503, -1044, 138, 161]]]
  hmulB := by decide  
  f := ![![![764, -1288, 1060, 35, -179]], ![![-1790, 3147, -2646, 42, 498]], ![![246, -389, 309, 36, -42]], ![![-1315, 2363, -2008, 80, 397]], ![![2, 88, -112, 88, 55]]]
  g := ![![![-2022, 277, 4950, -627, -783], ![-2442, 327, 5962, -750, -942], ![-1450, 189, 3531, -440, -558], ![375, -54, -928, 118, 149], ![428, -62, -1044, 138, 161]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P1 : CertificateIrreducibleZModOfList' 41 2 2 5 [37, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 40], [0, 1]]
 g := ![![[25, 10], [10], [10], [31, 37], [1]], ![[0, 31], [10], [10], [0, 4], [1]]]
 h' := ![![[18, 40], [40, 16], [0, 25], [1, 25], [4, 18], [0, 1]], ![[0, 1], [0, 25], [40, 16], [0, 16], [0, 23], [18, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [22, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N1 : CertifiedPrimeIdeal' SI41N1 41 where
  n := 2
  hpos := by decide
  P := [37, 23, 1]
  hirr := P41P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-60763, 70360, -34322, -49310, 41580]
  a := ![0, -4, -2, -14, 12]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![4125, 33172, -34322, -49310, 41580]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N1 B_one_repr
lemma NI41N1 : Nat.card (O ⧸ I41N1) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5341, 9104, -7536, -150, 1312]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![-5341, 9104, -7536, -150, 1312]] 
 ![![41, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![21, 0, 1, 0, 0], ![24, 0, 0, 1, 0], ![22, 0, 0, 0, 1]] where
  M :=![![![-5341, 9104, -7536, -150, 1312], ![13120, -22361, 18508, 372, -3224], ![-16120, 27470, -22733, -464, 3968], ![13280, -22598, 18680, 425, -3284], ![-29470, 50164, -41472, -930, 7305]]]
  hmulB := by decide  
  f := ![![![239379, -78876, -176368, 21842, 27816]], ![![59331, -19461, -43628, 5398, 6880]], ![![126479, -41570, -93085, 11522, 14680]], ![![138896, -45718, -102288, 12665, 16132]], ![![127228, -41928, -93744, 11610, 14785]]]
  g := ![![![1115, 9104, -7536, -150, 1312], ![-2739, -22361, 18508, 372, -3224], ![3363, 27470, -22733, -464, 3968], ![-2770, -22598, 18680, 425, -3284], ![6136, 50164, -41472, -930, 7305]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![51, -16, -36, 4, 6]] ![![-6396, 2354, 4950, -627, -783]]
  ![![-18636, 12604, 19966, -2837, -3211]] where
 M := ![![![-18636, 12604, 19966, -2837, -3211]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![-18636, 12604, 19966, -2837, -3211]] ![![-5341, 9104, -7536, -150, 1312]]
  ![![41, 0, 0, 0, 0]] where
 M := ![![![246, -246, 82, 369, -287]]]
 hmul := by decide  
 g := ![![![![6, -6, 2, 9, -7]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1, I41N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
    exact isPrimeI41N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0 ⊙ MulI41N1)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0, 0, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0, 0, 0]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![0, 0, 0, 0, 43]] where
  M :=![![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![0, 0, 0, 0, 43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 5 2 5 [18, 19, 39, 9, 33, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 8, 0, 10, 13], [15, 28, 39, 40, 15], [38, 25, 4, 35, 33], [21, 24, 0, 1, 25], [0, 1]]
 g := ![![[37, 11, 38, 12, 23], [2, 8, 15, 10, 14], [12, 22, 3, 14], [1], []], ![[32, 33, 27, 7, 26, 32, 38, 41], [8, 39, 35, 22, 29, 17, 2, 31], [30, 1, 9, 23], [31, 39, 18, 30, 10, 28, 31, 38], [36, 19, 15, 40]], ![[39, 13, 32, 35, 16, 32, 28, 21], [30, 2, 14, 21, 34, 23, 22, 11], [41, 39, 6, 1], [33, 34, 42, 34, 37, 10], [19, 28, 10, 10]], ![[40, 12, 20, 23, 3, 3, 40, 26], [13, 15, 31, 29, 22, 33, 31, 33], [6, 31, 4, 4], [2, 11, 35, 30, 30, 23, 12, 34], [2, 20, 42, 14]], ![[27, 28, 11, 26, 18, 25, 11, 17], [15, 16, 11, 12, 0, 14, 35, 1], [23, 0, 4, 25], [0, 13, 30, 35, 21, 0, 2, 24], [30, 14, 22, 23]]]
 h' := ![![[22, 8, 0, 10, 13], [7, 1, 33, 18, 25], [22, 17, 8, 15, 10], [25, 24, 4, 34, 10], [0, 0, 1], [0, 1]], ![[15, 28, 39, 40, 15], [35, 7, 13, 0, 18], [33, 24, 17, 4, 40], [33, 21, 16, 36, 25], [8, 14, 7, 4, 6], [22, 8, 0, 10, 13]], ![[38, 25, 4, 35, 33], [32, 26, 20, 1, 15], [16, 0, 26, 38, 9], [18, 28, 35, 41, 1], [12, 18, 28, 31], [15, 28, 39, 40, 15]], ![[21, 24, 0, 1, 25], [16, 23, 17, 0, 7], [37, 37, 7, 21, 1], [4, 8, 8, 34, 2], [32, 40, 16, 23, 17], [38, 25, 4, 35, 33]], ![[0, 1], [19, 29, 3, 24, 21], [29, 8, 28, 8, 26], [23, 5, 23, 27, 5], [30, 14, 34, 28, 20], [21, 24, 0, 1, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19, 3, 31, 25], [], [], []]
 b := ![[], [6, 32, 22, 14, 8], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 5
  hpos := by decide
  P := [18, 19, 39, 9, 33, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![73800892283865, -216998708516329, 186041697639614, -34898547762688, -228342636159525]
  a := ![13, -7, 4, -6, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1716299820555, -5046481593403, 4326551107898, -811594134016, -5310293864175]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 147008443 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def PBC43 : ContainsPrimesAboveP 43 ![I43N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![43, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 43 (by decide) 𝕀

instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0, 0, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0, 0, 0]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![0, 0, 0, 0, 47]] where
  M :=![![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![0, 0, 0, 0, 47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 5 2 5 [3, 34, 5, 14, 29, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [43, 36, 12, 25, 16], [25, 12, 6, 20, 46], [17, 1, 23, 27, 36], [27, 44, 6, 22, 43], [0, 1]]
 g := ![![[17, 2, 26, 20, 21], [46, 18, 12, 17, 34], [5, 25, 16, 17, 42], [1], []], ![[45, 40, 33, 30, 35, 20, 8, 36], [21, 42, 17, 22, 7, 5, 20, 16], [13, 45, 44, 23, 39, 23, 10, 18], [11, 37, 1, 31, 22, 4, 37, 3], [31, 17, 3, 21]], ![[24, 28, 43, 16, 9, 32, 19, 38], [45, 11, 1, 24, 27, 14, 7, 41], [25, 39, 19, 18, 38, 1, 15, 10], [3, 27, 36, 38, 44, 42, 17, 13], [29, 25, 25, 1]], ![[42, 31, 25, 8, 29, 0, 19, 7], [26, 32, 32, 17, 9, 2, 35, 3], [25, 0, 42, 33, 38, 7, 34, 9], [46, 24, 29, 39, 1, 33, 46, 34], [18, 16, 33, 27]], ![[4, 17, 34, 10, 39, 31, 4, 19], [11, 35, 16, 10, 43, 8, 26, 10], [10, 20, 3, 6, 33, 44, 42, 23], [37, 45, 17, 13, 16, 20, 24, 10], [16, 19, 18, 16]]]
 h' := ![![[43, 36, 12, 25, 16], [3, 17, 45, 27, 16], [32, 46, 33, 20, 38], [44, 13, 42, 33, 18], [0, 0, 1], [0, 1]], ![[25, 12, 6, 20, 46], [30, 0, 36, 3, 22], [23, 8, 35, 7, 1], [33, 40, 30, 39, 30], [17, 17, 35, 27, 44], [43, 36, 12, 25, 16]], ![[17, 1, 23, 27, 36], [34, 6, 42, 8, 44], [35, 24, 0, 35, 37], [18, 36, 30, 9, 32], [21, 9, 32, 42, 9], [25, 12, 6, 20, 46]], ![[27, 44, 6, 22, 43], [44, 17, 42, 4, 42], [31, 30, 34, 36, 2], [3, 9, 13, 24, 24], [0, 32, 3, 40, 25], [17, 1, 23, 27, 36]], ![[0, 1], [32, 7, 23, 5, 17], [19, 33, 39, 43, 16], [25, 43, 26, 36, 37], [23, 36, 23, 32, 16], [27, 44, 6, 22, 43]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32, 42, 32, 15], [], [], []]
 b := ![[], [12, 9, 7, 0, 2], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 5
  hpos := by decide
  P := [3, 34, 5, 14, 29, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-763993566502, 895294517205, -446883773847, -603612509826, 512857686537]
  a := ![-1, -1, -1, -2, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-16255182266, 19048819515, -9508165401, -12842819358, 10911865671]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 229345007 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def PBC47 : ContainsPrimesAboveP 47 ![I47N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![47, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 47 (by decide) 𝕀

instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3437, 664, 1672, -5118, -2300]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-3437, 664, 1672, -5118, -2300]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![2, 45, 30, 1, 0], ![22, 0, 34, 0, 1]] where
  M :=![![![-3437, 664, 1672, -5118, -2300], ![-23000, 4099, 11564, -34492, -15872], ![-79360, 15342, 38591, -118160, -53112], ![-254060, 45298, 127720, -380995, -175272], ![-339330, 67616, 162800, -503790, -224343]]]
  hmulB := by decide  
  f := ![![![-35209, 20236, 34264, -4734, -5484]], ![![-54840, 27975, 49940, -6748, -7968]], ![![-39840, 18690, 34723, -4616, -5528]], ![![-70446, 35061, 63318, -8515, -10096]], ![![-40016, 20304, 36350, -4906, -5799]]]
  g := ![![![1083, 4358, 4404, -5118, -2300], ![7456, 29363, 29924, -34492, -15872], ![25008, 100614, 101683, -118160, -53112], ![82338, 324341, 330506, -380995, -175272], ![105732, 429022, 432154, -503790, -224343]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [24, 20, 41, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [39, 48, 49], [26, 4, 4], [0, 1]]
 g := ![![[5, 45, 43], [7, 47], [39, 2, 25], [29, 38], [1]], ![[1, 39, 52, 11], [13, 9], [37, 4, 30, 7], [48, 7], [17, 31, 52, 42]], ![[51, 17, 26, 10], [46, 10], [36, 17, 20, 43], [11, 43], [31, 20, 6, 11]]]
 h' := ![![[39, 48, 49], [50, 42, 19], [18, 4, 43], [39, 51, 48], [29, 33, 12], [0, 1]], ![[26, 4, 4], [2, 9, 14], [46, 7, 50], [3, 50, 41], [28, 4, 22], [39, 48, 49]], ![[0, 1], [34, 2, 20], [5, 42, 13], [8, 5, 17], [31, 16, 19], [26, 4, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34, 47], []]
 b := ![[], [9, 42, 25], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [24, 20, 41, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-86396820, 115239894, -65835750, -58297268, 77262832]
  a := ![3, 3, 0, -1, 14]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-31501596, 51672018, -17808566, -58297268, 77262832]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 148877 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![35209, -20236, -34264, 4734, 5484]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![35209, -20236, -34264, 4734, 5484]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![43, 23, 1, 0, 0], ![18, 23, 0, 1, 0], ![48, 32, 0, 0, 1]] where
  M :=![![![35209, -20236, -34264, 4734, 5484], ![54840, -27975, -49940, 6748, 7968], ![39840, -18690, -34723, 4616, 5528], ![220, 1814, 1664, -313, -280], ![-8310, 4540, 7840, -1074, -1253]]]
  hmulB := by decide  
  f := ![![![3437, -664, -1672, 5118, 2300]], ![![23000, -4099, -11564, 34492, 15872]], ![![14267, -2607, -7103, 21350, 9756]], ![![15942, -2859, -7996, 23895, 10976]], ![![23402, -4352, -11568, 34966, 15899]]]
  g := ![![![21889, 9122, -34264, 4734, 5484], ![32044, 13405, -49940, 6748, 7968], ![22349, 9375, -34723, 4616, 5528], ![-986, -383, 1664, -313, -280], ![-5018, -2094, 7840, -1074, -1253]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P1 : CertificateIrreducibleZModOfList' 53 2 2 5 [25, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [21, 52], [0, 1]]
 g := ![![[14, 17], [40], [44, 11], [11], [21, 1]], ![[0, 36], [40], [10, 42], [11], [42, 52]]]
 h' := ![![[21, 52], [17, 32], [13, 26], [15, 45], [5, 45], [0, 1]], ![[0, 1], [0, 21], [29, 27], [6, 8], [49, 8], [21, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39]]
 b := ![[], [47, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N1 : CertifiedPrimeIdeal' SI53N1 53 where
  n := 2
  hpos := by decide
  P := [25, 32, 1]
  hirr := P53P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3997, 15521, -14049, 4465, 17740]
  a := ![1, 5, -3, 4, 11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6260, -6259, -14049, 4465, 17740]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N1 B_one_repr
lemma NI53N1 : Nat.card (O ⧸ I53N1) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-3437, 664, 1672, -5118, -2300]] ![![35209, -20236, -34264, 4734, 5484]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![55449, -22941, -45352, 5882, 7196]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![55449, -22941, -45352, 5882, 7196]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![35, 54, 20, 9, 1]] where
  M :=![![![55449, -22941, -45352, 5882, 7196], ![71960, -28511, -57646, 7412, 9136], ![45680, -17407, -35923, 4582, 5688], ![-7540, 3808, 6834, -919, -1092], ![-12100, 4923, 9808, -1274, -1551]]]
  hmulB := by decide  
  f := ![![![-109, 17, 58, -166, -76]], ![![-760, 149, 366, -1128, -512]], ![![-2560, 467, 1277, -3834, -1744]], ![![-8340, 1554, 4118, -12457, -5668]], ![![-3085, 576, 1522, -4607, -2095]]]
  g := ![![![-3329, -6975, -3208, -998, 7196], ![-4200, -8845, -4074, -1268, 9136], ![-2600, -5501, -2537, -790, 5688], ![520, 1064, 486, 151, -1092], ![715, 1503, 692, 215, -1551]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 4 2 5 [36, 0, 3, 1, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 52, 3, 40], [34, 55, 32, 54], [58, 10, 24, 24], [0, 1]]
 g := ![![[37, 43, 11, 4], [47, 8, 47, 45], [26, 19, 45], [5, 57, 58, 1], []], ![[57, 39, 28, 50], [1, 55, 53, 27, 43, 50], [27, 5, 25], [27, 25, 44, 48, 20, 50], [6, 13, 42, 15, 19, 44]], ![[49, 15, 10, 2, 35, 55], [7, 57, 27, 17, 0, 24], [40, 55, 16], [18, 13, 48, 33, 37, 54], [10, 8, 10, 8, 47, 52]], ![[34, 21, 7, 27, 56, 44], [56, 49, 36, 10, 28, 56], [3, 28, 35], [22, 54, 12, 8, 25, 30], [28, 51, 40, 16, 36, 18]]]
 h' := ![![[25, 52, 3, 40], [19, 1, 48, 2], [17, 5, 56, 24], [56, 13, 21, 24], [0, 0, 0, 1], [0, 1]], ![[34, 55, 32, 54], [30, 13, 4], [8, 21, 49, 4], [53, 57, 3, 5], [10, 36, 41, 4], [25, 52, 3, 40]], ![[58, 10, 24, 24], [8, 3, 47, 44], [54, 57, 30, 40], [14, 58, 28, 55], [4, 0, 0, 58], [34, 55, 32, 54]], ![[0, 1], [30, 42, 19, 13], [14, 35, 42, 50], [57, 49, 7, 34], [53, 23, 18, 55], [58, 10, 24, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [48, 42, 2], []]
 b := ![[], [], [3, 41, 9, 24], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 4
  hpos := by decide
  P := [36, 0, 3, 1, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-189728336, 223404423, -112147824, -149136929, 128826870]
  a := ![4, 0, 0, 1, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-79638454, -114122823, -45570936, -22179301, 128826870]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 12117361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, -17, -58, 166, 76]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![109, -17, -58, 166, 76]] 
 ![![59, 0, 0, 0, 0], ![25, 1, 0, 0, 0], ![12, 0, 1, 0, 0], ![44, 0, 0, 1, 0], ![21, 0, 0, 0, 1]] where
  M :=![![![109, -17, -58, 166, 76], ![760, -149, -366, 1128, 512], ![2560, -467, -1277, 3834, 1744], ![8340, -1554, -4118, 12457, 5668], ![10900, -2017, -5402, 16298, 7405]]]
  hmulB := by decide  
  f := ![![![-55449, 22941, 45352, -5882, -7196]], ![![-24715, 10204, 20194, -2618, -3204]], ![![-12052, 4961, 9833, -1274, -1560]], ![![-41224, 17044, 33706, -4371, -5348]], ![![-19531, 8082, 15976, -2072, -2535]]]
  g := ![![![-130, -17, -58, 166, 76], ![-873, -149, -366, 1128, 512], ![-2979, -467, -1277, 3834, 1744], ![-9670, -1554, -4118, 12457, 5668], ![-12652, -2017, -5402, 16298, 7405]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![55449, -22941, -45352, 5882, 7196]] ![![109, -17, -58, 166, 76]]
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


def P61P0 : CertificateIrreducibleZModOfList' 61 5 2 5 [33, 5, 20, 53, 37, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [13, 39, 24, 48, 54], [46, 41, 54, 10, 21], [7, 13, 58, 39, 43], [19, 28, 47, 25, 4], [0, 1]]
 g := ![![[7, 25, 20], [57, 16, 35, 20], [8, 40, 31, 57, 15], [35, 24, 1], []], ![[29, 31, 55, 50, 32, 44, 45, 17], [2, 30, 60, 56], [16, 21, 15, 8, 16, 40, 14, 23], [26, 12, 32, 30, 50, 60, 3, 35], [44, 50, 25, 6, 38, 60, 44, 23]], ![[22, 20, 42, 10, 31, 19, 8, 33], [3, 57, 16, 58], [46, 19, 15, 45, 6, 9, 56, 50], [21, 38, 54, 21, 20, 40, 27, 2], [2, 52, 40, 38, 33, 24, 34, 50]], ![[15, 23, 37, 32, 19, 34, 32, 18], [12, 35, 50, 36], [32, 1, 22, 22, 46, 23, 20, 2], [19, 57, 55, 31, 43, 40, 45, 33], [4, 26, 28, 16, 6, 8, 54, 24]], ![[54, 46, 31, 21, 30, 52, 36, 3], [28, 6, 33, 49], [26, 19, 36, 12, 24, 23, 11, 46], [20, 17, 59, 48, 35, 23, 57, 3], [3, 29, 44, 19, 12, 48, 52, 3]]]
 h' := ![![[13, 39, 24, 48, 54], [44, 60, 49, 52], [41, 59, 31, 1, 52], [4, 9, 1, 39, 36], [0, 0, 0, 1], [0, 1]], ![[46, 41, 54, 10, 21], [7, 31, 53, 20, 25], [16, 57, 48, 37, 42], [58, 40, 51, 27, 7], [13, 30, 53, 20, 42], [13, 39, 24, 48, 54]], ![[7, 13, 58, 39, 43], [59, 52, 18, 5, 43], [55, 41, 15, 31, 27], [58, 54, 6, 11, 40], [36, 24, 55, 20, 8], [46, 41, 54, 10, 21]], ![[19, 28, 47, 25, 4], [19, 56, 11, 51, 50], [7, 8, 13, 17, 55], [42, 60, 16, 41, 24], [28, 57, 22, 12, 7], [7, 13, 58, 39, 43]], ![[0, 1], [55, 45, 52, 55, 4], [53, 18, 15, 36, 7], [53, 20, 48, 4, 15], [50, 11, 53, 8, 4], [19, 28, 47, 25, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34, 1, 49, 10], [], [], []]
 b := ![[], [17, 52, 29, 46, 45], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 5
  hpos := by decide
  P := [33, 5, 20, 53, 37, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-303190345342749, -47258424362306574, 51945109584377912, -34242878238359640, -65026071697492286]
  a := ![7, -21, -1, -21, -44]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4970333530209, -774728268234534, 851559173514392, -561358659645240, -1066001175368726]
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



lemma PB1640I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB1640I1 : PrimesBelowBoundCertificateInterval O 23 61 1640 where
  m := 9
  g := ![3, 4, 2, 3, 1, 1, 2, 2, 1]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB1640I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1, I29N2]
    · exact ![I31N0, I31N1, I31N2, I31N3]
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0]
    · exact ![I47N0]
    · exact ![I53N0, I53N1]
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
    · exact ![24389, 29, 29]
    · exact ![961, 31, 31, 31]
    · exact ![50653, 1369]
    · exact ![1681, 1681, 41]
    · exact ![147008443]
    · exact ![229345007]
    · exact ![148877, 2809]
    · exact ![12117361, 59]
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
      exact NI31N3
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
      exact NI41N2
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
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
  β := ![I29N1, I29N2, I31N0, I31N1, I31N2, I31N3, I37N1, I41N2, I59N1]
  Il := ![[I29N1, I29N2], [I31N0, I31N1, I31N2, I31N3], [I37N1], [I41N2], [], [], [], [I59N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
