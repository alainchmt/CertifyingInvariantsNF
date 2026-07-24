
import IdealArithmetic.Examples.NF5_1_48600000_5.RI5_1_48600000_5
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1188, -1974, 3106, -1220, 481]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![-1188, -1974, 3106, -1220, 481]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![12, 5, 7, 5, 1]] where
  M :=![![![-1188, -1974, 3106, -1220, 481], ![1478, -2927, -5426, 3772, -8282], ![4510, 22503, -7437, -1654, 19598], ![-18683, -50649, 43160, -10977, -20419], ![14301, 27136, -36412, 13274, -976]]]
  hmulB := by decide  
  f := ![![![-1058, 142, 60, -18, -145]], ![![326, -309, -42, 84, 182]], ![![-266, -229, -43, 42, 70]], ![![-275, -133, -96, -43, -35]], ![![-502, -65, -9, 7, -23]]]
  g := ![![![-240, -151, -9, -125, 481], ![3478, 1327, 1812, 1558, -8282], ![-7954, -2603, -4987, -3436, 19598], ![7805, 1774, 6417, 3142, -20419], ![897, 1104, -1020, 626, -976]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 4 2 4 [11, 25, 28, 11, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 2, 6, 1], [28, 28, 25, 22], [15, 27, 27, 6], [0, 1]]
 g := ![![[26, 22], [22], [14, 6, 18, 1], []], ![[8, 3, 8, 27, 20, 23], [19, 0, 7], [14, 7, 7, 21, 23, 23], [15, 9, 9, 9, 7, 1]], ![[11, 23, 18, 4, 16, 23], [17, 22, 9], [16, 16, 23, 1, 15, 22], [6, 23, 26, 12, 24, 5]], ![[28, 4, 2, 6, 17, 22], [21, 28, 23], [12, 2, 28, 27, 18, 22], [19, 8, 22, 19, 18, 13]]]
 h' := ![![[4, 2, 6, 1], [13, 7, 15], [20, 19, 14], [0, 0, 0, 1], [0, 1]], ![[28, 28, 25, 22], [0, 4, 7, 20], [21, 19, 4, 6], [15, 28, 27, 9], [4, 2, 6, 1]], ![[15, 27, 27, 6], [3, 22, 16, 18], [4, 10, 25, 3], [20, 0, 0, 28], [28, 28, 25, 22]], ![[0, 1], [6, 25, 20, 20], [11, 10, 15, 20], [5, 1, 2, 20], [15, 27, 27, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [28, 26, 19], []]
 b := ![[], [], [17, 24, 19, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 4
  hpos := by decide
  P := [11, 25, 28, 11, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-15326058, -27101645, 7573980, 7244940, 777783]
  a := ![5, -7, -8, -8, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-850326, -1068640, 73431, 115725, 777783]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 707281 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1058, 142, 60, -18, -145]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![-1058, 142, 60, -18, -145]] 
 ![![29, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![14, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![25, 0, 0, 0, 1]] where
  M :=![![![-1058, 142, 60, -18, -145], ![326, -309, -42, 84, 182], ![-266, -229, -43, 42, 70], ![-275, -133, -96, -43, -35], ![-255, 224, 10, -80, -152]]]
  hmulB := by decide  
  f := ![![![-1188, -1974, 3106, -1220, 481]], ![![10, -169, -80, 88, -269]], ![![-418, -177, 1243, -646, 908]], ![![-931, -2223, 2238, -673, -588]], ![![-531, -766, 1422, -594, 381]]]
  g := ![![![59, 142, 60, -18, -145], ![-135, -309, -42, 84, 182], ![-51, -229, -43, 42, 70], ![82, -133, -96, -43, -35], ![129, 224, 10, -80, -152]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![-1188, -1974, 3106, -1220, 481]] ![![-1058, 142, 60, -18, -145]]
  ![![29, 0, 0, 0, 0]] where
 M := ![![![29, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1035, -2769, 2406, -626, -1074]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![-1035, -2769, 2406, -626, -1074]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![13, 16, 13, 22, 1]] where
  M :=![![![-1035, -2769, 2406, -626, -1074], ![3400, 5489, -8938, 3560, -1608], ![-1952, 4811, 7441, -5378, 12288], ![-8610, -36098, 16190, 283, -27618], ![11154, 32049, -25240, 5794, 14777]]]
  hmulB := by decide  
  f := ![![![-269, -231, 196, 262, 282]], ![![-1088, -959, 626, 916, 1008]], ![![-1924, -1835, 965, 1542, 1740]], ![![-2738, -2808, 1134, 2049, 2382]], ![![-3413, -3347, 1605, 2672, 3047]]]
  g := ![![![417, 465, 528, 742, -1074], ![784, 1007, 386, 1256, -1608], ![-5216, -6187, -4913, -8894, 12288], ![11304, 13090, 12104, 19609, -27618], ![-5837, -6593, -7011, -10300, 14777]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 4 2 4 [1, 15, 3, 29, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [7, 22, 16, 30], [12, 12, 5, 18], [14, 27, 10, 14], [0, 1]]
 g := ![![[24, 28, 15, 14], [10, 0, 20, 7], [12, 1, 2, 1], []], ![[23, 10, 11, 27, 18, 13], [27, 5, 26, 23, 19, 22], [11, 17, 28, 26, 14, 3], [27, 4, 17, 13, 15, 30]], ![[13, 20, 16, 17, 6, 14], [14, 26, 12, 27, 22, 5], [11, 0, 25, 20, 26, 4], [1, 11, 8, 15, 1, 4]], ![[25, 12, 9, 29, 15, 14], [18, 3, 24, 15, 21, 5], [19, 15, 9, 17, 26, 14], [6, 23, 16, 15, 22, 16]]]
 h' := ![![[7, 22, 16, 30], [21, 25, 16, 18], [19, 5, 9, 21], [0, 0, 0, 1], [0, 1]], ![[12, 12, 5, 18], [6, 30, 30, 7], [24, 16, 8, 28], [6, 4, 20, 11], [7, 22, 16, 30]], ![[14, 27, 10, 14], [17, 12, 3, 7], [0, 13, 17, 23], [22, 12, 7, 18], [12, 12, 5, 18]], ![[0, 1], [29, 26, 13, 30], [17, 28, 28, 21], [10, 15, 4, 1], [14, 27, 10, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [11, 17, 4], []]
 b := ![[], [], [25, 11, 12, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 4
  hpos := by decide
  P := [1, 15, 3, 29, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-24032328375, 12917042268, 35785506202, -11209659244, 77616375912]
  a := ![-6, -56, 11, -57, 21]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-33324039201, -39643386204, -31394431634, -55444191268, 77616375912]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 923521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-269, -231, 196, 262, 282]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![-269, -231, 196, 262, 282]] 
 ![![31, 0, 0, 0, 0], ![25, 1, 0, 0, 0], ![13, 0, 1, 0, 0], ![11, 0, 0, 1, 0], ![15, 0, 0, 0, 1]] where
  M :=![![![-269, -231, 196, 262, 282], ![-1088, -959, 626, 916, 1008], ![-1924, -1835, 965, 1542, 1740], ![-2738, -2808, 1134, 2049, 2382], ![350, 221, -302, -354, -361]]]
  hmulB := by decide  
  f := ![![![-1035, -2769, 2406, -626, -1074]], ![![-725, -2056, 1652, -390, -918]], ![![-497, -1006, 1249, -436, -54]], ![![-645, -2147, 1376, -213, -1272]], ![![-141, -306, 350, -116, -43]]]
  g := ![![![-134, -231, 196, 262, 282], ![-337, -959, 626, 916, 1008], ![-376, -1835, 965, 1542, 1740], ![-179, -2808, 1134, 2049, 2382], ![260, 221, -302, -354, -361]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![-1035, -2769, 2406, -626, -1074]] ![![-269, -231, 196, 262, 282]]
  ![![31, 0, 0, 0, 0]] where
 M := ![![![31, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![57530, -12688, -3380, 2744, 10741]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![57530, -12688, -3380, 2744, 10741]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![24, 22, 1, 0, 0], ![27, 28, 0, 1, 0], ![30, 11, 0, 0, 1]] where
  M :=![![![57530, -12688, -3380, 2744, 10741], ![-26970, 5933, 1594, -1272, -5018], ![6290, -1415, -357, 322, 1202], ![11961, -2683, -688, 601, 2273], ![21125, -4656, -1246, 1002, 3938]]]
  hmulB := by decide  
  f := ![![![160, 316, -402, 142, 7]], ![![-298, 7, 930, -520, 838]], ![![-82, 147, 301, -206, 438]], ![![-51, 409, 282, -263, 726]], ![![-9, 149, 74, -80, 238]]]
  g := ![![![-6964, -3603, -3380, 2744, 10741], ![3234, 1667, 1594, -1272, -5018], ![-808, -427, -357, 322, 1202], ![-1512, -794, -688, 601, 2273], ![-2545, -1314, -1246, 1002, 3938]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [24, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 36], [0, 1]]
 g := ![![[28, 12], [27], [18, 4], [36], [1]], ![[30, 25], [27], [31, 33], [36], [1]]]
 h' := ![![[31, 36], [14, 30], [12, 8], [8, 35], [13, 31], [0, 1]], ![[0, 1], [19, 7], [1, 29], [20, 2], [12, 6], [31, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [26, 21]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [24, 6, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-286, -108, 113, 339, 499]
  a := ![1, -4, -1, -5, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-733, -475, 113, 339, 499]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-797, -1105, -24, 380, 552]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-797, -1105, -24, 380, 552]] 
 ![![37, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![14, 0, 1, 0, 0], ![33, 0, 0, 1, 0], ![22, 0, 0, 0, 1]] where
  M :=![![![-797, -1105, -24, 380, 552], ![-1864, -2821, -346, 712, 1176], ![-1888, -3333, -933, 366, 960], ![-394, -2034, -1834, -923, -450], ![1574, 2057, -106, -844, -1151]]]
  hmulB := by decide  
  f := ![![![7791, -1845, -382, 360, 1392]], ![![537, -118, -36, 28, 96]], ![![2966, -707, -131, 130, 540]], ![![6989, -1685, -340, 329, 1218]], ![![4720, -1079, -252, 220, 865]]]
  g := ![![![-590, -1105, -24, 380, 552], ![-1025, -2821, -346, 712, 1176], ![-325, -3333, -933, 366, 960], ![1939, -2034, -1834, -923, -450], ![1353, 2057, -106, -844, -1151]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![748, 1076, -2004, 838, -541]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![748, 1076, -2004, 838, -541]] 
 ![![37, 0, 0, 0, 0], ![30, 1, 0, 0, 0], ![31, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![11, 0, 0, 0, 1]] where
  M :=![![![748, 1076, -2004, 838, -541], ![-594, 3125, 2746, -2332, 6110], ![-3778, -16531, 6903, 414, -13106], ![12989, 33179, -30596, 8483, 11293], ![-9215, -15750, 23966, -9280, 3106]]]
  hmulB := by decide  
  f := ![![![-12362, -15240, 3462, 8696, 10817]], ![![-11078, -13589, 3038, 7708, 9596]], ![![-11840, -14587, 3151, 8174, 10209]], ![![-1841, -2389, 194, 1045, 1398]], ![![-3077, -3878, 846, 2182, 2729]]]
  g := ![![![965, 1076, -2004, 838, -541], ![-6604, 3125, 2746, -2332, 6110], ![11403, -16531, 6903, 414, -13106], ![-4503, 33179, -30596, 8483, 11293], ![-8231, -15750, 23966, -9280, 3106]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2

def I37N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 1, 0, 0, 0]] i)))

def SI37N3: IdealEqSpanCertificate' Table ![![-3, 1, 0, 0, 0]] 
 ![![37, 0, 0, 0, 0], ![34, 1, 0, 0, 0], ![14, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  M :=![![![-3, 1, 0, 0, 0], ![0, -3, 2, 0, 0], ![0, 1, -3, 2, 0], ![-2, 2, 2, -1, 6], ![-2, -5, 2, 0, -5]]]
  hmulB := by decide  
  f := ![![![17, 29, -10, -20, -24]], ![![18, 29, -10, -20, -24]], ![![10, 15, -5, -10, -12]], ![![6, 8, -2, -5, -6]], ![![3, 6, -2, -4, -5]]]
  g := ![![![-1, 1, 0, 0, 0], ![2, -3, 2, 0, 0], ![0, 1, -3, 2, 0], ![-4, 2, 2, -1, 6], ![5, -5, 2, 0, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N3 : Nat.card (O ⧸ I37N3) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N3)

lemma isPrimeI37N3 : Ideal.IsPrime I37N3 := prime_ideal_of_norm_prime hp37.out _ NI37N3
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![57530, -12688, -3380, 2744, 10741]] ![![-797, -1105, -24, 380, 552]]
  ![![5660, 679, -8174, -7652, -7019]] where
 M := ![![![5660, 679, -8174, -7652, -7019]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![5660, 679, -8174, -7652, -7019]] ![![748, 1076, -2004, 838, -541]]
  ![![-17, -29, 10, 20, 24]] where
 M := ![![![-17, -29, 10, 20, 24]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI37N2 : IdealMulLeCertificate' Table 
  ![![-17, -29, 10, 20, 24]] ![![-3, 1, 0, 0, 0]]
  ![![37, 0, 0, 0, 0]] where
 M := ![![![-37, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![24, 25, 4, -10, -29]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![24, 25, 4, -10, -29]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![2, 26, 14, 6, 1]] where
  M :=![![![24, 25, 4, -10, -29], ![78, 153, -28, -12, -2], ![14, 18, 139, -40, -34], ![35, 45, -42, 105, -85], ![-41, 41, 0, 0, 164]]]
  hmulB := by decide  
  f := ![![![-5374, 1185, 316, -256, -1003]], ![![2518, -555, -148, 120, 470]], ![![-590, 130, 35, -28, -110]], ![![-1121, 247, 66, -53, -209]], ![![921, -203, -54, 44, 172]]]
  g := ![![![2, 19, 10, 4, -29], ![2, 5, 0, 0, -2], ![2, 22, 15, 4, -34], ![5, 55, 28, 15, -85], ![-9, -103, -56, -24, 164]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 4 2 5 [29, 13, 40, 34, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 32, 16, 11], [28, 8, 13, 15], [24, 0, 12, 15], [0, 1]]
 g := ![![[27, 32, 1, 4], [17, 7, 39], [22, 8, 40], [7, 1], []], ![[40, 21, 9, 5, 1, 24], [19, 21, 2], [5, 40, 21], [18, 6, 18, 37, 22, 30], [3, 10, 39]], ![[23, 24, 14, 15, 35, 26], [15, 7, 9], [4, 34, 20], [18, 8, 27, 21, 26, 17], [39, 38, 20]], ![[2, 32, 19, 7, 19, 27], [24, 6, 40], [3, 11, 37], [26, 3, 23, 34, 37, 15], [15, 8, 20]]]
 h' := ![![[37, 32, 16, 11], [32, 26, 17, 39], [22, 27, 14, 11], [2, 3, 35, 9], [0, 0, 1], [0, 1]], ![[28, 8, 13, 15], [21, 15, 5, 27], [11, 34, 1, 24], [19, 4, 13, 29], [11, 30, 7, 9], [37, 32, 16, 11]], ![[24, 0, 12, 15], [14, 33, 9, 32], [30, 27, 23, 38], [33, 18, 9, 26], [22, 28, 3, 33], [28, 8, 13, 15]], ![[0, 1], [9, 8, 10, 25], [34, 35, 3, 9], [11, 16, 25, 18], [18, 24, 30, 40], [24, 0, 12, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [8, 27, 2], []]
 b := ![[], [], [2, 22, 10, 19], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 4
  hpos := by decide
  P := [29, 13, 40, 34, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1628819068, -1764848913, 370434656, 1176031740, 1405494917]
  a := ![-8, 27, 13, 26, 25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-108288022, -934334555, -470890102, -176998482, 1405494917]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 2825761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5374, 1185, 316, -256, -1003]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-5374, 1185, 316, -256, -1003]] 
 ![![41, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![37, 0, 1, 0, 0], ![31, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-5374, 1185, 316, -256, -1003], ![2518, -555, -148, 120, 470], ![-590, 130, 35, -28, -110], ![-1121, 247, 66, -53, -209], ![-1973, 435, 116, -94, -368]]]
  hmulB := by decide  
  f := ![![![24, 25, 4, -10, -29]], ![![6, 8, 0, -2, -5]], ![![22, 23, 7, -10, -27]], ![![19, 20, 2, -5, -24]], ![![-1, 1, 0, 0, 4]]]
  g := ![![![-425, 1185, 316, -256, -1003], ![199, -555, -148, 120, 470], ![-47, 130, 35, -28, -110], ![-89, 247, 66, -53, -209], ![-156, 435, 116, -94, -368]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![24, 25, 4, -10, -29]] ![![-5374, 1185, 316, -256, -1003]]
  ![![41, 0, 0, 0, 0]] where
 M := ![![![41, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0, 0, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0, 0, 0]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![0, 0, 0, 0, 43]] where
  M :=![![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![0, 0, 0, 0, 43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 5 2 5 [30, 21, 7, 20, 8, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 11, 4, 9, 32], [25, 37, 16, 13, 19], [16, 36, 42, 8, 23], [35, 1, 24, 13, 12], [0, 1]]
 g := ![![[20, 1, 7, 1, 23], [2, 17, 27, 20, 1], [14, 37, 23, 21], [1], []], ![[3, 24, 23, 34, 17, 2, 29, 27], [10, 4, 25, 22, 1, 24, 39, 22], [41, 29, 37, 31], [34, 0, 4, 13, 16, 26, 12, 18], [33, 21, 38, 35]], ![[22, 42, 37, 41, 26, 14, 17, 26], [20, 18, 19, 31, 11, 31, 12, 7], [5, 1, 24, 10], [30, 29, 22, 37, 32, 8, 13, 18], [27, 24, 14, 17]], ![[14, 4, 8, 9, 10, 33, 10, 17], [36, 30, 22, 23, 42, 20, 21, 36], [20, 21, 14, 36], [13, 39, 25, 34, 18, 13, 42, 25], [8, 11, 6, 13]], ![[30, 12, 0, 13, 41, 30, 15, 19], [8, 17, 6, 9, 25, 42, 19, 2], [10, 26, 27, 15], [25, 22, 26, 30, 22, 15, 24, 12], [13, 27, 20, 15]]]
 h' := ![![[2, 11, 4, 9, 32], [26, 13, 28, 8, 25], [7, 28, 27, 14, 1], [13, 22, 36, 23, 35], [0, 0, 1], [0, 1]], ![[25, 37, 16, 13, 19], [6, 32, 33, 14, 35], [14, 34, 24, 30, 16], [30, 33, 25, 40, 17], [3, 11, 2, 6, 33], [2, 11, 4, 9, 32]], ![[16, 36, 42, 8, 23], [12, 22, 9, 35, 29], [3, 35, 21, 4, 18], [14, 3, 22, 8, 28], [30, 4, 24, 21, 28], [25, 37, 16, 13, 19]], ![[35, 1, 24, 13, 12], [31, 30, 9, 22, 13], [23, 20, 37, 12, 14], [8, 40, 24, 25, 37], [16, 9, 23, 33, 26], [16, 36, 42, 8, 23]], ![[0, 1], [34, 32, 7, 7, 27], [16, 12, 20, 26, 37], [12, 31, 22, 33, 12], [18, 19, 36, 26, 42], [35, 1, 24, 13, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33, 40, 21, 41], [], [], []]
 b := ![[], [0, 21, 12, 33, 35], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 5
  hpos := by decide
  P := [30, 21, 7, 20, 8, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![72493073060, 99735204007, -195673193125, 84049055041, -59419090287]
  a := ![10, -9, -15, -7, -31]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1685885420, 2319423349, -4550539375, 1954629187, -1381839309]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 17, 0, -4, -6]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![11, 17, 0, -4, -6]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![20, 10, 1, 0, 0], ![35, 28, 0, 1, 0], ![14, 2, 0, 0, 1]] where
  M :=![![![11, 17, 0, -4, -6], ![20, 33, 14, -8, -12], ![20, 39, 13, 6, -12], ![-4, 36, 26, 23, 36], ![-28, -49, 14, 8, 5]]]
  hmulB := by decide  
  f := ![![![-18807, 4147, 1106, -896, -3510]], ![![8812, -1943, -518, 420, 1644]], ![![-6172, 1361, 363, -294, -1152]], ![![-8839, 1949, 520, -421, -1650]], ![![-5374, 1185, 316, -256, -1003]]]
  g := ![![![5, 3, 0, -4, -6], ![4, 3, 14, -8, -12], ![-6, -5, 13, 6, -12], ![-39, -20, 26, 23, 36], ![-14, -9, 14, 8, 5]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [12, 41, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 46], [0, 1]]
 g := ![![[23, 4], [46, 8], [40, 9], [25, 36], [1]], ![[0, 43], [0, 39], [0, 38], [6, 11], [1]]]
 h' := ![![[6, 46], [12, 45], [37, 33], [29, 3], [35, 6], [0, 1]], ![[0, 1], [0, 2], [0, 14], [0, 44], [24, 41], [6, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [23, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [12, 41, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3874, 7388, -11402, 5174, -546]
  a := ![-6, -4, 10, -14, 18]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1244, -476, -11402, 5174, -546]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![147, 320, 146, 16, -46]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![147, 320, 146, 16, -46]] 
 ![![47, 0, 0, 0, 0], ![16, 1, 0, 0, 0], ![13, 0, 1, 0, 0], ![29, 0, 0, 1, 0], ![44, 0, 0, 0, 1]] where
  M :=![![![147, 320, 146, 16, -46], ![60, 555, 580, 324, 188], ![-512, 174, 1067, 904, 784], ![-1718, -1056, 1572, 1809, 1834], ![-442, -734, -162, 120, 247]]]
  hmulB := by decide  
  f := ![![![-335, -360, 662, -272, 130]], ![![-108, -141, 204, -76, 4]], ![![-69, 10, 141, -80, 126]], ![![-295, -452, 614, -223, -4]], ![![-250, -222, 454, -192, 107]]]
  g := ![![![-113, 320, 146, 16, -46], ![-724, 555, 580, 324, 188], ![-1657, 174, 1067, 904, 784], ![-2945, -1056, 1572, 1809, 1834], ![-20, -734, -162, 120, 247]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![411, 1643, -796, 20, 1204]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![411, 1643, -796, 20, 1204]] 
 ![![47, 0, 0, 0, 0], ![26, 1, 0, 0, 0], ![38, 0, 1, 0, 0], ![10, 0, 0, 1, 0], ![10, 0, 0, 0, 1]] where
  M :=![![![411, 1643, -796, 20, 1204], ![-2448, -6365, 5734, -1552, -2288], ![3840, 5811, -10205, 4182, -2368], ![-590, 10102, 4758, -5247, 16058], ![-3734, -17071, 6610, 716, -13999]]]
  hmulB := by decide  
  f := ![![![-582299, 128349, 34370, -27600, -108532]], ![![-316330, 69715, 18682, -14980, -58944]], ![![-472178, 104053, 27885, -22358, -87980]], ![![-126516, 27842, 7486, -5963, -23538]], ![![-128440, 28309, 7576, -6092, -23943]]]
  g := ![![![-517, 1643, -796, 20, 1204], ![-350, -6365, 5734, -1552, -2288], ![4732, 5811, -10205, 4182, -2368], ![-11748, 10102, 4758, -5247, 16058], ![6846, -17071, 6610, 716, -13999]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2

def I47N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1482, -1400, 760, 1198, 1347]] i)))

def SI47N3: IdealEqSpanCertificate' Table ![![-1482, -1400, 760, 1198, 1347]] 
 ![![47, 0, 0, 0, 0], ![32, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![45, 0, 0, 1, 0], ![30, 0, 0, 0, 1]] where
  M :=![![![-1482, -1400, 760, 1198, 1347], ![-5090, -5061, 2290, 3916, 4494], ![-8410, -8719, 3349, 6206, 7254], ![-10915, -11929, 3596, 7597, 9117], ![2073, 1818, -1230, -1776, -1948]]]
  hmulB := by decide  
  f := ![![![1052, 3820, -2078, 172, 2607]], ![![598, 2309, -1134, 36, 1686]], ![![282, 629, -683, 218, 123]], ![![1021, 4243, -1862, -57, 3294]], ![![465, 1578, -936, 114, 1010]]]
  g := ![![![-1166, -1400, 760, 1198, 1347], ![-3524, -5061, 2290, 3916, 4494], ![-5171, -8719, 3349, 6206, 7254], ![-5586, -11929, 3596, 7597, 9117], ![1881, 1818, -1230, -1776, -1948]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N3 : Nat.card (O ⧸ I47N3) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N3)

lemma isPrimeI47N3 : Ideal.IsPrime I47N3 := prime_ideal_of_norm_prime hp47.out _ NI47N3
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![11, 17, 0, -4, -6]] ![![147, 320, 146, 16, -46]]
  ![![12161, 21583, 6150, -2272, -6128]] where
 M := ![![![12161, 21583, 6150, -2272, -6128]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![12161, 21583, 6150, -2272, -6128]] ![![411, 1643, -796, 20, 1204]]
  ![![1419, 1722, -240, -760, -1164]] where
 M := ![![![1419, 1722, -240, -760, -1164]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI47N2 : IdealMulLeCertificate' Table 
  ![![1419, 1722, -240, -760, -1164]] ![![-1482, -1400, 760, 1198, 1347]]
  ![![47, 0, 0, 0, 0]] where
 M := ![![![-2967110, -1659194, 2916820, 3247418, 3247653]]]
 hmul := by decide  
 g := ![![![![-63130, -35302, 62060, 69094, 69099]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0, 0, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0, 0, 0]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![0, 0, 0, 0, 53]] where
  M :=![![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![0, 0, 0, 0, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 5 2 5 [11, 0, 46, 9, 45, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [36, 16, 38, 47, 45], [38, 6, 24, 40, 38], [42, 49, 37, 43, 37], [51, 34, 7, 29, 39], [0, 1]]
 g := ![![[16, 30, 12, 48, 42], [25, 18, 34, 46], [29, 45, 45, 37, 4], [8, 1], []], ![[15, 22, 8, 34, 42, 23, 31, 34], [51, 16, 49, 25], [14, 14, 49, 9, 13, 42, 29, 51], [21, 18, 34, 49], [26, 17, 4, 25, 7, 8, 52, 18]], ![[37, 47, 33, 11, 3, 6, 42, 1], [19, 9, 22, 38], [25, 9, 29, 23, 18, 28, 50, 42], [0, 50, 3, 49], [5, 43, 4, 35, 15, 15, 0, 17]], ![[15, 1, 17, 46, 34, 38, 28, 7], [32, 1, 32, 25], [39, 37, 39, 30, 10, 14, 49, 6], [35, 40, 36, 1], [41, 33, 36, 18, 5, 41, 44, 38]], ![[20, 5, 21, 25, 28, 5], [10, 12, 18, 4], [46, 45, 26, 10, 37, 45, 31, 27], [34, 11, 36, 13], [31, 20, 29, 44, 36, 29, 29, 12]]]
 h' := ![![[36, 16, 38, 47, 45], [44, 38, 49, 43, 25], [52, 41, 1, 35, 24], [18, 42, 3, 41, 2], [0, 0, 0, 1], [0, 1]], ![[38, 6, 24, 40, 38], [15, 2, 45, 5, 3], [29, 25, 37, 31, 48], [6, 10, 7, 29, 26], [48, 11, 47, 35, 7], [36, 16, 38, 47, 45]], ![[42, 49, 37, 43, 37], [4, 27, 33, 3, 31], [52, 43, 32, 25, 41], [13, 18, 46, 49, 33], [15, 26, 49, 29, 7], [38, 6, 24, 40, 38]], ![[51, 34, 7, 29, 39], [34, 8, 0, 47, 47], [11, 37, 52, 38, 48], [15, 47, 10, 21, 24], [20, 40, 21, 14, 1], [42, 49, 37, 43, 37]], ![[0, 1], [7, 31, 32, 8], [45, 13, 37, 30, 51], [4, 42, 40, 19, 21], [22, 29, 42, 27, 38], [51, 34, 7, 29, 39]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 12, 27, 38], [], [], []]
 b := ![[], [12, 9, 8, 38, 18], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 5
  hpos := by decide
  P := [11, 0, 46, 9, 45, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-99582619232, -127879513954, -14015243680, 66227274342, 74613830572]
  a := ![-6, 19, 16, 20, 31]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1878917344, -2412821018, -264438560, 1249571214, 1407808124]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-436, 3412, 2340, -2180, 6081]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-436, 3412, 2340, -2180, 6081]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![28, 48, 1, 0, 0], ![13, 41, 0, 1, 0], ![36, 15, 0, 0, 1]] where
  M :=![![![-436, 3412, 2340, -2180, 6081], ![-7802, -32861, 14626, 320, -25242], ![24922, 66837, -57783, 14946, 26202], ![-37247, -50559, 100672, -42997, 31257], ![10477, -23144, -39158, 27742, -62128]]]
  hmulB := by decide  
  f := ![![![-4453686, 981888, 261854, -212118, -831135]], ![![2086506, -460393, -122730, 99472, 389562]], ![![-424406, 93245, 24907, -20134, -79050]], ![![452881, -100118, -26668, 21635, 84642]], ![![-2214745, 488183, 130202, -105460, -413266]]]
  g := ![![![-4348, -1877, 2340, -2180, 6081], ![8258, -6261, 14626, 320, -25242], ![8564, 31095, -57783, 14946, 26202], ![-58006, -60827, 100672, -42997, 31257], ![50557, 27982, -39158, 27742, -62128]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [21, 52, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [7, 58], [0, 1]]
 g := ![![[39, 45], [51, 22], [28], [29, 17], [7, 1]], ![[0, 14], [28, 37], [28], [30, 42], [14, 58]]]
 h' := ![![[7, 58], [50, 35], [9, 50], [40, 38], [30, 28], [0, 1]], ![[0, 1], [0, 24], [5, 9], [11, 21], [49, 31], [7, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49]]
 b := ![[], [47, 54]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [21, 52, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![264, 600, -803, 260, 302]
  a := ![-2, -3, 3, -4, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![144, 406, -803, 260, 302]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, -7, -2, 2, 6]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![29, -7, -2, 2, 6]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![51, 30, 1, 0, 0], ![4, 11, 0, 1, 0], ![50, 15, 0, 0, 1]] where
  M :=![![![29, -7, -2, 2, 6], ![-16, 1, 2, 0, 0], ![0, -7, 1, 2, 0], ![6, 2, -6, 3, 6], ![10, -5, 4, -2, 1]]]
  hmulB := by decide  
  f := ![![![7, 3, -4, -6, -6]], ![![24, 21, -18, -20, -24]], ![![19, 14, -13, -16, -18]], ![![6, 5, -4, -5, -6]], ![![12, 8, -8, -10, -11]]]
  g := ![![![-3, -1, -2, 2, 6], ![-2, -1, 2, 0, 0], ![-1, -1, 1, 2, 0], ![0, 1, -6, 3, 6], ![-4, -2, 4, -2, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P1 : CertificateIrreducibleZModOfList' 59 2 2 5 [35, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [48, 58], [0, 1]]
 g := ![![[2, 27], [7, 27], [26], [27, 21], [48, 1]], ![[0, 32], [5, 32], [26], [32, 38], [37, 58]]]
 h' := ![![[48, 58], [50, 26], [35, 33], [58, 47], [31, 27], [0, 1]], ![[0, 1], [0, 33], [26, 26], [13, 12], [29, 32], [48, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53]]
 b := ![[], [13, 56]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N1 : CertifiedPrimeIdeal' SI59N1 59 where
  n := 2
  hpos := by decide
  P := [35, 11, 1]
  hirr := P59P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1079, -2957, -4478, 5948, -2742]
  a := ![-10, 9, 20, 5, 33]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![5773, 1815, -4478, 5948, -2742]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N1 B_one_repr
lemma NI59N1 : Nat.card (O ⧸ I59N1) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-128440, 28309, 7576, -6092, -23943]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![-128440, 28309, 7576, -6092, -23943]] 
 ![![59, 0, 0, 0, 0], ![21, 1, 0, 0, 0], ![45, 0, 1, 0, 0], ![48, 0, 0, 1, 0], ![10, 0, 0, 0, 1]] where
  M :=![![![-128440, 28309, 7576, -6092, -23943], ![60070, -13333, -3452, 2968, 11334], ![-14302, 2942, 969, -484, -2430], ![-27121, 5591, 1754, -999, -4689], ![-47133, 10383, 2736, -2274, -8822]]]
  hmulB := by decide  
  f := ![![![-19506, -44681, 47440, -14894, -9615]], ![![-6112, -15120, 14540, -4198, -4611]], ![![-14792, -30761, 36881, -12602, -2835]], ![![-19541, -48839, 46342, -13213, -15453]], ![![411, 1643, -796, 20, 1204]]]
  g := ![![![-9017, 28309, 7576, -6092, -23943], ![4061, -13333, -3452, 2968, 11334], ![-1223, 2942, 969, -484, -2430], ![-2180, 5591, 1754, -999, -4689], ![-3236, 10383, 2736, -2274, -8822]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-436, 3412, 2340, -2180, 6081]] ![![29, -7, -2, 2, 6]]
  ![![-19506, -44681, 47440, -14894, -9615]] where
 M := ![![![-19506, -44681, 47440, -14894, -9615]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![-19506, -44681, 47440, -14894, -9615]] ![![-128440, 28309, 7576, -6092, -23943]]
  ![![59, 0, 0, 0, 0]] where
 M := ![![![59, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1, I59N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
    exact isPrimeI59N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0 ⊙ MulI59N1)
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


def P61P0 : CertificateIrreducibleZModOfList' 61 5 2 5 [3, 0, 37, 20, 52, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [28, 11, 31, 10, 1], [19, 0, 42, 4, 7], [47, 21, 2, 57, 56], [37, 28, 47, 51, 58], [0, 1]]
 g := ![![[11, 21, 13, 44, 39], [55, 26, 18, 12], [48, 18, 7, 47, 58], [0, 9, 1], []], ![[51, 6, 2, 59, 4, 23, 18, 41], [55, 18, 9, 42], [57, 2, 36, 1, 50, 53, 28, 57], [32, 29, 45, 26, 34, 27, 17, 34], [9, 23, 35, 34, 52, 53, 39, 1]], ![[22, 24, 47, 43, 40, 34, 47, 8], [53, 27, 3, 12], [47, 42, 49, 29, 29, 2, 16, 43], [11, 2, 1, 20, 47, 51, 54, 10], [14, 4, 28, 49, 2, 29, 15, 38]], ![[7, 57, 20, 47, 17, 4, 55, 48], [21, 0, 28, 58], [57, 13, 24, 52, 8, 43, 59, 16], [34, 34, 52, 25, 58, 16, 24, 4], [36, 31, 4, 41, 6, 16, 39, 58]], ![[37, 7, 26, 32, 35, 41, 23, 48], [24, 16, 36, 47], [44, 8, 52, 21, 53, 54, 27, 22], [51, 37, 43, 11, 21, 22, 5, 52], [31, 18, 48, 46, 11, 13, 36, 34]]]
 h' := ![![[28, 11, 31, 10, 1], [14, 41, 46, 55, 51], [39, 7, 33, 60, 45], [0, 34, 58, 33, 27], [0, 0, 0, 1], [0, 1]], ![[19, 0, 42, 4, 7], [38, 27, 59, 6, 23], [52, 26, 18, 55, 46], [44, 29, 9, 19, 22], [26, 0, 44, 59, 20], [28, 11, 31, 10, 1]], ![[47, 21, 2, 57, 56], [12, 60, 11, 10, 55], [54, 3, 16, 9, 45], [33, 2, 11, 8, 23], [46, 49, 49, 36, 17], [19, 0, 42, 4, 7]], ![[37, 28, 47, 51, 58], [12, 38, 34, 52, 37], [21, 59, 43, 34, 34], [42, 6, 13, 24, 3], [15, 55, 37, 49, 32], [47, 21, 2, 57, 56]], ![[0, 1], [8, 17, 33, 60, 17], [43, 27, 12, 25, 13], [38, 51, 31, 38, 47], [52, 18, 53, 38, 53], [37, 28, 47, 51, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 20, 51, 16], [], [], []]
 b := ![[], [14, 19, 37, 9, 45], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 5
  hpos := by decide
  P := [3, 0, 37, 20, 52, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1874995796, -16015001, 4536365406, -2553963006, 5181408381]
  a := ![-6, 7, 9, 6, 19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-30737636, -262541, 74366646, -41868246, 84941121]
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



lemma PB434I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB434I1 : PrimesBelowBoundCertificateInterval O 23 61 434 where
  m := 9
  g := ![2, 2, 4, 2, 1, 4, 1, 3, 1]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB434I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1]
    · exact ![I31N0, I31N1]
    · exact ![I37N0, I37N1, I37N2, I37N3]
    · exact ![I41N0, I41N1]
    · exact ![I43N0]
    · exact ![I47N0, I47N1, I47N2, I47N3]
    · exact ![I53N0]
    · exact ![I59N0, I59N1, I59N2]
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
    · exact ![707281, 29]
    · exact ![923521, 31]
    · exact ![1369, 37, 37, 37]
    · exact ![2825761, 41]
    · exact ![147008443]
    · exact ![2209, 47, 47, 47]
    · exact ![418195493]
    · exact ![3481, 3481, 59]
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
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
      exact NI37N2
      exact NI37N3
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
      exact NI47N2
      exact NI47N3
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
      exact NI59N2
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
  β := ![I29N1, I31N1, I37N1, I37N2, I37N3, I41N1, I47N1, I47N2, I47N3, I59N2]
  Il := ![[I29N1], [I31N1], [I37N1, I37N2, I37N3], [I41N1], [], [I47N1, I47N2, I47N3], [], [I59N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
