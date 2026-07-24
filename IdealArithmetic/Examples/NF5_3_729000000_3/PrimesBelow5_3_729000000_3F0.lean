
import IdealArithmetic.Examples.NF5_3_729000000_3.RI5_3_729000000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-294, -282, 473, 100, -310]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![-294, -282, 473, 100, -310]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-294, -282, 473, 100, -310], ![1240, 999, -2424, 1056, -20], ![40, 484, 939, -3470, 3148], ![-6916, -6628, 11140, 2307, -7252], ![2116, 1348, -4940, 4570, -2521]]]
  hmulB := by decide  
  f := ![![![-27407, 15386, -1035, 2402, -4954]], ![![9908, -6865, 524, -960, 2252]], ![![-4504, 2004, -109, 358, -628]], ![![-3698, 2112, -142, 327, -680]], ![![-4082, 2688, -198, 386, -877]]]
  g := ![![![-147, -282, 473, 100, -310], ![620, 999, -2424, 1056, -20], ![20, 484, 939, -3470, 3148], ![-3458, -6628, 11140, 2307, -7252], ![1058, 1348, -4940, 4570, -2521]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 22, -157, -35, -109]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![109, 22, -157, -35, -109]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![109, 22, -157, -35, -109], ![436, 100, -610, -135, -428], ![856, 206, -1184, -261, -833], ![1448, 358, -1988, -439, -1402], ![1272, 317, -1742, -384, -1231]]]
  hmulB := by decide  
  f := ![![![27534, -16591, 1170, -2493, 5378]], ![![-10756, 6481, -457, 974, -2101]], ![![17969, -10827, 763, -1627, 3510]], ![![3736, -2252, 160, -339, 730]], ![![4344, -2618, 185, -393, 848]]]
  g := ![![![133, 22, -157, -35, -109], ![523, 100, -610, -135, -428], ![1020, 206, -1184, -261, -833], ![1718, 358, -1988, -439, -1402], ![1507, 317, -1742, -384, -1231]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-65, -73, 10, -2, 27]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![-65, -73, 10, -2, 27]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-65, -73, 10, -2, 27], ![-108, -113, 16, -3, 42], ![-84, -91, 13, -2, 33], ![-12, -14, 0, 0, 6], ![28, 29, -4, 0, -10]]]
  hmulB := by decide  
  f := ![![![50, 12, -68, -15, -48]], ![![96, 24, -132, -29, -93]], ![![211, 52, -289, -64, -204]], ![![312, 77, -428, -94, -303]], ![![299, 74, -410, -90, -289]]]
  g := ![![![-51, -73, 10, -2, 27], ![-83, -113, 16, -3, 42], ![-65, -91, 13, -2, 33], ![-9, -14, 0, 0, 6], ![21, 29, -4, 0, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![-294, -282, 473, 100, -310]] ![![109, 22, -157, -35, -109]]
  ![![370, 300, -634, 47, 143]] where
 M := ![![![370, 300, -634, 47, 143]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![370, 300, -634, 47, 143]] ![![109, 22, -157, -35, -109]]
  ![![-121622, -30307, 167024, 36479, 117465]] where
 M := ![![![-121622, -30307, 167024, 36479, 117465]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![-121622, -30307, 167024, 36479, 117465]] ![![-65, -73, 10, -2, 27]]
  ![![-158, -308, 320, 117, -672]] where
 M := ![![![-158, -308, 320, 117, -672]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![-158, -308, 320, 117, -672]] ![![-65, -73, 10, -2, 27]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![-3566, -3908, 340, 600, 780]]]
 hmul := by decide  
 g := ![![![![-1783, -1954, 170, 300, 390]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2348275, -1414972, 99770, -212614, 458662]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![2348275, -1414972, 99770, -212614, 458662]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![2348275, -1414972, 99770, -212614, 458662], ![-1834648, 1105493, -77972, 166106, -358360], ![716720, -431844, 30413, -64898, 139958], ![637408, -384036, 27016, -57721, 124444], ![741056, -446494, 31428, -67104, 144695]]]
  hmulB := by decide  
  f := ![![![-687, -408, 1670, -1714, 1026]], ![![-1368, -1499, 1780, 1914, -2744]], ![![5488, 4864, -9731, 1238, 2998]], ![![-5312, -3132, 12968, -13425, 8084]], ![![-6933, -6574, 11326, 1766, -6779]]]
  g := ![![![629871, -1414972, 99770, -212614, 458662], ![-492096, 1105493, -77972, 166106, -358360], ![192254, -431844, 30413, -64898, 139958], ![170988, -384036, 27016, -57721, 124444], ![198787, -446494, 31428, -67104, 144695]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![55, 43, -6, 0, -16]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![55, 43, -6, 0, -16]] 
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![55, 43, -6, 0, -16], ![64, 81, -10, 4, -32], ![64, 63, -15, 2, -20], ![8, 6, 8, -9, 2], ![-20, -26, 10, 1, 3]]]
  hmulB := by decide  
  f := ![![![-9195, -2279, 12616, 2780, 8904]], ![![-14937, -3702, 20494, 4516, 14464]], ![![-26057, -6458, 35751, 7878, 25232]], ![![-44722, -11084, 61360, 13521, 43306]], ![![-33820, -8382, 46402, 10225, 32749]]]
  g := ![![![6, 43, -6, 0, -16], ![-5, 81, -10, 4, -32], ![4, 63, -15, 2, -20], ![4, 6, 8, -9, 2], ![-2, -26, 10, 1, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![2348275, -1414972, 99770, -212614, 458662]] ![![2348275, -1414972, 99770, -212614, 458662]]
  ![![8386250542441, -5053208491300, 356320748056, -759292115496, 1638005045104]] where
 M := ![![![8386250542441, -5053208491300, 356320748056, -759292115496, 1638005045104]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![8386250542441, -5053208491300, 356320748056, -759292115496, 1638005045104]] ![![55, 43, -6, 0, -16]]
  ![![121808526440591, -73396791208489, 5175483964586, -11028558384520, 23791678985744]] where
 M := ![![![121808526440591, -73396791208489, 5175483964586, -11028558384520, 23791678985744]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![121808526440591, -73396791208489, 5175483964586, -11028558384520, 23791678985744]] ![![55, 43, -6, 0, -16]]
  ![![1769243243831673, -1066072965109742, 75172816753834, -160187492458360, 345569136518664]] where
 M := ![![![1769243243831673, -1066072965109742, 75172816753834, -160187492458360, 345569136518664]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N3 : IdealMulLeCertificate' Table 
  ![![1769243243831673, -1066072965109742, 75172816753834, -160187492458360, 345569136518664]] ![![55, 43, -6, 0, -16]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![25697886245923743, -15484485737871045, 1091869362319632, -2326689658287396, 5019319071767568]]]
 hmul := by decide  
 g := ![![![![8565962081974581, -5161495245957015, 363956454106544, -775563219429132, 1673106357255856]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-101, -12, 4, 4, 6]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![-101, -12, 4, 4, 6]] 
 ![![5, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![-101, -12, 4, 4, 6], ![-24, -101, 12, -6, 36], ![-72, -48, 7, 0, 18], ![-24, 0, 0, 1, 0], ![0, 30, -4, 2, -11]]]
  hmulB := by decide  
  f := ![![![-1, 0, 4, -8, 6]], ![![-5, -5, 8, 2, -6]], ![![14, 12, -25, 4, 6]], ![![-5, 0, 20, -39, 30]], ![![-20, -18, 36, -6, -11]]]
  g := ![![![-25, -12, 4, 4, 6], ![-17, -101, 12, -6, 36], ![-22, -48, 7, 0, 18], ![-5, 0, 0, 1, 0], ![4, 30, -4, 2, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![-101, -12, 4, 4, 6]] ![![-101, -12, 4, 4, 6]]
  ![![10105, 2412, -544, -316, -1032]] where
 M := ![![![10105, 2412, -544, -316, -1032]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![10105, 2412, -544, -316, -1032]] ![![-101, -12, 4, 4, 6]]
  ![![-1031741, -369720, 69684, 23568, 149022]] where
 M := ![![![-1031741, -369720, 69684, 23568, 149022]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![-1031741, -369720, 69684, 23568, 149022]] ![![-101, -12, 4, 4, 6]]
  ![![107496241, 50848440, -8671904, -1587032, -19885296]] where
 M := ![![![107496241, 50848440, -8671904, -1587032, -19885296]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![107496241, 50848440, -8671904, -1587032, -19885296]] ![![-101, -12, 4, 4, 6]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![-11415017045, -6605954820, 1059004100, 83536700, 2538165270]]]
 hmul := by decide  
 g := ![![![![-2283003409, -1321190964, 211800820, 16707340, 507633054]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1167, -398, 1448, 311, 1060]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![-1167, -398, 1448, 311, 1060]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![3, 5, 2, 1, 1]] where
  M :=![![![-1167, -398, 1448, 311, 1060], ![-4240, -1217, 5564, 1214, 3986], ![-7972, -2110, 10741, 2357, 7628], ![-13136, -3278, 17992, 3963, 12706], ![-11436, -2792, 15756, 3475, 11105]]]
  hmulB := by decide  
  f := ![![![-17, -20, 24, 23, -34]], ![![136, 121, -244, 36, 70]], ![![-140, -88, 331, -315, 178]], ![![-424, -458, 568, 539, -802]], ![![39, 27, -86, 67, -31]]]
  g := ![![![-621, -814, -96, -107, 1060], ![-2314, -3021, -344, -396, 3986], ![-4408, -5750, -645, -753, 7628], ![-7322, -9544, -1060, -1249, 12706], ![-6393, -8331, -922, -1090, 11105]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 4 2 2 [2, 6, 6, 5, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 3, 0, 3], [2, 2, 4, 5], [5, 1, 3, 6], [0, 1]]
 g := ![![[6, 5, 2, 1], []], ![[3, 3, 5, 2, 0, 3], [5, 3, 0, 6, 5, 6]], ![[2, 6, 3, 4, 6, 3], [1, 4, 5, 5, 4, 6]], ![[6, 4, 5, 0, 0, 6], [0, 4, 1, 3, 0, 6]]]
 h' := ![![[2, 3, 0, 3], [0, 0, 0, 1], [0, 1]], ![[2, 2, 4, 5], [5, 0, 6, 1], [2, 3, 0, 3]], ![[5, 1, 3, 6], [6, 3, 4, 4], [2, 2, 4, 5]], ![[0, 1], [6, 4, 4, 1], [5, 1, 3, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [2, 6], []]
 b := ![[], [], [2, 1, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 4
  hpos := by decide
  P := [2, 6, 6, 5, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![61648638594, 60773066062, -165129408390, 174125320550, -34950585230]
  a := ![3, -61, 2, -69, 11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![23785770612, 33646570316, -13604033990, 29867986540, -34950585230]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 2401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17, -20, 24, 23, -34]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![-17, -20, 24, 23, -34]] 
 ![![7, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![-17, -20, 24, 23, -34], ![136, 121, -244, 36, 70], ![-140, -88, 331, -315, 178], ![-424, -458, 568, 539, -802], ![348, 278, -684, 311, -19]]]
  hmulB := by decide  
  f := ![![![-1167, -398, 1448, 311, 1060]], ![![-1606, -515, 2036, 440, 1478]], ![![-1639, -472, 2155, 470, 1544]], ![![-2210, -582, 2984, 655, 2118]], ![![-2634, -740, 3492, 763, 2495]]]
  g := ![![![27, -20, 24, 23, -34], ![-50, 121, -244, 36, 70], ![-149, -88, 331, -315, 178], ![622, -458, 568, 539, -802], ![32, 278, -684, 311, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![-1167, -398, 1448, 311, 1060]] ![![-17, -20, 24, 23, -34]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![21, 1, -46, 71, -52]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![21, 1, -46, 71, -52]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![7, 4, 3, 9, 1]] where
  M :=![![![21, 1, -46, 71, -52], ![208, 221, -310, -182, 322], ![-644, -555, 1187, -289, -224], ![344, 96, -1072, 1679, -1252], ![880, 814, -1474, -88, 737]]]
  hmulB := by decide  
  f := ![![![439, 117, -588, -129, -418]], ![![1672, 429, -2274, -500, -1610]], ![![3220, 809, -4401, -969, -3110]], ![![5384, 1336, -7384, -1627, -5212]], ![![6599, 1650, -9031, -1989, -6379]]]
  g := ![![![35, 19, 10, 49, -52], ![-186, -97, -116, -280, 322], ![84, 31, 169, 157, -224], ![828, 464, 244, 1177, -1252], ![-389, -194, -335, -611, 737]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 4 2 3 [10, 7, 3, 2, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 10, 9], [6, 5, 8, 8], [5, 6, 5, 3], [0, 1]]
 g := ![![[9, 3, 7, 1], [9, 1], []], ![[5, 1, 5, 2, 1], [0, 0, 1, 0, 1], [4]], ![[6, 7, 1, 6, 8, 2], [8, 2, 3, 8], [7, 0, 9]], ![[10, 9, 10, 2, 6, 1], [5, 5, 2, 2, 1, 4], [10, 1, 9]]]
 h' := ![![[9, 10, 9], [9, 4, 10, 1], [0, 0, 1], [0, 1]], ![[6, 5, 8, 8], [4, 0, 4, 7], [8, 9, 8, 7], [9, 10, 9]], ![[5, 6, 5, 3], [3, 6, 7, 5], [10, 0, 10], [6, 5, 8, 8]], ![[0, 1], [3, 1, 1, 9], [2, 2, 3, 4], [5, 6, 5, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [5, 6], []]
 b := ![[], [], [1, 0, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 4
  hpos := by decide
  P := [10, 7, 3, 2, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-18208921, -7416228, 26552043, 3870177, 10333404]
  a := ![1, -6, -1, -3, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-8231159, -4431804, -404379, -8102769, 10333404]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 14641 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![439, 117, -588, -129, -418]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![439, 117, -588, -129, -418]] 
 ![![11, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![439, 117, -588, -129, -418], ![1672, 429, -2274, -500, -1610], ![3220, 809, -4401, -969, -3110], ![5384, 1336, -7384, -1627, -5212], ![4712, 1164, -6470, -1426, -4565]]]
  hmulB := by decide  
  f := ![![![21, 1, -46, 71, -52]], ![![38, 21, -70, 48, -18]], ![![-49, -50, 87, 6, -44]], ![![37, 9, -110, 172, -128]], ![![80, 74, -134, -8, 67]]]
  g := ![![![236, 117, -588, -129, -418], ![932, 429, -2274, -500, -1610], ![1822, 809, -4401, -969, -3110], ![3075, 1336, -7384, -1627, -5212], ![2700, 1164, -6470, -1426, -4565]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![21, 1, -46, 71, -52]] ![![439, 117, -588, -129, -418]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 7, -10, -2, 6]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![7, 7, -10, -2, 6]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![7, 5, 6, 1, 0], ![10, 5, 9, 0, 1]] where
  M :=![![![7, 7, -10, -2, 6], ![-24, -19, 50, -22, 0], ![0, -9, -19, 72, -66], ![144, 138, -232, -47, 150], ![-44, -28, 102, -95, 53]]]
  hmulB := by decide  
  f := ![![![-53, 31, 4, 6, -6]], ![![24, -25, 26, 2, 24]], ![![-48, 3, 47, 12, 30]], ![![-47, 8, 40, 11, 24]], ![![-70, 16, 51, 15, 29]]]
  g := ![![![-3, -1, -4, -2, 6], ![10, 7, 14, -22, 0], ![12, -3, 11, 72, -66], ![-79, -29, -100, -47, 150], ![7, 14, 15, -95, 53]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [8, 11, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 7, 6], [10, 5, 7], [0, 1]]
 g := ![![[8, 12, 4], [10, 4], [1]], ![[2, 8, 5, 6], [7, 4], [8, 7, 12, 8]], ![[11, 7, 8, 11], [], [3, 9, 10, 5]]]
 h' := ![![[1, 7, 6], [10, 8, 11], [5, 2, 11], [0, 1]], ![[10, 5, 7], [0, 10, 12], [2, 7, 2], [1, 7, 6]], ![[0, 1], [1, 8, 3], [1, 4], [10, 5, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 10], []]
 b := ![[], [5, 6, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [8, 11, 2, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7536858, -2721794, 11487162, -124996, 6141290]
  a := ![1, 26, 4, 10, 23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5236522, -2523328, -3310344, -124996, 6141290]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 2197 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9, -3, 14, 3, 10]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![-9, -3, 14, 3, 10]] 
 ![![13, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![-9, -3, 14, 3, 10], ![-40, -9, 54, 12, 38], ![-76, -19, 105, 23, 74], ![-128, -32, 176, 39, 124], ![-112, -28, 154, 34, 109]]]
  hmulB := by decide  
  f := ![![![19, 11, -4, 1, -4]], ![![10, 7, -2, 0, -2]], ![![12, 7, -1, 1, -4]], ![![20, 12, -8, 3, -4]], ![![5, 3, -2, -1, 1]]]
  g := ![![![-13, -3, 14, 3, 10], ![-52, -9, 54, 12, 38], ![-100, -19, 105, 23, 74], ![-168, -32, 176, 39, 124], ![-147, -28, 154, 34, 109]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1

def I13N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-27, 24, -2, 3, -8]] i)))

def SI13N2: IdealEqSpanCertificate' Table ![![-27, 24, -2, 3, -8]] 
 ![![13, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![12, 0, 0, 0, 1]] where
  M :=![![![-27, 24, -2, 3, -8], ![32, -7, 0, -2, 2], ![-4, 12, -1, 1, -4], ![-8, 6, 0, 1, -2], ![-12, 4, 0, 1, -1]]]
  hmulB := by decide  
  f := ![![![1, 2, -2, 1, 2]], ![![0, 1, 0, 0, 2]], ![![-1, 0, 1, 2, 0]], ![![3, 4, -6, 2, 4]], ![![0, 2, 0, -1, 5]]]
  g := ![![![-10, 24, -2, 3, -8], ![6, -7, 0, -2, 2], ![-4, 12, -1, 1, -4], ![-3, 6, 0, 1, -2], ![-3, 4, 0, 1, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N2 : Nat.card (O ⧸ I13N2) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N2)

lemma isPrimeI13N2 : Ideal.IsPrime I13N2 := prime_ideal_of_norm_prime hp13.out _ NI13N2
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![7, 7, -10, -2, 6]] ![![-9, -3, 14, 3, 10]]
  ![![1, 2, -2, 1, 2]] where
 M := ![![![1, 2, -2, 1, 2]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI13N1 : IdealMulLeCertificate' Table 
  ![![1, 2, -2, 1, 2]] ![![-27, 24, -2, 3, -8]]
  ![![13, 0, 0, 0, 0]] where
 M := ![![![13, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 13, -4, 1, -6]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![13, 13, -4, 1, -6]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![10, 14, 1, 0, 0], ![13, 5, 0, 1, 0], ![16, 12, 0, 0, 1]] where
  M :=![![![13, 13, -4, 1, -6], ![24, 23, -10, -4, -6], ![12, 9, 5, -3, -18], ![24, 12, -40, 19, -24], ![16, 8, -30, -8, 5]]]
  hmulB := by decide  
  f := ![![![18125, -10921, 770, -1641, 3540]], ![![-14160, 8533, -602, 1282, -2766]], ![![-674, 407, -29, 61, -132]], ![![9985, -6016, 424, -904, 1950]], ![![7400, -4458, 314, -670, 1445]]]
  g := ![![![8, 8, -4, 1, -6], ![16, 15, -10, -4, -6], ![17, 10, 5, -3, -18], ![33, 45, -40, 19, -24], ![20, 24, -30, -8, 5]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [15, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 16], [0, 1]]
 g := ![![[3, 8], [4], [2], [1]], ![[0, 9], [4], [2], [1]]]
 h' := ![![[6, 16], [4, 5], [8, 2], [2, 6], [0, 1]], ![[0, 1], [0, 12], [3, 15], [4, 11], [6, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [4, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 2
  hpos := by decide
  P := [15, 11, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8347, -7191, 13170, 2740, -6454]
  a := ![-1, -6, -4, 13, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4259, -7519, 13170, 2740, -6454]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, -6, 12, -3, -2]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![-7, -6, 12, -3, -2]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![4, 1, 1, 0, 0], ![13, 10, 0, 1, 0], ![8, 11, 0, 0, 1]] where
  M :=![![![-7, -6, 12, -3, -2], ![8, 3, -24, 32, -22], ![44, 46, -63, -45, 74], ![-152, -130, 280, -71, -50], ![-20, -30, 8, 91, -97]]]
  hmulB := by decide  
  f := ![![![-111, 68, -20, 7, -32]], ![![128, -53, -56, -22, -22]], ![![-16, 15, -15, -1, -14]], ![![-3, 24, -60, -10, -46]], ![![36, 1, -56, -13, -37]]]
  g := ![![![0, 2, 12, -3, -2], ![-8, -3, -24, 32, -22], ![17, -15, -63, -45, 74], ![3, 50, 280, -71, -50], ![-27, 7, 8, 91, -97]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P1 : CertificateIrreducibleZModOfList' 17 2 2 4 [9, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 16], [0, 1]]
 g := ![![[8, 2], [13], [16], [1]], ![[0, 15], [13], [16], [1]]]
 h' := ![![[13, 16], [10, 11], [5, 8], [8, 13], [0, 1]], ![[0, 1], [0, 6], [7, 9], [7, 4], [13, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [7, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N1 : CertifiedPrimeIdeal' SI17N1 17 where
  n := 2
  hpos := by decide
  P := [9, 4, 1]
  hirr := P17P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6295, -7548, 6576, 14572, -17548]
  a := ![0, -2, 4, -26, 22]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4803, 1952, 6576, 14572, -17548]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N1 B_one_repr
lemma NI17N1 : Nat.card (O ⧸ I17N1) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N1

def I17N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-190235, 114627, -8082, 17224, -37156]] i)))

def SI17N2: IdealEqSpanCertificate' Table ![![-190235, 114627, -8082, 17224, -37156]] 
 ![![17, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![14, 0, 0, 1, 0], ![11, 0, 0, 0, 1]] where
  M :=![![![-190235, 114627, -8082, 17224, -37156], ![148624, -89557, 6318, -13456, 29032], ![-58064, 34983, -2461, 5258, -11336], ![-51640, 31110, -2184, 4677, -10078], ![-60036, 36170, -2542, 5437, -11719]]]
  hmulB := by decide  
  f := ![![![-195, -173, 328, -60, -76]], ![![-28, -31, 30, 36, -48]], ![![-43, -26, 93, -114, 80]], ![![-410, -360, 720, -133, -174]], ![![-141, -145, 194, 113, -197]]]
  g := ![![![-24025, 114627, -8082, 17224, -37156], ![18766, -89557, 6318, -13456, 29032], ![-7339, 34983, -2461, 5258, -11336], ![-6532, 31110, -2184, 4677, -10078], ![-7591, 36170, -2542, 5437, -11719]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N2 : Nat.card (O ⧸ I17N2) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N2)

lemma isPrimeI17N2 : Ideal.IsPrime I17N2 := prime_ideal_of_norm_prime hp17.out _ NI17N2
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![13, 13, -4, 1, -6]] ![![-7, -6, 12, -3, -2]]
  ![![-195, -173, 328, -60, -76]] where
 M := ![![![-195, -173, 328, -60, -76]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI17N1 : IdealMulLeCertificate' Table 
  ![![-195, -173, 328, -60, -76]] ![![-190235, 114627, -8082, 17224, -37156]]
  ![![17, 0, 0, 0, 0]] where
 M := ![![![17, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8253, 7642, -13896, -678, 6790]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![8253, 7642, -13896, -678, 6790]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![5, 14, 16, 1, 0], ![13, 13, 7, 0, 1]] where
  M :=![![![8253, 7642, -13896, -678, 6790], ![-27160, -20579, 56024, -33226, 9512], ![-19024, -28306, 7957, 84494, -90166], ![193912, 179416, -326816, -14841, 158560], ![-32016, -13286, 90752, -124290, 87695]]]
  hmulB := by decide  
  f := ![![![488623, -290930, 20360, -43994, 94202]], ![![-376808, 232591, -16648, 34506, -75560]], ![![151120, -86662, 5911, -13374, 27958]], ![![-14831, 17680, -1640, 1957, -5994]], ![![140217, -76761, 5067, -12152, 24651]]]
  g := ![![![-4033, -3744, -2662, -678, 6790], ![806, 16891, 27424, -33226, 9512], ![38456, -2056, -37515, 84494, -90166], ![-94377, -88110, -63120, -14841, 158560], ![-28979, 30881, 77133, -124290, 87695]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 3 2 4 [9, 13, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 1, 2], [7, 17, 17], [0, 1]]
 g := ![![[12, 14, 7], [7, 0, 16], [13, 1], []], ![[18, 2, 4, 10], [18, 3, 0, 18], [1, 4], [18, 4]], ![[11, 5, 9, 17], [10, 0, 14, 17], [16, 1], [3, 4]]]
 h' := ![![[6, 1, 2], [13, 13, 8], [16, 12, 4], [0, 0, 1], [0, 1]], ![[7, 17, 17], [14, 1, 10], [2, 6, 16], [7, 8, 17], [6, 1, 2]], ![[0, 1], [14, 5, 1], [17, 1, 18], [3, 11, 1], [7, 17, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 9], []]
 b := ![[], [1, 6, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 3
  hpos := by decide
  P := [9, 13, 6, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1171671, -1027151, 2334462, -1031807, -189814]
  a := ![13, -6, -3, 8, -19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![339734, 836091, 1061688, -1031807, -189814]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 6859 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-488623, 290930, -20360, 43994, -94202]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![-488623, 290930, -20360, 43994, -94202]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![10, 3, 1, 0, 0], ![8, 6, 0, 1, 0], ![8, 4, 0, 0, 1]] where
  M :=![![![-488623, 290930, -20360, 43994, -94202], ![376808, -232591, 16648, -34506, 75560], ![-151120, 86662, -5911, 13374, -27958], ![-132488, 79112, -5536, 11947, -25616], ![-152688, 93418, -6640, 13926, -30317]]]
  hmulB := by decide  
  f := ![![![-8253, -7642, 13896, 678, -6790]], ![![27160, 20579, -56024, 33226, -9512]], ![![946, 717, -1951, 1156, -330]], ![![-5104, -6162, 5360, 11559, -14208]], ![![3928, 1814, -10720, 13822, -9477]]]
  g := ![![![6139, 24466, -20360, 43994, -94202], ![-6216, -19881, 16648, -34506, 75560], ![1298, 7157, -5911, 13374, -27958], ![1696, 6658, -5536, 11947, -25616], ![2360, 7950, -6640, 13926, -30317]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P1 : CertificateIrreducibleZModOfList' 19 2 2 4 [7, 2, 1] where
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
 g := ![![[3, 11], [2, 1], [4], [1]], ![[0, 8], [0, 18], [4], [1]]]
 h' := ![![[17, 18], [5, 12], [2, 1], [12, 17], [0, 1]], ![[0, 1], [0, 7], [0, 18], [16, 2], [17, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [8, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N1 : CertifiedPrimeIdeal' SI19N1 19 where
  n := 2
  hpos := by decide
  P := [7, 2, 1]
  hirr := P19P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1458, -1467, 2130, 1267, -2131]
  a := ![-1, 0, 2, -8, 11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-834, -365, 2130, 1267, -2131]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N1 B_one_repr
lemma NI19N1 : Nat.card (O ⧸ I19N1) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![8253, 7642, -13896, -678, 6790]] ![![-488623, 290930, -20360, 43994, -94202]]
  ![![19, 0, 0, 0, 0]] where
 M := ![![![-19, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![170691, 42219, -234052, -51585, -165170]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![170691, 42219, -234052, -51585, -165170]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![12, 21, 17, 6, 1]] where
  M :=![![![170691, 42219, -234052, -51585, -165170], ![660680, 163809, -906582, -199764, -639850], ![1279700, 317135, -1755741, -386893, -1239142], ![2147944, 532324, -2947000, -649395, -2079896], ![1882352, 466496, -2582594, -569096, -1822709]]]
  hmulB := by decide  
  f := ![![![-43, -41, 58, -1, -20]], ![![80, 53, -202, 138, -46]], ![![92, 123, -85, -317, 368]], ![![-776, -708, 1328, -21, -560]], ![![-80, -66, 117, -93, 57]]]
  g := ![![![93597, 152643, 111906, 40845, -165170], ![362560, 591333, 433516, 158232, -639850], ![702148, 1145179, 839551, 306433, -1239142], ![1178552, 1922180, 1409184, 514347, -2079896], ![1032820, 1684495, 1234933, 450746, -1822709]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 4 2 4 [3, 8, 0, 14, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 3, 5, 10], [14, 18, 3, 22], [6, 1, 15, 14], [0, 1]]
 g := ![![[19, 15, 5, 1], [14, 12, 0, 6], [9, 1], []], ![[15, 22, 7, 12, 19, 20], [3, 10, 21, 18, 2, 20], [7, 16, 6, 14, 8, 10], [0, 11, 8]], ![[9, 18, 6, 20, 4, 19], [15, 8, 8, 18, 5, 17], [16, 0, 4, 2, 6, 14], [0, 3, 1]], ![[3, 12, 13, 7, 9, 10], [11, 9, 9, 22, 6, 17], [8, 15, 14, 4, 0, 10], [14, 22, 12]]]
 h' := ![![[12, 3, 5, 10], [4, 6, 21, 1], [19, 17, 15, 12], [0, 0, 1], [0, 1]], ![[14, 18, 3, 22], [7, 18, 7, 18], [20, 8, 12, 18], [6, 16, 17, 22], [12, 3, 5, 10]], ![[6, 1, 15, 14], [21, 6, 16, 2], [13, 10, 5, 12], [12, 12, 13, 3], [14, 18, 3, 22]], ![[0, 1], [6, 16, 2, 2], [8, 11, 14, 4], [17, 18, 15, 21], [6, 1, 15, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [19, 0, 2], []]
 b := ![[], [], [19, 17, 11, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 4
  hpos := by decide
  P := [3, 8, 0, 14, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1364328634, -337085193, 3772909653, -5254582809, 4359469875]
  a := ![3, 10, 7, -15, 35]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2333824658, -3995041416, -3058177314, -1365713133, 4359469875]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 279841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 41, -58, 1, 20]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![43, 41, -58, 1, 20]] 
 ![![23, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![14, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![19, 0, 0, 0, 1]] where
  M :=![![![43, 41, -58, 1, 20], ![-80, -53, 202, -138, 46], ![-92, -123, 85, 317, -368], ![776, 708, -1328, 21, 560], ![-88, -18, 286, -490, 379]]]
  hmulB := by decide  
  f := ![![![-170691, -42219, 234052, 51585, 165170]], ![![-88096, -21807, 120826, 26628, 85270]], ![![-159538, -39487, 218803, 48221, 154414]], ![![-160181, -39665, 219716, 48420, 155062]], ![![-222847, -55159, 305634, 67357, 215693]]]
  g := ![![![6, 41, -58, 1, 20], ![-92, -53, 202, -138, 46], ![167, -123, 85, 317, -368], ![125, 708, -1328, 21, 560], ![-293, -18, 286, -490, 379]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![170691, 42219, -234052, -51585, -165170]] ![![43, 41, -58, 1, 20]]
  ![![23, 0, 0, 0, 0]] where
 M := ![![![-23, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC23 : ContainsPrimesAboveP 23 ![I23N0, I23N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 23 (by decide) (𝕀 ⊙ MulI23N0)


lemma PB1321I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB1321I0 : PrimesBelowBoundCertificateInterval O 1 23 1321 where
  m := 9
  g := ![5, 5, 5, 2, 2, 3, 3, 2, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB1321I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N0, I3N1, I3N1, I3N1]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1, I13N2]
    · exact ![I17N0, I17N1, I17N2]
    · exact ![I19N0, I19N1]
    · exact ![I23N0, I23N1]
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
    · exact ![2401, 7]
    · exact ![14641, 11]
    · exact ![2197, 13, 13]
    · exact ![289, 289, 17]
    · exact ![6859, 361]
    · exact ![279841, 23]
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
      exact NI13N2
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
      exact NI17N2
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I5N0, I7N1, I11N1, I13N1, I13N2, I17N0, I17N1, I17N2, I19N1, I23N1]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N0, I3N1, I3N1, I3N1], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N1], [I11N1], [I13N1, I13N2], [I17N0, I17N1, I17N2], [I19N1], [I23N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
