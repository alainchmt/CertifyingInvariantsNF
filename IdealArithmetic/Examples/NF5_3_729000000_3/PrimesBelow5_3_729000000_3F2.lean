
import IdealArithmetic.Examples.NF5_3_729000000_3.RI5_3_729000000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41608379, -25071811, 1768300, -3767172, 8127322]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![41608379, -25071811, 1768300, -3767172, 8127322]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![0, 0, 67, 0, 0], ![0, 0, 0, 67, 0], ![21, 57, 40, 56, 1]] where
  M :=![![![41608379, -25071811, 1768300, -3767172, 8127322], ![-32509288, 19587691, -1379690, 2943622, -6348388], ![12696776, -7652479, 542527, -1149118, 2482478], ![11289688, -6805790, 484800, -1021405, 2209318], ![13126780, -7912320, 562218, -1187827, 2567603]]]
  hmulB := by decide  
  f := ![![![681, 1091, -110, -3628, 3770]], ![![-15080, -14225, 24802, 3266, -14228]], ![![28456, 22355, -56909, 28650, -4430]], ![![16400, 25966, -3336, -84977, 88634]], ![![17355, 22658, -14386, -52533, 60199]]]
  g := ![![![-1926349, -7288495, -4825740, -6849212, 8127322], ![1504580, 5693221, 3769490, 5350050, -6348388], ![-588586, -2226175, -1473979, -2092058, 2482478], ![-523970, -1981148, -1311760, -1861839, 2209318], ![-608849, -2302473, -1524506, -2163785, 2567603]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 4 2 6 [3, 1, 12, 41, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 37, 16, 53], [42, 23, 7, 25], [39, 6, 44, 56], [0, 1]]
 g := ![![[63, 2, 33, 49], [60, 49, 8, 40], [39, 56, 6], [46, 1, 6], [1], []], ![[2, 34, 58, 53, 19, 38], [12, 9, 46, 4, 23, 57], [3, 53, 17], [58, 49, 4], [44, 40, 36], [64, 25, 62]], ![[46, 53, 47, 1, 28, 23], [37, 56, 64, 23, 19, 23], [18, 54, 49], [7, 41, 1], [13, 41, 36], [50, 51, 22]], ![[41, 34, 22, 57, 19, 64], [21, 33, 24, 51, 50, 24], [6], [23, 4, 37], [25, 52, 10], [30, 34, 54]]]
 h' := ![![[12, 37, 16, 53], [21, 16, 36, 60], [42, 33, 12, 24], [5, 24, 38, 41], [64, 66, 55, 26], [0, 0, 1], [0, 1]], ![[42, 23, 7, 25], [2, 54, 28, 48], [40, 39, 13, 21], [7, 0, 54, 33], [28, 24, 3, 2], [19, 12, 37, 6], [12, 37, 16, 53]], ![[39, 6, 44, 56], [64, 17, 49, 33], [23, 20, 23, 34], [55, 14, 1, 60], [64, 43, 41, 1], [6, 54, 65, 6], [42, 23, 7, 25]], ![[0, 1], [20, 47, 21, 60], [3, 42, 19, 55], [17, 29, 41], [32, 1, 35, 38], [24, 1, 31, 55], [39, 6, 44, 56]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [32, 0, 62], []]
 b := ![[], [], [44, 40, 6, 27], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 4
  hpos := by decide
  P := [3, 1, 12, 41, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![59387847, 109932181, -118103867, -8380869, 205414859]
  a := ![0, -8, -3, 2, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-63497376, -173115146, -124398481, -171815119, 205414859]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 20151121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-681, -1091, 110, 3628, -3770]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![-681, -1091, 110, 3628, -3770]] 
 ![![67, 0, 0, 0, 0], ![64, 1, 0, 0, 0], ![29, 0, 1, 0, 0], ![45, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![-681, -1091, 110, 3628, -3770], ![15080, 14225, -24802, -3266, 14228], ![-28456, -22355, 56909, -28650, 4430], ![-16400, -25966, 3336, 84977, -88634], ![48596, 42296, -87910, 16973, 21145]]]
  hmulB := by decide  
  f := ![![![-41608379, 25071811, -1768300, 3767172, -8127322]], ![![-39260104, 23656839, -1668530, 3554558, -7668660]], ![![-18199101, 10966194, -773481, 1647718, -3554848]], ![![-28114429, 16940855, -1194900, 2545435, -5491624]], ![![-3301025, 1989125, -140354, 298861, -644839]]]
  g := ![![![-1171, -1091, 110, 3628, -3770], ![-1496, 14225, -24802, -3266, 14228], ![15209, -22355, 56909, -28650, 4430], ![-27345, -25966, 3336, 84977, -88634], ![-14604, 42296, -87910, 16973, 21145]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![41608379, -25071811, 1768300, -3767172, 8127322]] ![![-681, -1091, 110, 3628, -3770]]
  ![![67, 0, 0, 0, 0]] where
 M := ![![![-67, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![933, 1305, -174, 47, -478]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![933, 1305, -174, 47, -478]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![68, 3, 65, 1, 0], ![64, 65, 58, 0, 1]] where
  M :=![![![933, 1305, -174, 47, -478], ![1912, 1809, -258, 36, -674], ![1348, 1537, -213, 43, -566], ![176, 272, -32, 9, -100], ![-512, -452, 66, -6, 167]]]
  hmulB := by decide  
  f := ![![![67, 17, -92, -21, -64]], ![![256, 61, -350, -78, -254]], ![![508, 129, -701, -145, -488]], ![![552, 140, -761, -160, -530]], ![![720, 179, -990, -212, -699]]]
  g := ![![![399, 454, 345, 47, -478], ![600, 641, 514, 36, -674], ![488, 538, 420, 43, -566], ![84, 95, 73, 9, -100], ![-152, -159, -130, -6, 167]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [60, 51, 31, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [48, 51, 69], [63, 19, 2], [0, 1]]
 g := ![![[56, 8, 18], [1, 35, 30], [67, 45, 2], [16, 27], [40, 1], []], ![[39, 53, 67, 26], [49, 11, 21, 59], [0, 67, 0, 67], [18, 32], [24, 6], [27, 4]], ![[53, 37, 28, 37], [6, 56, 58, 54], [41, 39, 39, 16], [39, 18], [48, 45], [23, 4]]]
 h' := ![![[48, 51, 69], [11, 69, 36], [27, 65, 32], [17, 37, 12], [14, 30, 58], [0, 0, 1], [0, 1]], ![[63, 19, 2], [44, 11, 49], [43, 39, 52], [61, 55, 12], [17, 12, 48], [45, 13, 19], [48, 51, 69]], ![[0, 1], [8, 62, 57], [66, 38, 58], [46, 50, 47], [55, 29, 36], [33, 58, 51], [63, 19, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48, 20], []]
 b := ![[], [48, 16, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [60, 51, 31, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-22117049, -31672203, 82135684, -121813395, 17288009]
  a := ![3, -61, 2, -69, 11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![100771285, -11126093, 98553547, -121813395, 17288009]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 357911 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-67, -17, 92, 21, 64]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-67, -17, 92, 21, 64]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![67, 6, 1, 0, 0], ![24, 69, 0, 1, 0], ![29, 55, 0, 0, 1]] where
  M :=![![![-67, -17, 92, 21, 64], ![-256, -61, 350, 78, 254], ![-508, -129, 701, 145, 488], ![-848, -216, 1160, 273, 796], ![-728, -174, 994, 228, 719]]]
  hmulB := by decide  
  f := ![![![-933, -1305, 174, -47, 478]], ![![-1912, -1809, 258, -36, 674]], ![![-1061, -1406, 189, -48, 516]], ![![-2176, -2203, 310, -51, 818]], ![![-1855, -1928, 270, -47, 715]]]
  g := ![![![-121, -78, 92, 21, 64], ![-464, -303, 350, 78, 254], ![-917, -580, 701, 145, 488], ![-1524, -983, 1160, 273, 796], ![-1319, -865, 994, 228, 719]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P1 : CertificateIrreducibleZModOfList' 71 2 2 6 [41, 65, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 70], [0, 1]]
 g := ![![[57, 6], [23, 16], [29, 3], [64], [36], [1]], ![[22, 65], [48, 55], [47, 68], [64], [36], [1]]]
 h' := ![![[6, 70], [51, 19], [18, 67], [67, 43], [63, 8], [30, 6], [0, 1]], ![[0, 1], [23, 52], [65, 4], [41, 28], [40, 63], [66, 65], [6, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [41, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N1 : CertifiedPrimeIdeal' SI71N1 71 where
  n := 2
  hpos := by decide
  P := [41, 65, 1]
  hirr := P71P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-445, -334, 750, -275, 798]
  a := ![1, -6, -1, -3, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-947, -419, 750, -275, 798]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N1 B_one_repr
lemma NI71N1 : Nat.card (O ⧸ I71N1) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![933, 1305, -174, 47, -478]] ![![-67, -17, 92, 21, 64]]
  ![![71, 0, 0, 0, 0]] where
 M := ![![![-71, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0)
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, -124, 10, -18, 40]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![191, -124, 10, -18, 40]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![3, 51, 4, 1, 0], ![70, 60, 13, 0, 1]] where
  M :=![![![191, -124, 10, -18, 40], ![-160, 85, -8, 16, -28], ![56, -40, 1, -10, 20], ![40, -44, 24, -7, 4], ![64, -36, 0, 2, 5]]]
  hmulB := by decide  
  f := ![![![-9, -4, 10, 2, 8]], ![![-32, -11, 40, 8, 28]], ![![-56, -16, 73, 18, 52]], ![![-27, -9, 34, 7, 24]], ![![-46, -16, 57, 12, 41]]]
  g := ![![![-35, -22, -6, -18, 40], ![24, 13, 4, 16, -28], ![-18, -10, -3, -10, 20], ![-3, 1, 0, -7, 4], ![-4, -6, -1, 2, 5]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [25, 3, 69, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 24, 39], [43, 48, 34], [0, 1]]
 g := ![![[22, 57, 19], [23, 36], [23, 65], [38, 6, 23], [4, 1], []], ![[6, 5, 6, 47], [30, 50], [41, 6], [25, 19, 19, 56], [66, 41], [72, 61]], ![[62, 64, 23, 45], [56, 64], [29, 61], [21, 33, 33, 14], [17, 65], [4, 61]]]
 h' := ![![[34, 24, 39], [36, 60, 26], [10, 4, 67], [72, 27, 24], [46, 36, 13], [0, 0, 1], [0, 1]], ![[43, 48, 34], [5, 66, 11], [68, 20, 14], [61, 3, 15], [52, 31, 57], [13, 37, 48], [34, 24, 39]], ![[0, 1], [56, 20, 36], [54, 49, 65], [66, 43, 34], [22, 6, 3], [70, 36, 24], [43, 48, 34]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14, 30], []]
 b := ![[], [52, 36, 61], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [25, 3, 69, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8131206, -2706927, 12412668, -239847, 7279503]
  a := ![1, 26, 4, 10, 23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7081875, -5852670, -1113171, -239847, 7279503]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 389017 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-717, -843, 804, 1448, -1838]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-717, -843, 804, 1448, -1838]] 
 ![![73, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![24, 0, 1, 0, 0], ![47, 0, 0, 1, 0], ![60, 0, 0, 0, 1]] where
  M :=![![![-717, -843, 804, 1448, -1838], ![7352, 6659, -12714, 550, 5012], ![-10024, -7143, 21695, -15770, 6662], ![-17000, -19926, 19200, 33859, -43154], ![20652, 17176, -39158, 13409, 3419]]]
  hmulB := by decide  
  f := ![![![-59165, -17551, 83774, 18152, 59798]], ![![-7329, -2006, 10172, 2222, 7226]], ![![-25712, -7343, 36129, 7858, 25726]], ![![-48587, -13911, 68346, 14861, 48672]], ![![-57816, -16708, 81482, 17701, 58061]]]
  g := ![![![362, -843, 804, 1448, -1838], ![-649, 6659, -12714, 550, 5012], ![-2103, -7143, 21695, -15770, 6662], ![8489, -19926, 19200, 33859, -43154], ![537, 17176, -39158, 13409, 3419]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1

def I73N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![889, 590, -2022, 1736, -894]] i)))

def SI73N2: IdealEqSpanCertificate' Table ![![889, 590, -2022, 1736, -894]] 
 ![![73, 0, 0, 0, 0], ![60, 1, 0, 0, 0], ![25, 0, 1, 0, 0], ![23, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![889, 590, -2022, 1736, -894], ![3576, 4127, -4184, -6622, 8628], ![-17256, -15554, 30011, -1876, -11238], ![20688, 13676, -47176, 40817, -21180], ![19824, 19434, -30952, -9988, 23821]]]
  hmulB := by decide  
  f := ![![![42097, -26498, 6258, -2996, 11466]], ![![33972, -21513, 5360, -2366, 9492]], ![![14281, -9252, 2613, -940, 4284]], ![![12863, -8586, 2758, -787, 4194]], ![![265, -608, 778, 92, 679]]]
  g := ![![![-315, 590, -2022, 1736, -894], ![58, 4127, -4184, -6622, 8628], ![3015, -15554, 30011, -1876, -11238], ![-7371, 13676, -47176, 40817, -21180], ![-2281, 19434, -30952, -9988, 23821]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N2 : Nat.card (O ⧸ I73N2) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N2)

lemma isPrimeI73N2 : Ideal.IsPrime I73N2 := prime_ideal_of_norm_prime hp73.out _ NI73N2
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![191, -124, 10, -18, 40]] ![![-717, -843, 804, 1448, -1838]]
  ![![-16755, -12451, 35130, -22434, 7606]] where
 M := ![![![-16755, -12451, 35130, -22434, 7606]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI73N1 : IdealMulLeCertificate' Table 
  ![![-16755, -12451, 35130, -22434, 7606]] ![![889, 590, -2022, 1736, -894]]
  ![![73, 0, 0, 0, 0]] where
 M := ![![![-978956499, -766675127, 1963185496, -1004197344, 169095448]]]
 hmul := by decide  
 g := ![![![![-13410363, -10502399, 26892952, -13756128, 2316376]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1, I73N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
    exact isPrimeI73N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0 ⊙ MulI73N1)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-865, -214, 1188, 262, 838]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![-865, -214, 1188, 262, 838]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![43, 58, 30, 1, 0], ![32, 18, 19, 0, 1]] where
  M :=![![![-865, -214, 1188, 262, 838], ![-3352, -829, 4600, 1014, 3248], ![-6496, -1610, 8915, 1962, 6290], ![-10904, -2704, 14960, 3301, 10552], ![-9552, -2366, 13104, 2890, 9253]]]
  hmulB := by decide  
  f := ![![![177, -82, 4, -14, 26]], ![![-104, 101, -8, 10, -32]], ![![64, -14, 5, -2, -2]], ![![45, 24, -2, -1, -10]], ![![64, -14, 1, -4, 3]]]
  g := ![![![-493, -386, -286, 262, 838], ![-1910, -1495, -1108, 1014, 3248], ![-3698, -2894, -2145, 1962, 6290], ![-6209, -4862, -3602, 3301, 10552], ![-5442, -4260, -3157, 2890, 9253]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [60, 58, 55, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 31, 72], [7, 47, 7], [0, 1]]
 g := ![![[30, 25, 8], [31, 31, 73], [18, 17, 1], [47, 58, 40], [24, 1], []], ![[26, 34, 63, 4], [30, 55, 52, 18], [57, 0, 3, 21], [29, 70, 3, 2], [47, 76], [31, 49]], ![[32, 78, 51, 69], [19, 10, 38, 57], [69, 44, 27, 39], [14, 48, 30, 12], [15, 13], [17, 49]]]
 h' := ![![[17, 31, 72], [36, 20, 61], [26, 13, 28], [24, 43, 78], [61, 49, 44], [0, 0, 1], [0, 1]], ![[7, 47, 7], [56, 19, 41], [25, 30, 40], [35, 40, 47], [26, 30, 66], [9, 29, 47], [17, 31, 72]], ![[0, 1], [37, 40, 56], [26, 36, 11], [32, 75, 33], [24, 0, 48], [56, 50, 31], [7, 47, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [72, 37], []]
 b := ![[], [48, 27, 73], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [60, 58, 55, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3842748, -3376103, 7130488, -1841791, -1493010]
  a := ![-1, -6, -4, 13, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1558615, 1649645, 1148752, -1841791, -1493010]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 493039 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-177, 82, -4, 14, -26]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![-177, 82, -4, 14, -26]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![26, 49, 1, 0, 0], ![69, 22, 0, 1, 0], ![43, 68, 0, 0, 1]] where
  M :=![![![-177, 82, -4, 14, -26], ![104, -101, 8, -10, 32], ![-64, 14, -5, 2, 2], ![-56, 16, 16, -3, -8], ![-48, 34, 0, 10, -19]]]
  hmulB := by decide  
  f := ![![![865, 214, -1188, -262, -838]], ![![3352, 829, -4600, -1014, -3248]], ![![2446, 605, -3357, -740, -2370]], ![![1827, 452, -2508, -553, -1770]], ![![3477, 860, -4772, -1052, -3369]]]
  g := ![![![1, 22, -4, 14, -26], ![-10, -31, 8, -10, 32], ![-2, 1, -5, 2, 2], ![1, -2, 16, -3, -8], ![1, 14, 0, 10, -19]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P1 : CertificateIrreducibleZModOfList' 79 2 2 6 [22, 25, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [54, 78], [0, 1]]
 g := ![![[55, 18], [16, 67], [44, 46], [30, 42], [72], [1]], ![[0, 61], [0, 12], [0, 33], [7, 37], [72], [1]]]
 h' := ![![[54, 78], [43, 27], [59, 15], [51, 21], [6, 11], [57, 54], [0, 1]], ![[0, 1], [0, 52], [0, 64], [0, 58], [47, 68], [50, 25], [54, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [46, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N1 : CertifiedPrimeIdeal' SI79N1 79 where
  n := 2
  hpos := by decide
  P := [22, 25, 1]
  hirr := P79P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6282, -7590, 6660, 14026, -17086]
  a := ![0, -2, 4, -26, 22]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5222, 6574, 6660, 14026, -17086]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N1 B_one_repr
lemma NI79N1 : Nat.card (O ⧸ I79N1) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![-865, -214, 1188, 262, 838]] ![![-177, 82, -4, 14, -26]]
  ![![79, 0, 0, 0, 0]] where
 M := ![![![-79, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0)
instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-62635, -15512, 85918, 18934, 60636]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-62635, -15512, 85918, 18934, 60636]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![60, 80, 35, 1, 0], ![67, 64, 45, 0, 1]] where
  M :=![![![-62635, -15512, 85918, 18934, 60636], ![-242544, -60121, 332792, 73332, 234876], ![-469752, -116420, 644507, 142022, 454872], ![-788472, -195412, 1081800, 238383, 763500], ![-690976, -171248, 948032, 208906, 669091]]]
  hmulB := by decide  
  f := ![![![199, 216, -38, 14, -84]], ![![336, 357, -72, -20, -84]], ![![168, 196, 105, -10, -144]], ![![540, 584, -55, -11, -204]], ![![511, 556, -31, -10, -209]]]
  g := ![![![-63389, -65192, -39824, 18934, 60636], ![-245532, -252515, -154256, 73332, 234876], ![-475512, -489036, -298741, 142022, 454872], ![-798144, -820844, -501435, 238383, 763500], ![-699451, -719344, -439431, 208906, 669091]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [42, 72, 64, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 20, 44], [2, 62, 39], [0, 1]]
 g := ![![[49, 48, 1], [57, 52, 16], [7, 40], [8, 30], [40, 19, 1], []], ![[4, 49, 57, 3], [51, 10, 59, 29], [20, 31], [21, 65], [82, 56, 15, 65], [32, 27]], ![[9, 37, 67, 22], [47, 38, 78, 32], [59, 36], [4, 3], [63, 57, 82, 79], [37, 27]]]
 h' := ![![[17, 20, 44], [13, 27, 82], [67, 10, 4], [64, 34, 17], [63, 57, 14], [0, 0, 1], [0, 1]], ![[2, 62, 39], [33, 61, 47], [1, 41, 24], [54, 25, 60], [40, 44, 56], [24, 64, 62], [17, 20, 44]], ![[0, 1], [40, 78, 37], [29, 32, 55], [10, 24, 6], [57, 65, 13], [27, 19, 20], [2, 62, 39]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50, 26], []]
 b := ![[], [23, 1, 56], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [42, 72, 64, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1445037, -1258403, 2789063, -981165, -345969]
  a := ![13, -6, -3, 8, -19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![971142, 1197311, 634921, -981165, -345969]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 571787 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 216, -38, 14, -84]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![199, 216, -38, 14, -84]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![50, 48, 1, 0, 0], ![7, 4, 0, 1, 0], ![74, 8, 0, 0, 1]] where
  M :=![![![199, 216, -38, 14, -84], ![336, 357, -72, -20, -84], ![168, 196, 105, -10, -144], ![120, 92, -200, 197, -132], ![16, 8, -144, -38, 137]]]
  hmulB := by decide  
  f := ![![![-62635, -15512, 85918, 18934, 60636]], ![![-242544, -60121, 332792, 73332, 234876]], ![![-183658, -45516, 251981, 55526, 177840]], ![![-26471, -6560, 36318, 8003, 25632]], ![![-87546, -21688, 120100, 26466, 84761]]]
  g := ![![![99, 32, -38, 14, -84], ![124, 55, -72, -20, -84], ![68, -44, 105, -10, -144], ![223, 120, -200, 197, -132], ![-32, 72, -144, -38, 137]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P1 : CertificateIrreducibleZModOfList' 83 2 2 6 [72, 74, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 82], [0, 1]]
 g := ![![[31, 23], [33, 61], [10], [78], [14, 81], [1]], ![[72, 60], [1, 22], [10], [78], [79, 2], [1]]]
 h' := ![![[9, 82], [31, 40], [63, 71], [6, 33], [71, 59], [11, 9], [0, 1]], ![[0, 1], [59, 43], [38, 12], [54, 50], [21, 24], [9, 74], [9, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [75]]
 b := ![[], [18, 79]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N1 : CertifiedPrimeIdeal' SI83N1 83 where
  n := 2
  hpos := by decide
  P := [72, 74, 1]
  hirr := P83P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1465, -1467, 2274, 691, -1339]
  a := ![-1, 0, 2, -8, 11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-252, -1237, 2274, 691, -1339]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N1 B_one_repr
lemma NI83N1 : Nat.card (O ⧸ I83N1) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-62635, -15512, 85918, 18934, 60636]] ![![199, 216, -38, 14, -84]]
  ![![83, 0, 0, 0, 0]] where
 M := ![![![83, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC83 : ContainsPrimesAboveP 83 ![I83N0, I83N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 83 (by decide) (𝕀 ⊙ MulI83N0)
instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0, 0, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0, 0, 0]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![0, 0, 0, 89, 0], ![0, 0, 0, 0, 89]] where
  M :=![![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![0, 0, 0, 89, 0], ![0, 0, 0, 0, 89]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 5 2 6 [39, 38, 13, 83, 1, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [65, 72, 36, 57, 88], [14, 67, 82, 36, 76], [54, 0, 70, 70, 49], [44, 38, 79, 15, 54], [0, 1]]
 g := ![![[28, 27, 88, 16, 5], [5, 3, 57, 8], [50, 84, 26, 2], [37, 15, 81, 76, 1], [1], []], ![[28, 39, 39, 69, 56, 43, 50, 47], [77, 53, 6, 84], [66, 57, 12, 21], [8, 82, 15, 87, 51, 29, 27, 16], [11, 79, 3, 48, 42, 40, 30, 22], [48, 5, 63, 1]], ![[67, 65, 5, 9, 6, 26, 14, 38], [1, 11, 69, 40], [84, 53, 1, 2], [83, 26, 75, 59, 74, 53, 36, 28], [35, 51, 25, 42, 37, 84, 16, 52], [15, 37, 52, 80]], ![[82, 17, 87, 24, 48, 20, 38, 67], [21, 62, 46, 44], [29, 41, 64, 45], [28, 20, 85, 0, 5, 65, 85, 11], [71, 8, 66, 86, 46, 15, 23, 45], [10, 80, 9, 87]], ![[17, 75, 71, 4, 87, 25, 1, 74], [66, 72, 68, 80], [12, 58, 74, 53], [49, 86, 47, 28, 67, 51, 10, 75], [36, 32, 12, 21, 36, 86, 54, 75], [80, 48, 39, 68]]]
 h' := ![![[65, 72, 36, 57, 88], [63, 88, 68, 31, 19], [13, 46, 41, 75, 39], [70, 64, 0, 3, 64], [50, 51, 76, 6, 88], [0, 0, 1], [0, 1]], ![[14, 67, 82, 36, 76], [13, 82, 14, 43, 65], [41, 76, 3, 60, 23], [37, 83, 72, 44, 56], [2, 63, 8, 76, 47], [39, 43, 7, 60, 44], [65, 72, 36, 57, 88]], ![[54, 0, 70, 70, 49], [71, 48, 25, 19, 32], [33, 55, 45, 15, 60], [4, 19, 31, 48, 64], [86, 76, 15, 71, 13], [56, 41, 41, 12, 21], [14, 67, 82, 36, 76]], ![[44, 38, 79, 15, 54], [2, 70, 47, 54, 70], [51, 20, 5, 20, 69], [84, 75, 21, 72, 57], [25, 61, 50, 61, 24], [34, 60, 34, 86, 30], [54, 0, 70, 70, 49]], ![[0, 1], [86, 68, 24, 31, 81], [41, 70, 84, 8, 76], [81, 26, 54, 11, 26], [56, 16, 29, 53, 6], [62, 34, 6, 20, 83], [44, 38, 79, 15, 54]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [75, 17, 3, 49], [], [], []]
 b := ![[], [18, 55, 73, 86, 49], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 5
  hpos := by decide
  P := [39, 38, 13, 83, 1, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1859580797229, -1951857044670, 2442699027966, 2444873270554, -3404963474374]
  a := ![3, 10, 7, -15, 35]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-20894166261, -21930978030, 27446056494, 27470486186, -38258016566]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 5584059449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def PBC89 : ContainsPrimesAboveP 89 ![I89N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![89, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 89 (by decide) 𝕀

instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0, 0, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0, 0, 0]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![0, 0, 0, 97, 0], ![0, 0, 0, 0, 97]] where
  M :=![![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![0, 0, 0, 97, 0], ![0, 0, 0, 0, 97]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 5 2 6 [83, 33, 0, 12, 31, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [13, 67, 87, 35, 42], [95, 88, 82, 62, 47], [86, 5, 25, 74, 57], [66, 33, 0, 23, 48], [0, 1]]
 g := ![![[91, 15, 30, 66, 22], [72, 71, 17, 44], [69, 34, 19, 73], [57, 67, 96, 53], [66, 1], []], ![[61, 4, 77, 42, 54, 91, 13, 34], [64, 43, 82, 6], [12, 67, 47, 24], [92, 31, 13, 81], [10, 35, 36, 1], [24, 6, 2, 67, 15, 95, 85, 77]], ![[57, 52, 28, 4, 36, 19, 79, 94], [58, 46, 10, 61], [80, 31, 76, 8], [66, 31, 92, 24], [36, 44, 50, 75], [25, 46, 36, 72, 16, 47, 26, 33]], ![[17, 2, 70, 14, 91, 93, 89, 30], [45, 61, 50, 65], [50, 66, 43, 81], [48, 2, 39, 93], [2, 69, 68, 72], [29, 88, 5, 69, 52, 80, 45, 20]], ![[14, 21, 31, 91, 30, 25, 49, 9], [3, 71, 12, 22], [78, 47], [13, 18, 19, 27], [18, 10, 69, 35], [79, 18, 6, 73, 10, 93, 9, 12]]]
 h' := ![![[13, 67, 87, 35, 42], [85, 66, 55, 21, 64], [12, 28, 25, 49, 23], [4, 71, 62, 51, 49], [51, 67, 64, 81, 76], [0, 0, 0, 1], [0, 1]], ![[95, 88, 82, 62, 47], [35, 89, 75, 5, 85], [77, 74, 7, 55, 43], [54, 28, 0, 58, 11], [67, 37, 67, 54, 9], [11, 87, 81, 82, 1], [13, 67, 87, 35, 42]], ![[86, 5, 25, 74, 57], [68, 56, 83, 66, 83], [41, 28, 26, 23, 35], [52, 42, 23, 82, 28], [1, 20, 67, 59, 86], [51, 2, 66, 49, 47], [95, 88, 82, 62, 47]], ![[66, 33, 0, 23, 48], [17, 55, 19, 38, 13], [39, 66, 6, 54, 29], [55, 46, 41, 88, 9], [16, 44, 44, 66, 53], [45, 53, 81, 81, 13], [86, 5, 25, 74, 57]], ![[0, 1], [85, 25, 59, 64, 46], [72, 95, 33, 13, 64], [12, 7, 68, 12], [11, 26, 49, 31, 67], [27, 52, 63, 78, 36], [66, 33, 0, 23, 48]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65, 36, 2, 94], [], [], []]
 b := ![[], [85, 69, 81, 61, 7], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 5
  hpos := by decide
  P := [83, 33, 0, 12, 31, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16228193896, -16822290087, 22254491944, 18320795751, -27504982149]
  a := ![1, 4, 2, -6, 13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-167300968, -173425671, 229427752, 188874183, -283556517]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 8587340257 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def PBC97 : ContainsPrimesAboveP 97 ![I97N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![97, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 97 (by decide) 𝕀

instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-263, 222, -100, 63, -58]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![-263, 222, -100, 63, -58]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![53, 94, 1, 0, 0], ![68, 79, 0, 1, 0], ![41, 54, 0, 0, 1]] where
  M :=![![![-263, 222, -100, 63, -58], ![232, -121, 96, -268, 262], ![-524, -366, 665, 233, -542], ![968, 906, -2040, 837, 26], ![228, 434, -384, -595, 767]]]
  hmulB := by decide  
  f := ![![![115797, 28576, -159060, -35059, -112216]], ![![448864, 111051, -616144, -135786, -434786]], ![![487129, 120482, -668723, -147376, -471876]], ![![443508, 109683, -608856, -134183, -429628]], ![![299661, 74114, -411372, -90660, -290279]]]
  g := ![![![31, 77, -100, 63, -58], ![26, -21, 96, -268, 262], ![-291, -515, 665, 233, -542], ![506, 1239, -2040, 837, 26], ![293, 417, -384, -595, 767]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [24, 39, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [62, 100], [0, 1]]
 g := ![![[90, 80], [87], [15, 97], [22], [21], [62, 1]], ![[0, 21], [87], [70, 4], [22], [21], [23, 100]]]
 h' := ![![[62, 100], [50, 22], [44, 17], [1, 81], [23, 27], [27, 83], [0, 1]], ![[0, 1], [0, 79], [88, 84], [74, 20], [81, 74], [22, 18], [62, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [24, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [24, 39, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-132, -344, 454, 314, -564]
  a := ![4, -1, -1, 3, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-222, -370, 454, 314, -564]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![122615, -73862, 5174, -11107, 23920]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![122615, -73862, 5174, -11107, 23920]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![97, 89, 1, 0, 0], ![53, 6, 0, 1, 0], ![93, 52, 0, 0, 1]] where
  M :=![![![122615, -73862, 5174, -11107, 23920], ![-95680, 57735, -4204, 8642, -18802], ![37604, -22498, 1329, -3445, 7124], ![33592, -19970, 976, -3109, 6190], ![38964, -23240, 1260, -3587, 7285]]]
  hmulB := by decide  
  f := ![![![27, -36, -218, 435, -338]], ![![1352, 1355, -2100, -968, 1934]], ![![1179, 1127, -1989, -456, 1370]], ![![107, 60, -290, 272, -144]], ![![775, 714, -1374, -98, 725]]]
  g := ![![![-19952, -16946, 5174, -11107, 23920], ![15868, 13443, -4204, 8642, -18802], ![-5656, -4857, 1329, -3445, 7124], ![-4673, -4060, 976, -3109, 6190], ![-5650, -4878, 1260, -3587, 7285]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P1 : CertificateIrreducibleZModOfList' 101 2 2 6 [36, 45, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [56, 100], [0, 1]]
 g := ![![[77, 87], [76], [71, 16], [30], [52], [56, 1]], ![[0, 14], [76], [58, 85], [30], [52], [11, 100]]]
 h' := ![![[56, 100], [43, 84], [70, 51], [61, 4], [63, 38], [4, 70], [0, 1]], ![[0, 1], [0, 17], [98, 50], [83, 97], [70, 63], [86, 31], [56, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32]]
 b := ![[], [57, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N1 : CertifiedPrimeIdeal' SI101N1 101 where
  n := 2
  hpos := by decide
  P := [36, 45, 1]
  hirr := P101P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-188928, -116507, 308782, -17242, 27318]
  a := ![7, -46, -24, 25, -119]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-314530, -286289, 308782, -17242, 27318]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N1 B_one_repr
lemma NI101N1 : Nat.card (O ⧸ I101N1) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-116917, 71530, -5042, 10672, -23186]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![-116917, 71530, -5042, 10672, -23186]] 
 ![![101, 0, 0, 0, 0], ![38, 1, 0, 0, 0], ![86, 0, 1, 0, 0], ![64, 0, 0, 1, 0], ![41, 0, 0, 0, 1]] where
  M :=![![![-116917, 71530, -5042, 10672, -23186], ![92744, -54243, 3944, -8242, 17660], ![-35320, 22442, -1263, 3356, -7066], ![-32240, 19252, -728, 3035, -5828], ![-37776, 21958, -968, 3476, -6737]]]
  hmulB := by decide  
  f := ![![![66159, 81858, -65010, -165220, 197998]], ![![17050, 23617, -11076, -62138, 68600]], ![![68122, 78390, -80219, -124376, 162770]], ![![57488, 71052, -56664, -142965, 171508]], ![![3963, 13928, 16430, -79908, 74765]]]
  g := ![![![-21127, 71530, -5042, 10672, -23186], ![16022, -54243, 3944, -8242, 17660], ![-6976, 22442, -1263, 3356, -7066], ![-6500, 19252, -728, 3035, -5828], ![-7279, 21958, -968, 3476, -6737]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![-263, 222, -100, 63, -58]] ![![122615, -73862, 5174, -11107, 23920]]
  ![![-57392721, 34582486, -2438542, 5196344, -11209964]] where
 M := ![![![-57392721, 34582486, -2438542, 5196344, -11209964]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![-57392721, 34582486, -2438542, 5196344, -11209964]] ![![-116917, 71530, -5042, 10672, -23186]]
  ![![101, 0, 0, 0, 0]] where
 M := ![![![10259569615685, -6181993255616, 435915609332, -928902645900, 2003902304274]]]
 hmul := by decide  
 g := ![![![![101579897185, -61207854016, 4315996132, -9197055900, 19840616874]]]]
 hle2 := by decide  


def PBC101 : ContainsPrimesAboveP 101 ![I101N0, I101N1, I101N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
    exact isPrimeI101N1
    exact isPrimeI101N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 101 (by decide) (𝕀 ⊙ MulI101N0 ⊙ MulI101N1)
instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1069, -1017, 1738, 300, -1070]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![-1069, -1017, 1738, 300, -1070]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![80, 66, 28, 1, 0], ![1, 8, 79, 0, 1]] where
  M :=![![![-1069, -1017, 1738, 300, -1070], ![4280, 3409, -8454, 3946, -340], ![680, 2199, 2389, -12230, 11498], ![-25136, -23898, 40920, 6897, -25022], ![6876, 4168, -16530, 16495, -9671]]]
  hmulB := by decide  
  f := ![![![-723, -131, 240, 68, 194]], ![![-776, -735, 902, 150, 796]], ![![-1592, -583, 1653, 354, 1246]], ![![-1512, -736, 1240, 251, 1018]], ![![-1305, -508, 1363, 289, 1035]]]
  g := ![![![-233, -119, 756, 300, -1070], ![-3020, -2469, -894, 3946, -340], ![9394, 6965, -5471, -12230, 11498], ![-5358, -2708, 17714, 6897, -25022], ![-12651, -9778, 2773, 16495, -9671]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [98, 31, 21, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [78, 75, 63], [4, 27, 40], [0, 1]]
 g := ![![[98, 60, 91], [52, 102, 91], [86, 83, 81], [38, 63], [75, 29], [1]], ![[1, 77, 87, 1], [98, 12, 61, 82], [22, 9, 73, 46], [50, 23], [6, 38], [16, 22, 71, 66]], ![[98, 16, 51, 21], [59, 40, 9, 102], [93, 55, 15, 3], [10, 33], [84, 23], [71, 73, 73, 37]]]
 h' := ![![[78, 75, 63], [54, 46, 83], [18, 22, 20], [25, 84, 94], [91, 85, 28], [5, 72, 82], [0, 1]], ![[4, 27, 40], [62, 33, 92], [61, 20, 72], [22, 81, 2], [94, 76, 34], [8, 56, 55], [78, 75, 63]], ![[0, 1], [49, 24, 31], [89, 61, 11], [3, 41, 7], [57, 45, 41], [7, 78, 69], [4, 27, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53, 64], []]
 b := ![[], [80, 59, 84], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [98, 31, 21, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-486173, -1188674, 3398033, -6874261, 1224126]
  a := ![1, -12, -7, 9, -36]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![5322627, 4298248, 962829, -6874261, 1224126]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 1092727 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-723, -131, 240, 68, 194]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![-723, -131, 240, 68, 194]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![98, 75, 1, 0, 0], ![66, 38, 0, 1, 0], ![51, 1, 0, 0, 1]] where
  M :=![![![-723, -131, 240, 68, 194], ![-776, -735, 902, 150, 796], ![-1592, -583, 1653, 354, 1246], ![-2104, -494, 2704, 601, 1910], ![-1716, -256, 2346, 533, 1609]]]
  hmulB := by decide  
  f := ![![![-1069, -1017, 1738, 300, -1070]], ![![4280, 3409, -8454, 3946, -340]], ![![2106, 1536, -4479, 3040, -1154]], ![![650, 374, -1608, 1715, -1054]], ![![-421, -430, 618, 347, -627]]]
  g := ![![![-375, -203, 240, 68, 194], ![-1356, -727, 902, 150, 796], ![-2432, -1352, 1653, 354, 1246], ![-3924, -2214, 2704, 601, 1910], ![-3387, -1923, 2346, 533, 1609]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P1 : CertificateIrreducibleZModOfList' 103 2 2 6 [15, 90, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [13, 102], [0, 1]]
 g := ![![[6, 55], [69, 66], [25, 66], [15], [26], [13, 1]], ![[0, 48], [0, 37], [59, 37], [15], [26], [26, 102]]]
 h' := ![![[13, 102], [98, 40], [37, 13], [36, 90], [40, 18], [11, 51], [0, 1]], ![[0, 1], [0, 63], [0, 90], [73, 13], [68, 85], [56, 52], [13, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [68]]
 b := ![[], [88, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N1 : CertifiedPrimeIdeal' SI103N1 103 where
  n := 2
  hpos := by decide
  P := [15, 90, 1]
  hirr := P103P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1362, 1419, 2352, 841, 5447]
  a := ![3, 9, 2, 7, 11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5487, -2062, 2352, 841, 5447]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N1 B_one_repr
lemma NI103N1 : Nat.card (O ⧸ I103N1) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![-1069, -1017, 1738, 300, -1070]] ![![-723, -131, 240, 68, 194]]
  ![![103, 0, 0, 0, 0]] where
 M := ![![![103, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC103 : ContainsPrimesAboveP 103 ![I103N0, I103N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 103 (by decide) (𝕀 ⊙ MulI103N0)


lemma PB1321I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB1321I2 : PrimesBelowBoundCertificateInterval O 61 103 1321 where
  m := 9
  g := ![2, 2, 3, 2, 2, 1, 1, 3, 2]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB1321I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1, I73N2]
    · exact ![I79N0, I79N1]
    · exact ![I83N0, I83N1]
    · exact ![I89N0]
    · exact ![I97N0]
    · exact ![I101N0, I101N1, I101N2]
    · exact ![I103N0, I103N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC67
    · exact PBC71
    · exact PBC73
    · exact PBC79
    · exact PBC83
    · exact PBC89
    · exact PBC97
    · exact PBC101
    · exact PBC103
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![20151121, 67]
    · exact ![357911, 5041]
    · exact ![389017, 73, 73]
    · exact ![493039, 6241]
    · exact ![571787, 6889]
    · exact ![5584059449]
    · exact ![8587340257]
    · exact ![10201, 10201, 101]
    · exact ![1092727, 10609]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
      exact NI73N2
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
      exact NI101N2
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
  β := ![I67N1, I73N1, I73N2, I101N2]
  Il := ![[I67N1], [], [I73N1, I73N2], [], [], [], [], [I101N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
