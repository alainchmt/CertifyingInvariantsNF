
import IdealArithmetic.Examples.NF5_1_40500000_1.RI5_1_40500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![142181, 40759, -19117, 57428, 82750]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![142181, 40759, -19117, 57428, 82750]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![0, 0, 107, 0, 0], ![0, 0, 0, 107, 0], ![79, 19, 75, 87, 1]] where
  M :=![![![142181, 40759, -19117, 57428, 82750], ![363106, 104024, -48775, 146614, 211174], ![926750, 265845, -124644, 374440, 539390], ![55152, 15785, -7421, 22259, 32148], ![263536, 75618, -35438, 106492, 153335]]]
  hmulB := by decide  
  f := ![![![-177, 29, 61, -62, -146]], ![![-562, 66, 69, 132, -58]], ![![90, -85, -388, 970, 1230]], ![![844, -121, -211, 83, 436]], ![![519, -125, -387, 727, 1101]]]
  g := ![![![-59767, -14313, -58181, -66746, 82750], ![-152520, -36526, -148475, -170332, 211174], ![-389580, -93295, -379242, -435070, 539390], ![-23220, -5561, -22603, -25931, 32148], ![-110747, -26521, -107809, -123679, 153335]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 4 2 6 [84, 85, 53, 19, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [70, 52, 83, 49], [13, 26, 40, 53], [5, 28, 91, 5], [0, 1]]
 g := ![![[17, 7, 46, 29], [53, 30, 106, 11], [104, 18, 39], [79, 47, 72, 64], [94, 88, 1], []], ![[102, 67, 7, 101, 62, 57], [20, 82, 50, 93, 84, 69], [36, 72, 41], [4, 2, 77, 52, 17, 101], [41, 68, 34], [9, 67, 81, 101, 46, 56]], ![[41, 15, 12, 87, 16, 81], [41, 99, 106, 70, 33, 47], [89, 13, 37], [51, 29, 47, 55, 9, 62], [37, 102, 75], [105, 6, 41, 7, 19, 40]], ![[36, 83, 15, 43, 105, 21], [60, 7, 20, 66, 23, 17], [8, 42, 99], [81, 69, 87, 41, 19, 18], [94, 24, 52], [9, 85, 32, 44, 63, 18]]]
 h' := ![![[70, 52, 83, 49], [42, 89, 92, 55], [42, 83, 64, 15], [105, 93, 75, 50], [22, 26, 80, 99], [0, 0, 0, 1], [0, 1]], ![[13, 26, 40, 53], [92, 87, 53, 68], [13, 101, 103, 85], [83, 11, 69, 24], [27, 69, 42, 95], [58, 19, 48, 81], [70, 52, 83, 49]], ![[5, 28, 91, 5], [41, 23, 66, 42], [27, 6, 52, 21], [86, 102, 95, 95], [9, 19, 58, 25], [11, 8, 103, 90], [13, 26, 40, 53]], ![[0, 1], [54, 15, 3, 49], [86, 24, 102, 93], [104, 8, 82, 45], [36, 100, 34, 102], [11, 80, 63, 42], [5, 28, 91, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [3, 89, 22], []]
 b := ![[], [], [63, 99, 40, 44], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 4
  hpos := by decide
  P := [84, 85, 53, 19, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3841366, 4392005, -474437, 4201690, -2883640]
  a := ![-11, -7, 13, -19, -44]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2093142, 553095, 2016809, 2383910, -2883640]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 131079601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![177, -29, -61, 62, 146]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![177, -29, -61, 62, 146]] 
 ![![107, 0, 0, 0, 0], ![56, 1, 0, 0, 0], ![74, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![63, 0, 0, 0, 1]] where
  M :=![![![177, -29, -61, 62, 146], ![562, -66, -69, -132, 58], ![-90, 85, 388, -970, -1230], ![-844, 121, 211, -83, -436], ![-16, 18, 82, -208, -261]]]
  hmulB := by decide  
  f := ![![![-142181, -40759, 19117, -57428, -82750]], ![![-77806, -22304, 10461, -31426, -45282]], ![![-106992, -30673, 14386, -43216, -62270]], ![![-9817, -2814, 1320, -3965, -5714]], ![![-86177, -24705, 11587, -34808, -50155]]]
  g := ![![![-31, -29, -61, 62, 146], ![62, -66, -69, -132, 58], ![474, 85, 388, -970, -1230], ![45, 121, 211, -83, -436], ![101, 18, 82, -208, -261]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![142181, 40759, -19117, 57428, 82750]] ![![177, -29, -61, 62, 146]]
  ![![107, 0, 0, 0, 0]] where
 M := ![![![-107, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-471, -131, 57, -166, -248]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![-471, -131, 57, -166, -248]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![0, 0, 109, 0, 0], ![45, 76, 88, 1, 0], ![61, 38, 38, 0, 1]] where
  M :=![![![-471, -131, 57, -166, -248], ![-1076, -352, 119, -424, -584], ![-2600, -905, 336, -1250, -1640], ![-204, -41, 61, -155, -216], ![-766, -254, 100, -352, -473]]]
  hmulB := by decide  
  f := ![![![-47, 25, -19, 8, 56]], ![![184, -134, 57, -54, -104]], ![![-420, 415, -76, 200, -120]], ![![-231, 252, -30, 127, -144]], ![![-109, 113, -17, 56, -49]]]
  g := ![![![203, 201, 221, -166, -248], ![492, 496, 547, -424, -584], ![1410, 1435, 1584, -1250, -1640], ![183, 183, 201, -155, -216], ![403, 408, 450, -352, -473]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [67, 75, 62, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [75, 30, 96], [81, 78, 13], [0, 1]]
 g := ![![[103, 88, 46], [71, 87], [14, 25, 29], [76, 81, 26], [90, 29], [1]], ![[82, 34, 46, 50], [57, 74], [43, 77, 4, 52], [90, 43, 45, 90], [99, 45], [40, 49, 23, 92]], ![[76, 47, 68, 58], [43, 22], [58, 68, 21, 6], [76, 3, 80, 10], [83, 1], [80, 41, 15, 17]]]
 h' := ![![[75, 30, 96], [35, 97, 41], [43, 89, 95], [31, 107, 62], [94, 49, 74], [42, 34, 47], [0, 1]], ![[81, 78, 13], [16, 86, 84], [42, 24, 40], [94, 104, 66], [50, 87, 12], [90, 93, 63], [75, 30, 96]], ![[0, 1], [88, 35, 93], [35, 105, 83], [2, 7, 90], [27, 82, 23], [47, 91, 108], [81, 78, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [102, 44], []]
 b := ![[], [108, 64, 104], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [67, 75, 62, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-12577307, 1647176, 3339434, -5508830, -16324050]
  a := ![-49, -56, 48, -106, -199]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![11294377, 9547084, 10169086, -5508830, -16324050]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 1295029 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-47, 25, -19, 8, 56]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![-47, 25, -19, 8, 56]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![72, 101, 1, 0, 0], ![14, 34, 0, 1, 0], ![43, 61, 0, 0, 1]] where
  M :=![![![-47, 25, -19, 8, 56], ![184, -134, 57, -54, -104], ![-420, 415, -76, 200, -120], ![-88, 7, -59, -13, 248], ![-46, 114, 28, 68, -245]]]
  hmulB := by decide  
  f := ![![![-471, -131, 57, -166, -248]], ![![-1076, -352, 119, -424, -584]], ![![-1332, -421, 151, -514, -720]], ![![-398, -127, 45, -155, -216]], ![![-795, -251, 90, -306, -429]]]
  g := ![![![-11, -16, -19, 8, 56], ![12, 21, 57, -54, -104], ![68, 79, -76, 200, -120], ![-58, -80, -59, -13, 248], ![69, 91, 28, 68, -245]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P1 : CertificateIrreducibleZModOfList' 109 2 2 6 [73, 81, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [28, 108], [0, 1]]
 g := ![![[25, 3], [5], [68, 74], [72, 71], [88], [28, 1]], ![[0, 106], [5], [69, 35], [98, 38], [88], [56, 108]]]
 h' := ![![[28, 108], [64, 60], [50, 21], [85, 69], [82, 92], [27, 57], [0, 1]], ![[0, 1], [0, 49], [93, 88], [55, 40], [42, 17], [97, 52], [28, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [70]]
 b := ![[], [55, 35]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N1 : CertifiedPrimeIdeal' SI109N1 109 where
  n := 2
  hpos := by decide
  P := [73, 81, 1]
  hirr := P109P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-192, -298, 501, -768, -1625]
  a := ![-4, -4, 5, -9, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![407, 682, 501, -768, -1625]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N1 B_one_repr
lemma NI109N1 : Nat.card (O ⧸ I109N1) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![-471, -131, 57, -166, -248]] ![![-47, 25, -19, 8, 56]]
  ![![109, 0, 0, 0, 0]] where
 M := ![![![109, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0)
instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![33162, 8082, 56011, -165540, -191351]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![33162, 8082, 56011, -165540, -191351]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![85, 80, 1, 0, 0], ![111, 47, 0, 1, 0], ![42, 79, 0, 0, 1]] where
  M :=![![![33162, 8082, 56011, -165540, -191351], ![-905133, 147677, 313351, -319212, -750267], ![-2889225, 342410, 355046, 675340, -302895], ![496766, -117704, -355326, 656675, 1006274], ![-623374, 74164, 78036, 141950, -69995]]]
  hmulB := by decide  
  f := ![![![-24506396, -7024170, 3293803, -9897554, -14258181]], ![![-62569651, -17934935, 8410311, -25270994, -36405889]], ![![-64144915, -18386180, 8621861, -25907020, -37321830]], ![![-50181311, -14383623, 6744904, -20267293, -29197028]], ![![-53254001, -15264565, 7158057, -21508440, -30985326]]]
  g := ![![![191893, 163047, 56011, -165540, -191351], ![348706, 436758, 313351, -319212, -750267], ![-843445, -317465, 355046, 675340, -302895], ![-747389, -726115, -355326, 656675, 1006274], ![-177638, -64697, 78036, 141950, -69995]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [82, 99, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [14, 112], [0, 1]]
 g := ![![[77, 51], [109], [18], [62], [91, 1], [14, 1]], ![[0, 62], [109], [18], [62], [105, 112], [28, 112]]]
 h' := ![![[14, 112], [74, 27], [56, 30], [17, 40], [109, 47], [95, 1], [0, 1]], ![[0, 1], [0, 86], [24, 83], [12, 73], [89, 66], [109, 112], [14, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [29, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [82, 99, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7837, 8919, 440, 8100, -1693]
  a := ![36, 27, -39, 62, 143]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7589, -2418, 440, 8100, -1693]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8, 0, 1, 2, -1]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![-8, 0, 1, 2, -1]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![90, 84, 1, 0, 0], ![35, 61, 0, 1, 0], ![55, 93, 0, 0, 1]] where
  M :=![![![-8, 0, 1, 2, -1], ![1, -1, -7, 14, 19], ![85, -20, -24, 10, 55], ![18, -2, 4, -17, -18], ![16, -4, -6, 2, 15]]]
  hmulB := by decide  
  f := ![![![-18, -8, 5, -8, -19]], ![![-73, -1, -3, -12, -7]], ![![-69, -8, 2, -16, -21]], ![![-45, -3, 0, -9, -10]], ![![-69, -5, 0, -14, -15]]]
  g := ![![![-1, -1, 1, 2, -1], ![-8, -18, -7, 14, 19], ![-10, -33, -24, 10, 55], ![11, 21, 4, -17, -18], ![-3, -9, -6, 2, 15]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P1 : CertificateIrreducibleZModOfList' 113 2 2 6 [112, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [98, 112], [0, 1]]
 g := ![![[98, 112], [112], [112], [1], [], [98, 1]], ![[0, 1], [112], [112], [1], [], [83, 112]]]
 h' := ![![[98, 112], [112, 15], [0, 98], [1, 98], [0, 112], [98], [0, 1]], ![[0, 1], [0, 98], [112, 15], [0, 15], [15, 1], [98], [98, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [74]]
 b := ![[], [108, 37]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N1 : CertifiedPrimeIdeal' SI113N1 113 where
  n := 2
  hpos := by decide
  P := [112, 15, 1]
  hirr := P113P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1681, 877, 2206, 884, -7671]
  a := ![-21, -9, 26, -28, -83]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1688, 4204, 2206, 884, -7671]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N1 B_one_repr
lemma NI113N1 : Nat.card (O ⧸ I113N1) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N1

def I113N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9576113, -2744794, 1287134, -3867588, -5571720]] i)))

def SI113N2: IdealEqSpanCertificate' Table ![![-9576113, -2744794, 1287134, -3867588, -5571720]] 
 ![![113, 0, 0, 0, 0], ![62, 1, 0, 0, 0], ![111, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![44, 0, 0, 0, 1]] where
  M :=![![![-9576113, -2744794, 1287134, -3867588, -5571720], ![-24450336, -7008031, 3286250, -9874864, -14225544], ![-62426360, -17893950, 8391017, -25213180, -36322280], ![-3714152, -1064430, 499206, -1499961, -2161088], ![-17752156, -5088628, 2386160, -7169952, -10328877]]]
  hmulB := by decide  
  f := ![![![1537615, 31818, 881730, -3171060, -3310456]], ![![699634, 42017, 538954, -1804624, -1952968]], ![![971065, 98356, 948323, -3030680, -3360032]], ![![110836, -15562, -25758, 5967, 50976]], ![![482528, 26892, 361272, -1217216, -1313093]]]
  g := ![![![2463321, -2744794, 1287134, -3867588, -5571720], ![6289356, -7008031, 3286250, -9874864, -14225544], ![16058661, -17893950, 8391017, -25213180, -36322280], ![955366, -1064430, 499206, -1499961, -2161088], ![4566632, -5088628, 2386160, -7169952, -10328877]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N2 : Nat.card (O ⧸ I113N2) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N2)

lemma isPrimeI113N2 : Ideal.IsPrime I113N2 := prime_ideal_of_norm_prime hp113.out _ NI113N2
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![33162, 8082, 56011, -165540, -191351]] ![![-8, 0, 1, 2, -1]]
  ![![-1537615, -31818, -881730, 3171060, 3310456]] where
 M := ![![![-1537615, -31818, -881730, 3171060, 3310456]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI113N1 : IdealMulLeCertificate' Table 
  ![![-1537615, -31818, -881730, 3171060, 3310456]] ![![-9576113, -2744794, 1287134, -3867588, -5571720]]
  ![![113, 0, 0, 0, 0]] where
 M := ![![![-113, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N1, I113N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N1
    exact isPrimeI113N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0 ⊙ MulI113N1)
instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0, 0, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0, 0, 0]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![0, 0, 127, 0, 0], ![0, 0, 0, 127, 0], ![0, 0, 0, 0, 127]] where
  M :=![![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![0, 0, 127, 0, 0], ![0, 0, 0, 127, 0], ![0, 0, 0, 0, 127]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 5 2 6 [3, 90, 53, 60, 53, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 100, 120, 116, 118], [33, 50, 27, 83, 110], [59, 125, 1, 53, 20], [109, 105, 106, 2, 6], [0, 1]]
 g := ![![[0, 95, 117, 27, 8], [84, 25, 60, 110, 121], [86, 119, 121, 9, 22], [76, 78, 27, 103, 61], [82, 74, 1], []], ![[116, 44, 54, 114, 70, 107, 62, 40], [114, 106, 97, 55, 53, 100, 4, 97], [36, 37, 107, 54, 41, 113, 22, 45], [66, 11, 102, 46, 78, 113, 18, 24], [15, 68, 32, 124, 121, 21, 88, 6], [102, 69, 13, 85, 96, 88, 23, 33]], ![[60, 122, 94, 110, 51, 41, 113, 55], [47, 36, 58, 11, 115, 1, 88, 126], [52, 57, 54, 80, 79, 40, 72, 105], [67, 1, 83, 58, 102, 6, 13, 59], [77, 10, 117, 28, 63, 111, 25, 46], [1, 53, 118, 106, 62, 93, 118, 40]], ![[66, 25, 97, 28, 93, 60, 47, 109], [109, 122, 43, 19, 123, 42, 74, 112], [71, 125, 107, 48, 90, 48, 120, 67], [109, 86, 2, 124, 85, 118, 62, 80], [50, 97, 55, 1, 23, 59, 59, 10], [71, 4, 82, 58, 29, 20, 26, 126]], ![[18, 15, 47, 23, 87, 80, 10, 86], [84, 2, 42, 115, 7, 58, 75, 86], [122, 50, 80, 83, 97, 44, 108, 90], [75, 25, 111, 48, 79, 113, 75, 85], [86, 7, 98, 0, 20, 18, 94, 43], [63, 104, 31, 18, 12, 4, 71, 89]]]
 h' := ![![[0, 100, 120, 116, 118], [2, 1, 35, 13, 32], [123, 72, 87, 106, 11], [26, 102, 81, 72, 99], [8, 18, 40, 85, 51], [0, 0, 0, 1], [0, 1]], ![[33, 50, 27, 83, 110], [39, 122, 8, 93, 68], [19, 115, 43, 18, 56], [56, 58, 114, 65, 54], [82, 114, 123, 32, 35], [75, 11, 29, 103, 46], [0, 100, 120, 116, 118]], ![[59, 125, 1, 53, 20], [49, 11, 115, 14, 8], [122, 1, 104, 61, 53], [109, 1, 53, 25, 87], [116, 56, 97, 116, 125], [120, 33, 78, 49, 31], [33, 50, 27, 83, 110]], ![[109, 105, 106, 2, 6], [50, 91, 94, 30, 56], [74, 98, 7, 89, 44], [110, 125, 28, 70, 88], [60, 24, 67, 60, 125], [61, 17, 51, 98, 8], [59, 125, 1, 53, 20]], ![[0, 1], [88, 29, 2, 104, 90], [100, 95, 13, 107, 90], [77, 95, 105, 22, 53], [92, 42, 54, 88, 45], [75, 66, 96, 3, 42], [109, 105, 106, 2, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [85, 107, 98, 31], [], [], []]
 b := ![[], [8, 28, 76, 103, 74], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 5
  hpos := by decide
  P := [3, 90, 53, 60, 53, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3306819523, 4066423160, 4707366760, 3422111520, -24653971520]
  a := ![12, -4, -14, -2, 48]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![26037949, 32019080, 37065880, 26945760, -194125760]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 33038369407 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def PBC127 : ContainsPrimesAboveP 127 ![I127N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![127, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 127 (by decide) 𝕀

instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-519183, -148814, 69784, -209688, -302078]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![-519183, -148814, 69784, -209688, -302078]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![0, 0, 131, 0, 0], ![0, 0, 0, 131, 0], ![29, 33, 77, 120, 1]] where
  M :=![![![-519183, -148814, 69784, -209688, -302078], ![-1325610, -379951, 178172, -535380, -771270], ![-3384570, -970130, 454919, -1366960, -1969230], ![-201356, -57718, 27066, -81325, -117164], ![-962476, -275876, 129364, -388724, -559985]]]
  hmulB := by decide  
  f := ![![![31, -6, -8, 8, 18]], ![![70, -1, -12, -20, 10]], ![![-10, -10, 69, -160, -190]], ![![-124, 18, 34, -7, -76]], ![![-95, 9, 67, -104, -175]]]
  g := ![![![62909, 74960, 178090, 275112, -302078], ![160620, 191389, 454702, 702420, -771270], ![410100, 488660, 1160959, 1793440, -1969230], ![24400, 29074, 69074, 106705, -117164], ![116619, 138959, 330139, 509996, -559985]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 4 2 7 [130, 113, 85, 4, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [57, 64, 123, 18], [72, 43, 60, 22], [129, 23, 79, 91], [0, 1]]
 g := ![![[57, 108, 80, 102], [90, 76, 79, 34], [46, 120, 11], [78, 38, 77], [113, 92, 16], [1], []], ![[5, 62, 95, 39, 83, 97], [56, 21, 36, 99, 56, 88], [93, 119, 43], [126, 2, 91], [109], [12, 76, 80], [28, 119, 62]], ![[33, 122, 95, 102, 22, 128], [82, 38, 116, 82, 46, 71], [11, 8, 38], [87, 127, 4], [54, 3, 60], [126, 41, 107], [50, 49, 91]], ![[128, 58, 13, 85, 7, 84], [61, 97, 119, 72, 115, 49], [8, 6, 13], [40, 45, 129], [79, 12, 109], [58, 108, 49], [108, 118, 28]]]
 h' := ![![[57, 64, 123, 18], [90, 28, 54, 87], [67, 77, 59, 54], [105, 115, 56, 81], [114, 66, 81, 83], [1, 18, 46, 127], [0, 0, 1], [0, 1]], ![[72, 43, 60, 22], [10, 93, 25, 10], [11, 24, 30, 54], [124, 117, 15, 49], [103, 125, 50, 22], [16, 4, 90], [2, 59, 126, 39], [57, 64, 123, 18]], ![[129, 23, 79, 91], [62, 52, 67, 84], [20, 30, 75, 65], [128, 73, 117, 13], [98, 96, 128, 129], [31, 64, 42, 45], [125, 67, 7, 99], [72, 43, 60, 22]], ![[0, 1], [123, 89, 116, 81], [121, 0, 98, 89], [84, 88, 74, 119], [100, 106, 3, 28], [26, 45, 84, 90], [112, 5, 128, 124], [129, 23, 79, 91]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [74, 85, 19], []]
 b := ![[], [], [72, 45, 119, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 4
  hpos := by decide
  P := [130, 113, 85, 4, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-23770728, 75312537, -12167584, 32848780, 36872367]
  a := ![24, 19, -20, 44, 83]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-8344041, -8713554, -21765953, -33525460, 36872367]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 294499921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, -6, -8, 8, 18]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![31, -6, -8, 8, 18]] 
 ![![131, 0, 0, 0, 0], ![91, 1, 0, 0, 0], ![103, 0, 1, 0, 0], ![39, 0, 0, 1, 0], ![126, 0, 0, 0, 1]] where
  M :=![![![31, -6, -8, 8, 18], ![70, -1, -12, -20, 10], ![-10, -10, 69, -160, -190], ![-124, 18, 34, -7, -76], ![-4, -4, 12, -36, -27]]]
  hmulB := by decide  
  f := ![![![-519183, -148814, 69784, -209688, -302078]], ![![-370773, -106275, 49836, -149748, -215728]], ![![-434049, -124412, 58341, -175304, -252544]], ![![-156103, -44744, 20982, -63047, -90826]], ![![-506714, -145240, 68108, -204652, -294823]]]
  g := ![![![-9, -6, -8, 8, 18], ![7, -1, -12, -20, 10], ![183, -10, 69, -160, -190], ![35, 18, 34, -7, -76], ![30, -4, 12, -36, -27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![-519183, -148814, 69784, -209688, -302078]] ![![31, -6, -8, 8, 18]]
  ![![131, 0, 0, 0, 0]] where
 M := ![![![131, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC131 : ContainsPrimesAboveP 131 ![I131N0, I131N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
    exact isPrimeI131N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 131 (by decide) (𝕀 ⊙ MulI131N0)
instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0, 0, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0, 0, 0]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![0, 0, 137, 0, 0], ![0, 0, 0, 137, 0], ![0, 0, 0, 0, 137]] where
  M :=![![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![0, 0, 137, 0, 0], ![0, 0, 0, 137, 0], ![0, 0, 0, 0, 137]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 5 2 7 [97, 126, 3, 44, 5, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [103, 135, 106, 92, 102], [12, 124, 127, 70, 55], [129, 39, 81, 92, 70], [25, 112, 97, 20, 47], [0, 1]]
 g := ![![[6, 60, 90, 92, 22], [122, 55, 45, 68], [18, 49, 18, 72], [12, 129, 73, 24, 32], [38, 118, 132, 1], [], []], ![[34, 96, 38, 13, 54, 4, 2, 92], [132, 99, 136, 60], [102, 27, 123, 93], [116, 109, 48, 24, 44, 134, 132, 48], [75, 125, 134, 135], [83, 85, 131, 133], [28, 105, 39, 129]], ![[67, 111, 95, 123, 60, 82, 87, 80], [113, 3, 121, 77], [68, 95, 89, 105], [122, 42, 83, 27, 120, 118, 18, 95], [8, 101, 92, 32], [91, 36, 18, 121], [113, 26, 110, 11]], ![[105, 53, 108, 58, 65, 82, 53, 79], [118, 99, 93, 121], [119, 84, 30, 28], [28, 134, 19, 12, 70, 85, 70, 40], [26, 4, 23, 120], [64, 127, 81, 81], [98, 126, 25, 105]], ![[131, 63, 0, 29, 91, 131, 32, 91], [59, 46, 41, 133], [86, 115, 63, 11], [52, 53, 23, 126, 64, 49, 14, 124], [136, 59, 21, 65], [24, 82, 78, 115], [107, 69, 14, 17]]]
 h' := ![![[103, 135, 106, 92, 102], [86, 11, 35, 50, 76], [1, 84, 128, 22, 43], [69, 118, 69, 94, 88], [13, 69, 25, 14, 124], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[12, 124, 127, 70, 55], [15, 17, 63, 62, 103], [107, 10, 80, 87, 34], [0, 85, 87, 69, 40], [49, 126, 109, 76, 22], [101, 43, 126, 74, 86], [84, 123, 85, 102, 63], [103, 135, 106, 92, 102]], ![[129, 39, 81, 92, 70], [119, 18, 64, 3, 20], [95, 47, 42, 94, 112], [65, 95, 131, 115, 67], [27, 134, 96, 47, 8], [114, 63, 27, 43, 124], [6, 53, 29, 47, 11], [12, 124, 127, 70, 55]], ![[25, 112, 97, 20, 47], [111, 13, 78, 112, 125], [130, 130, 3, 94, 11], [24, 51, 106, 112, 24], [0, 18, 54, 63, 23], [78, 64, 130, 4, 95], [11, 14, 125, 110, 128], [129, 39, 81, 92, 70]], ![[0, 1], [96, 78, 34, 47, 87], [32, 3, 21, 114, 74], [47, 62, 18, 21, 55], [67, 64, 127, 74, 97], [45, 104, 128, 16, 105], [110, 84, 34, 15, 72], [25, 112, 97, 20, 47]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 49, 7, 96], [], [], []]
 b := ![[], [28, 127, 105, 2, 128], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 5
  hpos := by decide
  P := [97, 126, 3, 44, 5, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![24112, -98092, -144809, 309894, 324964]
  a := ![0, -3, -1, -4, 1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![176, -716, -1057, 2262, 2372]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 48261724457 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def PBC137 : ContainsPrimesAboveP 137 ![I137N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![137, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 137 (by decide) 𝕀

instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![91845, 2233, 54331, -193782, -203134]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![91845, 2233, 54331, -193782, -203134]] 
 ![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![0, 0, 139, 0, 0], ![0, 0, 0, 139, 0], ![36, 15, 109, 66, 1]] where
  M :=![![![91845, 2233, 54331, -193782, -203134], ![-996966, 169718, 380445, -444304, -940854], ![-3711170, 460955, 561776, 589830, -731870], ![396888, -116105, -394263, 814503, 1161852], ![-799542, 99634, 122656, 122804, -162947]]]
  hmulB := by decide  
  f := ![![![152311, 43635, -20459, 61500, 88578]], ![![388734, 111516, -52287, 157066, 226266]], ![![992930, 284365, -133416, 400860, 577730]], ![![59124, 16913, -7905, 23855, 34236]], ![![890130, 254939, -119589, 359368, 517837]]]
  g := ![![![53271, 21937, 159683, 95058, -203134], ![236502, 102752, 740529, 443540, -940854], ![162850, 82295, 577954, 351750, -731870], ![-298056, -126215, -913929, -545811, 1161852], ![36450, 18301, 128661, 78254, -162947]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 4 2 7 [119, 96, 98, 16, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [86, 63, 32, 69], [126, 66, 107, 32], [50, 9, 0, 38], [0, 1]]
 g := ![![[46, 48, 121, 24], [40, 4, 71, 63], [81, 65, 127], [67, 32, 69, 77], [29, 13, 117], [1], []], ![[75, 32, 0, 120, 12, 64], [95, 45, 23, 107, 42, 136], [114, 52, 120], [54, 43, 110, 77, 3, 89], [28], [66, 40, 35], [53, 103, 35]], ![[45, 5, 129, 71, 24, 61], [5, 21, 28, 83, 30, 48], [78, 57, 137], [60, 51, 92, 137, 39, 60], [130, 61, 30], [82, 127, 122], [65, 55, 51]], ![[57, 1, 59, 99, 62, 127], [108, 125, 20, 80, 95, 125], [47, 45, 49], [37, 32, 121, 100, 28, 46], [116, 47, 9], [85, 38, 137], [42, 109, 54]]]
 h' := ![![[86, 63, 32, 69], [105, 130, 108, 21], [89, 9, 7, 87], [89, 95, 85, 108], [7, 30, 71, 63], [20, 43, 41, 123], [0, 0, 1], [0, 1]], ![[126, 66, 107, 32], [130, 132, 17, 17], [125, 61, 1, 59], [114, 37, 69, 113], [100, 0, 80, 10], [42, 32, 81], [116, 24, 95, 69], [86, 63, 32, 69]], ![[50, 9, 0, 38], [34, 43, 77, 72], [23, 18, 5, 40], [100, 36, 35, 50], [55, 125, 106, 38], [97, 68, 101, 13], [79, 94, 118, 20], [126, 66, 107, 32]], ![[0, 1], [12, 112, 76, 29], [18, 51, 126, 92], [107, 110, 89, 7], [37, 123, 21, 28], [48, 135, 55, 3], [4, 21, 64, 50], [50, 9, 0, 38]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [128, 81, 138], []]
 b := ![[], [], [81, 135, 137, 126], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 4
  hpos := by decide
  P := [119, 96, 98, 16, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-352725453, 231810266, -139199675, 94020618, 358723840]
  a := ![23, 9, -23, 28, 89]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-95444487, -37043506, -282302865, -169652898, 358723840]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 373301041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-152311, -43635, 20459, -61500, -88578]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![-152311, -43635, 20459, -61500, -88578]] 
 ![![139, 0, 0, 0, 0], ![31, 1, 0, 0, 0], ![12, 0, 1, 0, 0], ![128, 0, 0, 1, 0], ![65, 0, 0, 0, 1]] where
  M :=![![![-152311, -43635, 20459, -61500, -88578], ![-388734, -111516, 52287, -157066, -226266], ![-992930, -284365, 133416, -400860, -577730], ![-59124, -16913, 7905, -23855, -34236], ![-282310, -80878, 37968, -113992, -164399]]]
  hmulB := by decide  
  f := ![![![-91845, -2233, -54331, 193782, 203134]], ![![-13311, -1719, -14854, 46414, 52072]], ![![18770, -3509, -8732, 12486, 22802]], ![![-87432, -1221, -47195, 172587, 178700]], ![![-37197, -1761, -26289, 89734, 96163]]]
  g := ![![![104924, -43635, 20459, -61500, -88578], ![268004, -111516, 52287, -157066, -226266], ![684057, -284365, 133416, -400860, -577730], ![40641, -16913, 7905, -23855, -34236], ![194577, -80878, 37968, -113992, -164399]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![91845, 2233, 54331, -193782, -203134]] ![![-152311, -43635, 20459, -61500, -88578]]
  ![![139, 0, 0, 0, 0]] where
 M := ![![![-139, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC139 : ContainsPrimesAboveP 139 ![I139N0, I139N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
    exact isPrimeI139N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 139 (by decide) (𝕀 ⊙ MulI139N0)
instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9263, -2639, 1239, -3730, -5376]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![-9263, -2639, 1239, -3730, -5376]] 
 ![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![0, 0, 149, 0, 0], ![65, 56, 36, 1, 0], ![124, 60, 68, 0, 1]] where
  M :=![![![-9263, -2639, 1239, -3730, -5376], ![-23588, -6798, 3175, -9552, -13712], ![-60240, -17265, 8146, -24330, -35280], ![-3656, -985, 457, -1433, -2024], ![-17072, -4946, 2338, -6932, -10087]]]
  hmulB := by decide  
  f := ![![![-439, 61, 99, -16, -192]], ![![-608, 40, -83, 558, 448]], ![![2460, -465, -1186, 1740, 3120]], ![![185, -72, -276, 621, 840]], ![![516, -146, -494, 1008, 1449]]]
  g := ![![![6039, 3549, 3363, -3730, -5376], ![15420, 9066, 8587, -9552, -13712], ![39570, 23235, 22034, -24330, -35280], ![2285, 1347, 1273, -1433, -2024], ![11304, 6634, 6294, -6932, -10087]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [110, 97, 55, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [92, 90, 84], [2, 58, 65], [0, 1]]
 g := ![![[10, 22, 39], [9, 148], [148, 95, 67], [80, 20], [10, 134, 22], [94, 1], []], ![[76, 95, 100, 43], [112, 22], [21, 89, 8, 38], [148, 31], [80, 16, 100, 66], [79, 86], [136, 53]], ![[92, 45, 110, 70], [125, 64], [132, 57, 122, 131], [120, 22], [45, 39, 99, 56], [44, 54], [6, 53]]]
 h' := ![![[92, 90, 84], [84, 97, 121], [110, 31, 105], [111, 85, 31], [92, 138, 136], [90, 10, 97], [0, 0, 1], [0, 1]], ![[2, 58, 65], [27, 37, 117], [24, 113, 52], [106, 17, 147], [88, 24, 110], [125, 39, 59], [60, 71, 58], [92, 90, 84]], ![[0, 1], [21, 15, 60], [130, 5, 141], [60, 47, 120], [105, 136, 52], [101, 100, 142], [89, 78, 90], [2, 58, 65]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41, 21], []]
 b := ![[], [134, 147, 37], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [110, 97, 55, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![23812, -48315, 29583, -65600, 8855]
  a := ![14, 7, -17, 20, 55]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![21408, 20765, 12007, -65600, 8855]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 3307949 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![439, -61, -99, 16, 192]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![439, -61, -99, 16, 192]] 
 ![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![11, 87, 1, 0, 0], ![98, 94, 0, 1, 0], ![6, 105, 0, 0, 1]] where
  M :=![![![439, -61, -99, 16, 192], ![608, -40, 83, -558, -448], ![-2460, 465, 1186, -1740, -3120], ![-1588, 193, 215, 319, -232], ![-520, 98, 254, -376, -669]]]
  hmulB := by decide  
  f := ![![![9263, 2639, -1239, 3730, 5376]], ![![23588, 6798, -3175, 9552, 13712]], ![![14861, 4280, -2000, 6016, 8640]], ![![20998, 6031, -2821, 8489, 12200]], ![![17110, 4930, -2303, 6928, 9947]]]
  g := ![![![-8, -88, -99, 16, 192], ![383, 619, 83, -558, -448], ![1166, 2607, 1186, -1740, -3120], ![-227, -162, 215, 319, -232], ![252, 561, 254, -376, -669]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P1 : CertificateIrreducibleZModOfList' 149 2 2 7 [57, 148, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 148], [0, 1]]
 g := ![![[115, 118], [17], [13, 121], [1], [21, 104], [1], [1]], ![[84, 31], [17], [134, 28], [1], [125, 45], [1], [1]]]
 h' := ![![[1, 148], [90, 72], [4, 100], [117, 11], [144, 148], [63, 36], [92, 1], [0, 1]], ![[0, 1], [13, 77], [104, 49], [128, 138], [143, 1], [99, 113], [93, 148], [1, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65]]
 b := ![[], [21, 107]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N1 : CertifiedPrimeIdeal' SI149N1 149 where
  n := 2
  hpos := by decide
  P := [57, 148, 1]
  hirr := P149P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1915, 1474, -1138, 2721, 4376]
  a := ![10, 8, -10, 19, 36]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1869, -4126, -1138, 2721, 4376]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N1 B_one_repr
lemma NI149N1 : Nat.card (O ⧸ I149N1) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![-9263, -2639, 1239, -3730, -5376]] ![![439, -61, -99, 16, 192]]
  ![![149, 0, 0, 0, 0]] where
 M := ![![![-149, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC149 : ContainsPrimesAboveP 149 ![I149N0, I149N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
    exact isPrimeI149N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 149 (by decide) (𝕀 ⊙ MulI149N0)
instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-194, 26, 39, 32, -75]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![-194, 26, 39, 32, -75]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![0, 0, 151, 0, 0], ![50, 10, 10, 1, 0], ![36, 16, 42, 0, 1]] where
  M :=![![![-194, 26, 39, 32, -75], ![-161, 33, -145, 336, 481], ![2115, -550, -494, 520, 1245], ![558, 0, -14, -257, -198], ![514, -188, -100, 78, 317]]]
  hmulB := by decide  
  f := ![![![87368, 25042, -11743, 35286, 50833]], ![![223071, 63939, -29983, 90094, 129789]], ![![569555, 163250, -76554, 230030, 331385]], ![![81646, 23402, -10974, 32975, 47504]], ![![203958, 58460, -27414, 82374, 118669]]]
  g := ![![![6, 6, 19, 32, -75], ![-227, -73, -157, 336, 481], ![-455, -170, -384, 520, 1245], ![136, 38, 72, -257, -198], ![-98, -40, -94, 78, 317]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [91, 67, 36, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [74, 118, 38], [41, 32, 113], [0, 1]]
 g := ![![[117, 103, 64], [11, 148, 72], [138], [64, 128], [85, 66, 139], [115, 1], []], ![[11, 128, 111, 69], [135, 134, 119, 42], [7, 145, 50, 139], [67, 105], [65, 114, 147, 20], [131, 118], [19, 85]], ![[66, 146, 80, 109], [126, 123, 69, 89], [11, 72, 94, 12], [86, 80], [72, 64, 116, 28], [56, 32], [95, 85]]]
 h' := ![![[74, 118, 38], [56, 10, 143], [126, 134, 26], [13, 134], [117, 79, 85], [105, 56, 21], [0, 0, 1], [0, 1]], ![[41, 32, 113], [114, 123, 124], [103, 108, 35], [114, 108, 109], [110, 111, 135], [37, 115, 82], [123, 0, 32], [74, 118, 38]], ![[0, 1], [6, 18, 35], [18, 60, 90], [71, 60, 42], [14, 112, 82], [60, 131, 48], [133, 0, 118], [41, 32, 113]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20, 84], []]
 b := ![[], [55, 112, 117], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [91, 67, 36, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4636068, 2933097, -1216094, 942686, 2275041]
  a := ![-23, -7, 22, -30, -99]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-885244, -284069, -703276, 942686, 2275041]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 3442951 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![918, -151, -324, 340, 781]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![918, -151, -324, 340, 781]] 
 ![![151, 0, 0, 0, 0], ![71, 1, 0, 0, 0], ![93, 0, 1, 0, 0], ![29, 0, 0, 1, 0], ![60, 0, 0, 0, 1]] where
  M :=![![![918, -151, -324, 340, 781], ![3023, -362, -390, -658, 377], ![-185, 415, 1989, -5120, -6395], ![-4454, 645, 1133, -497, -2366], ![-18, 86, 422, -1098, -1363]]]
  hmulB := by decide  
  f := ![![![-28684, -8269, 3804, -11616, -16407]], ![![-13967, -4029, 1856, -5658, -8004]], ![![-18927, -5432, 2501, -7648, -10806]], ![![-5578, -1614, 741, -2263, -3191]], ![![-11760, -3378, 1556, -4754, -6721]]]
  g := ![![![-99, -151, -324, 340, 781], ![407, -362, -390, -658, 377], ![2103, 415, 1989, -5120, -6395], ![5, 645, 1133, -497, -2366], ![452, 86, 422, -1098, -1363]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1

def I151N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-34668965, -9937129, 4659827, -14002048, -20171356]] i)))

def SI151N2: IdealEqSpanCertificate' Table ![![-34668965, -9937129, 4659827, -14002048, -20171356]] 
 ![![151, 0, 0, 0, 0], ![131, 1, 0, 0, 0], ![53, 0, 1, 0, 0], ![116, 0, 0, 1, 0], ![137, 0, 0, 0, 1]] where
  M :=![![![-34668965, -9937129, 4659827, -14002048, -20171356], ![-88518164, -25371878, 11897659, -35750586, -51502316], ![-226008120, -64780455, 30377564, -91279800, -131497740], ![-13446200, -3854071, 1807291, -5430631, -7823360], ![-64270126, -18421674, 8638496, -25957316, -37394135]]]
  hmulB := by decide  
  f := ![![![-247887, 50257, 134893, -216302, -364604]], ![![-225163, 44993, 119242, -187846, -320528]], ![![-100041, 18416, 45103, -62776, -116872]], ![![-179416, 36801, 99763, -162149, -270800]], ![![-227759, 45773, 121923, -193442, -328459]]]
  g := ![![![35813493, -9937129, 4659827, -14002048, -20171356], ![91440445, -25371878, 11897659, -35750586, -51502316], ![233469323, -64780455, 30377564, -91279800, -131497740], ![13890094, -3854071, 1807291, -5430631, -7823360], ![66391881, -18421674, 8638496, -25957316, -37394135]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N2 : Nat.card (O ⧸ I151N2) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N2)

lemma isPrimeI151N2 : Ideal.IsPrime I151N2 := prime_ideal_of_norm_prime hp151.out _ NI151N2
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![-194, 26, 39, 32, -75]] ![![918, -151, -324, 340, 781]]
  ![![-247887, 50257, 134893, -216302, -364604]] where
 M := ![![![-247887, 50257, 134893, -216302, -364604]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI151N1 : IdealMulLeCertificate' Table 
  ![![-247887, 50257, 134893, -216302, -364604]] ![![-34668965, -9937129, 4659827, -14002048, -20171356]]
  ![![151, 0, 0, 0, 0]] where
 M := ![![![151, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC151 : ContainsPrimesAboveP 151 ![I151N0, I151N1, I151N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
    exact isPrimeI151N1
    exact isPrimeI151N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 151 (by decide) (𝕀 ⊙ MulI151N0 ⊙ MulI151N1)


lemma PB397I3_primes (p : ℕ) :
  p ∈ Set.range ![107, 109, 113, 127, 131, 137, 139, 149, 151] ↔ Nat.Prime p ∧ 103 < p ∧ p ≤ 151 := by
  rw [← List.mem_ofFn']
  convert primes_range 103 151 (by omega)

def PB397I3 : PrimesBelowBoundCertificateInterval O 103 151 397 where
  m := 9
  g := ![2, 2, 3, 1, 2, 1, 2, 2, 3]
  P := ![107, 109, 113, 127, 131, 137, 139, 149, 151]
  hP := PB397I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1, I113N2]
    · exact ![I127N0]
    · exact ![I131N0, I131N1]
    · exact ![I137N0]
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N1, I151N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC107
    · exact PBC109
    · exact PBC113
    · exact PBC127
    · exact PBC131
    · exact PBC137
    · exact PBC139
    · exact PBC149
    · exact PBC151
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![131079601, 107]
    · exact ![1295029, 11881]
    · exact ![12769, 12769, 113]
    · exact ![33038369407]
    · exact ![294499921, 131]
    · exact ![48261724457]
    · exact ![373301041, 139]
    · exact ![3307949, 22201]
    · exact ![3442951, 151, 151]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
      exact NI113N2
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
      exact NI139N1
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
      exact NI151N2
  β := ![I107N1, I113N2, I131N1, I139N1, I151N1, I151N2]
  Il := ![[I107N1], [], [I113N2], [], [I131N1], [], [I139N1], [], [I151N1, I151N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
