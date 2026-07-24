
import IdealArithmetic.Examples.NF5_3_379687500_2.RI5_3_379687500_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![51, 60, 4, -22, -134]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![51, 60, 4, -22, -134]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![0, 0, 67, 0, 0], ![19, 46, 12, 1, 0], ![1, 49, 8, 0, 1]] where
  M :=![![![51, 60, 4, -22, -134], ![-12, -137, -8, 30, 222], ![1116, 1344, 71, -478, -2934], ![-1004, -2472, -144, 673, 4634], ![264, 480, 28, -144, -953]]]
  hmulB := by decide  
  f := ![![![-327, -180, -20, 70, 406]], ![![-532, -299, -32, 114, 658]], ![![-956, -576, -67, 222, 1286]], ![![-635, -362, -40, 139, 804]], ![![-513, -293, -32, 112, 647]]]
  g := ![![![9, 114, 20, -22, -134], ![-12, -185, -32, 30, 222], ![196, 2494, 437, -478, -2934], ![-275, -3888, -676, 673, 4634], ![59, 803, 140, -144, -953]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [36, 42, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [46, 7, 28], [12, 59, 39], [0, 1]]
 g := ![![[62, 39, 65], [48, 35, 35], [7, 16], [56, 47], [58, 1], []], ![[66, 13, 45, 27], [42, 61, 27, 34], [2, 36], [29, 56], [50, 64], [36, 47]], ![[41, 43, 54, 22], [5, 57, 4, 25], [53, 4], [56, 33], [23, 49], [25, 47]]]
 h' := ![![[46, 7, 28], [14, 29, 20], [42, 65, 13], [48, 23, 63], [56, 7, 39], [0, 0, 1], [0, 1]], ![[12, 59, 39], [60, 57, 49], [24, 5, 41], [37, 16, 6], [64, 39, 18], [16, 53, 59], [46, 7, 28]], ![[0, 1], [49, 48, 65], [39, 64, 13], [65, 28, 65], [2, 21, 10], [48, 14, 7], [12, 59, 39]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54, 31], []]
 b := ![[], [0, 8, 30], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [36, 42, 9, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1899530064, 1919569758, 110054076, -742672290, -4444481124]
  a := ![935, 890, 79, -369, -2189]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![305295294, 3788986122, 665342844, -742672290, -4444481124]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 300763 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1645, 1098, 60, -534, -2960]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![1645, 1098, 60, -534, -2960]] 
 ![![67, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![20, 0, 0, 1, 0], ![27, 0, 0, 0, 1]] where
  M :=![![![1645, 1098, 60, -534, -2960], ![7900, 5273, 288, -2564, -14212], ![37944, 25332, 1385, -12316, -68268], ![72136, 48150, 2634, -23411, -129772], ![-5744, -3834, -210, 1864, 10333]]]
  hmulB := by decide  
  f := ![![![247, 558, 24, -166, -1088]], ![![-4, 17, 0, -4, -28]], ![![175, 282, 17, -90, -580]], ![![-428, -630, -42, 205, 1308]], ![![183, 360, 18, -110, -715]]]
  g := ![![![1243, 1098, 60, -534, -2960], ![5968, 5273, 288, -2564, -14212], ![28667, 25332, 1385, -12316, -68268], ![54494, 48150, 2634, -23411, -129772], ![-4339, -3834, -210, 1864, 10333]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3105, -4979, -295, 1580, 10160]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![-3105, -4979, -295, 1580, 10160]] 
 ![![67, 0, 0, 0, 0], ![36, 1, 0, 0, 0], ![44, 0, 1, 0, 0], ![57, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![-3105, -4979, -295, 1580, 10160], ![15880, 25415, 1506, -8070, -51880], ![-80740, -129420, -7669, 41072, 264100], ![246650, 394908, 23400, -125379, -806072], ![-41962, -67202, -3982, 21334, 137163]]]
  hmulB := by decide  
  f := ![![![5, -1771, -221, 546, 2964]], ![![-144, -1033, -138, 338, 1872]], ![![240, -716, -77, 192, 988]], ![![625, -1539, -153, 391, 1964]], ![![-161, -215, -37, 88, 519]]]
  g := ![![![417, -4979, -295, 1580, 10160], ![-2122, 25415, 1506, -8070, -51880], ![10836, -129420, -7669, 41072, 264100], ![-32993, 394908, 23400, -125379, -806072], ![5617, -67202, -3982, 21334, 137163]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![51, 60, 4, -22, -134]] ![![1645, 1098, 60, -534, -2960]]
  ![![-107625, -71838, -3928, 34928, 193610]] where
 M := ![![![-107625, -71838, -3928, 34928, 193610]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![-107625, -71838, -3928, 34928, 193610]] ![![-3105, -4979, -295, 1580, 10160]]
  ![![67, 0, 0, 0, 0]] where
 M := ![![![1263285, 831269, 45359, -407628, -2253746]]]
 hmul := by decide  
 g := ![![![![18855, 12407, 677, -6084, -33638]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1, I67N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
    exact isPrimeI67N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0 ⊙ MulI67N1)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1275, -1704, -285, 687, 4036]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-1275, -1704, -285, 687, 4036]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![23, 62, 29, 1, 0], ![42, 64, 4, 0, 1]] where
  M :=![![![-1275, -1704, -285, 687, 4036], ![-3782, 439, -186, 376, 3014], ![20472, 19698, 3655, -8710, -52290], ![-1946, -26163, -3261, 8175, 44570], ![-1346, 4335, 435, -1130, -5739]]]
  hmulB := by decide  
  f := ![![![203, 249, 18, -79, -504]], ![![-682, -1111, -60, 366, 2326]], ![![2908, 5154, 317, -1550, -10174]], ![![487, 962, 68, -256, -1760]], ![![-302, -521, -23, 182, 1137]]]
  g := ![![![-2628, -4262, -512, 687, 4036], ![-1958, -3039, -326, 376, 3014], ![34042, 55018, 6555, -8710, -52290], ![-29041, -47683, -5896, 8175, 44570], ![3742, 6221, 791, -1130, -5739]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [55, 32, 25, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 14, 17], [40, 56, 54], [0, 1]]
 g := ![![[27, 19, 48], [50, 63, 57], [38, 44, 38], [41, 57], [46, 1], []], ![[30, 11, 38, 63], [17, 29, 13, 47], [17, 19, 16, 13], [63, 49], [64, 12], [67, 5]], ![[65, 9, 4, 40], [10, 51, 5, 24], [41, 66, 39, 48], [65, 30], [50, 54], [30, 5]]]
 h' := ![![[6, 14, 17], [19, 14, 41], [40, 61, 25], [54, 0, 31], [26, 35, 25], [0, 0, 1], [0, 1]], ![[40, 56, 54], [20, 63, 49], [61, 30, 23], [38, 12, 32], [33, 21, 7], [43, 21, 56], [6, 14, 17]], ![[0, 1], [20, 65, 52], [23, 51, 23], [66, 59, 8], [34, 15, 39], [21, 50, 14], [40, 56, 54]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56, 69], []]
 b := ![[], [43, 17, 21], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [55, 32, 25, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5024343461, -6110918999, -363009231, 2174387734, 13395570066]
  a := ![-1313, -1315, -111, 518, 3074]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-8699284565, -14059710461, -1647923011, 2174387734, 13395570066]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 357911 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-203, -249, -18, 79, 504]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-203, -249, -18, 79, 504]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![57, 14, 1, 0, 0], ![34, 30, 0, 1, 0], ![28, 27, 0, 0, 1]] where
  M :=![![![-203, -249, -18, 79, 504], ![682, 1111, 60, -366, -2326], ![-2908, -5154, -317, 1550, 10174], ![12140, 18009, 1059, -5899, -37466], ![-2048, -3039, -183, 984, 6273]]]
  hmulB := by decide  
  f := ![![![1275, 1704, 285, -687, -4036]], ![![3782, -439, 186, -376, -3014]], ![![1481, 1004, 214, -503, -3098]], ![![2236, 999, 261, -603, -3834]], ![![1960, 444, 177, -398, -2657]]]
  g := ![![![-225, -225, -18, 79, 504], ![1054, 1043, 60, -366, -2326], ![-4541, -4534, -317, 1550, 10174], ![16921, 16785, 1059, -5899, -37466], ![-2827, -2808, -183, 984, 6273]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P1 : CertificateIrreducibleZModOfList' 71 2 2 6 [53, 57, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 70], [0, 1]]
 g := ![![[56, 49], [38, 25], [3, 5], [40], [54], [1]], ![[32, 22], [33, 46], [2, 66], [40], [54], [1]]]
 h' := ![![[14, 70], [45, 64], [54, 5], [50, 54], [18, 53], [18, 14], [0, 1]], ![[0, 1], [18, 7], [53, 66], [25, 17], [50, 18], [1, 57], [14, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [8, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N1 : CertifiedPrimeIdeal' SI71N1 71 where
  n := 2
  hpos := by decide
  P := [53, 57, 1]
  hirr := P71P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-17695, -14883, -760, 6167, 36298]
  a := ![129, 120, 11, -51, -302]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-16907, -16469, -760, 6167, 36298]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N1 B_one_repr
lemma NI71N1 : Nat.card (O ⧸ I71N1) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-1275, -1704, -285, 687, 4036]] ![![-203, -249, -18, 79, 504]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-369, -24, -18, 56, 382]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![-369, -24, -18, 56, 382]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![30, 15, 52, 1, 0], ![4, 5, 8, 0, 1]] where
  M :=![![![-369, -24, -18, 56, 382], ![1176, 1255, 264, -542, -3306], ![-428, -3588, -269, 1122, 5786], ![-14152, -8298, -1530, 4373, 26554], ![2652, 1794, 354, -896, -5465]]]
  hmulB := by decide  
  f := ![![![7, -588, -18, 164, 1134]], ![![3872, 5191, 336, -1686, -10706]], ![![-13148, -22764, -1301, 7162, 46274]], ![![-7942, -14397, -806, 4507, 29200]], ![![-1272, -2335, -130, 730, 4733]]]
  g := ![![![-49, -38, -82, 56, 382], ![420, 355, 752, -542, -3306], ![-784, -676, -1437, 1122, 5786], ![-3446, -2831, -6046, 4373, 26554], ![704, 583, 1242, -896, -5465]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [40, 9, 48, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 0, 24], [6, 72, 49], [0, 1]]
 g := ![![[5, 36, 3], [42, 19], [46, 69], [68, 26, 2], [25, 1], []], ![[0, 66, 34, 25], [45, 27], [70, 69], [57, 28, 28, 48], [19, 1], [19, 65]], ![[68, 8, 7, 27], [18, 55], [], [51, 34, 2, 27], [], [67, 65]]]
 h' := ![![[19, 0, 24], [68, 46, 21], [54, 38, 26], [54, 0, 19], [22, 27, 32], [0, 0, 1], [0, 1]], ![[6, 72, 49], [9, 63, 61], [38, 5, 10], [65, 57, 54], [31, 23, 32], [39, 3, 72], [19, 0, 24]], ![[0, 1], [8, 37, 64], [12, 30, 37], [42, 16], [37, 23, 9], [57, 70], [6, 72, 49]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59, 13], []]
 b := ![[], [18, 34, 39], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [40, 9, 48, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6594554578, -6532602828, -368953906, 2549341012, 15212999568]
  a := ![-1401, -1316, -119, 552, 3280]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1971599770, -1655311176, -3488201138, 2549341012, 15212999568]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 389017 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2803, -4489, -266, 1425, 9162]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-2803, -4489, -266, 1425, 9162]] 
 ![![73, 0, 0, 0, 0], ![48, 1, 0, 0, 0], ![32, 0, 1, 0, 0], ![19, 0, 0, 1, 0], ![71, 0, 0, 0, 1]] where
  M :=![![![-2803, -4489, -266, 1425, 9162], ![14286, 22883, 1356, -7264, -46704], ![-72832, -116658, -6913, 37032, 238096], ![222040, 355665, 21075, -112901, -725896], ![-37792, -60535, -3587, 19216, 123549]]]
  hmulB := by decide  
  f := ![![![-819, -452, -25, 209, 1166]], ![![-578, -325, -18, 150, 836]], ![![-556, -334, -21, 156, 872]], ![![-535, -311, -16, 152, 846]], ![![-775, -429, -24, 197, 1099]]]
  g := ![![![-6252, -4489, -266, 1425, 9162], ![31870, 22883, 1356, -7264, -46704], ![-162472, -116658, -6913, 37032, 238096], ![495335, 355665, 21075, -112901, -725896], ![-84307, -60535, -3587, 19216, 123549]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1

def I73N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1649, 926, 103, -359, -2080]] i)))

def SI73N2: IdealEqSpanCertificate' Table ![![1649, 926, 103, -359, -2080]] 
 ![![73, 0, 0, 0, 0], ![68, 1, 0, 0, 0], ![48, 0, 1, 0, 0], ![23, 0, 0, 1, 0], ![58, 0, 0, 0, 1]] where
  M :=![![![1649, 926, 103, -359, -2080], ![2790, 1567, 174, -608, -3522], ![4744, 2670, 295, -1038, -6010], ![1718, 975, 105, -385, -2222], ![1742, 977, 109, -378, -2191]]]
  hmulB := by decide  
  f := ![![![-115, 37, -10, 9, 68]], ![![-102, 39, -8, 6, 50]], ![![-44, 42, -5, -2, -10]], ![![-145, -106, -17, 48, 306]], ![![-70, 53, -5, -2, -3]]]
  g := ![![![858, 926, 103, -359, -2080], ![1454, 1567, 174, -608, -3522], ![2486, 2670, 295, -1038, -6010], ![933, 975, 105, -385, -2222], ![902, 977, 109, -378, -2191]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N2 : Nat.card (O ⧸ I73N2) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N2)

lemma isPrimeI73N2 : Ideal.IsPrime I73N2 := prime_ideal_of_norm_prime hp73.out _ NI73N2
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![-369, -24, -18, 56, 382]] ![![-2803, -4489, -266, 1425, 9162]]
  ![![115, -37, 10, -9, -68]] where
 M := ![![![115, -37, 10, -9, -68]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI73N1 : IdealMulLeCertificate' Table 
  ![![115, -37, 10, -9, -68]] ![![1649, 926, 103, -359, -2080]]
  ![![73, 0, 0, 0, 0]] where
 M := ![![![-73, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2685, 1549, 169, -596, -3466]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![2685, 1549, 169, -596, -3466]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![16, 21, 1, 0, 0], ![61, 14, 0, 1, 0], ![55, 34, 0, 0, 1]] where
  M :=![![![2685, 1549, 169, -596, -3466], ![4272, 2189, 260, -872, -4986], ![8632, 5928, 571, -2186, -12994], ![-422, -3498, -132, 993, 6782], ![3334, 2428, 226, -880, -5273]]]
  hmulB := by decide  
  f := ![![![-261, 665, 63, -166, -826]], ![![5092, 3503, 740, -1744, -10726]], ![![1252, 905, 187, -442, -2708]], ![![379, 1065, 151, -373, -2108]], ![![2089, 2001, 371, -886, -5319]]]
  g := ![![![2873, 1572, 169, -596, -3466], ![4146, 2259, 260, -872, -4986], ![10728, 5903, 571, -2186, -12994], ![-5467, -3104, -132, 993, 6782], ![4347, 2396, 226, -880, -5273]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [37, 63, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 78], [0, 1]]
 g := ![![[38, 9], [65, 10], [53, 50], [3, 42], [19], [1]], ![[24, 70], [67, 69], [63, 29], [43, 37], [19], [1]]]
 h' := ![![[16, 78], [44, 76], [14, 22], [47, 45], [34, 68], [42, 16], [0, 1]], ![[0, 1], [75, 3], [50, 57], [56, 34], [16, 11], [61, 63], [16, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38]]
 b := ![[], [6, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [37, 63, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3708371, -3572349, -226438, 1412603, 8463226]
  a := ![1656, 1578, 142, -652, -3877]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6983944, -3877763, -226438, 1412603, 8463226]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-893, -394, -59, 147, 844]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![-893, -394, -59, 147, 844]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![9, 48, 1, 0, 0], ![56, 53, 0, 1, 0], ![72, 34, 0, 0, 1]] where
  M :=![![![-893, -394, -59, 147, 844], ![-1358, -1075, -126, 300, 1958], ![3824, 4866, 173, -1990, -11786], ![2234, -4335, -321, 321, 4714], ![-966, 503, -5, -22, -541]]]
  hmulB := by decide  
  f := ![![![-6623, -10403, -1666, 4037, 23488]], ![![-28626, -2953, -2160, 4742, 33030]], ![![-16645, -1359, -1213, 2649, 18622]], ![![-23538, -11070, -2813, 6513, 41248]], ![![-18572, -10497, -2431, 5672, 35419]]]
  g := ![![![-878, -431, -59, 147, 844], ![-2000, -981, -126, 300, 1958], ![12181, 6364, 173, -1990, -11786], ![-4459, -2104, -321, 321, 4714], ![497, 257, -5, -22, -541]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P1 : CertificateIrreducibleZModOfList' 79 2 2 6 [48, 55, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 78], [0, 1]]
 g := ![![[39, 42], [2, 26], [56, 8], [18, 38], [23], [1]], ![[20, 37], [73, 53], [11, 71], [61, 41], [23], [1]]]
 h' := ![![[24, 78], [62, 68], [77, 37], [5, 18], [15, 65], [31, 24], [0, 1]], ![[0, 1], [35, 11], [17, 42], [42, 61], [74, 14], [54, 55], [24, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65]]
 b := ![[], [5, 72]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N1 : CertifiedPrimeIdeal' SI79N1 79 where
  n := 2
  hpos := by decide
  P := [48, 55, 1]
  hirr := P79P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-57962, -89046, -4452, 27918, 181886]
  a := ![-170, -162, -16, 62, 398]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-185786, -95432, -4452, 27918, 181886]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N1 B_one_repr
lemma NI79N1 : Nat.card (O ⧸ I79N1) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N1

def I79N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2251, -4672, -243, 1453, 9462]] i)))

def SI79N2: IdealEqSpanCertificate' Table ![![-2251, -4672, -243, 1453, 9462]] 
 ![![79, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![58, 0, 1, 0, 0], ![76, 0, 0, 1, 0], ![33, 0, 0, 0, 1]] where
  M :=![![![-2251, -4672, -243, 1453, 9462], ![17926, 27299, 1676, -8670, -55660], ![-84580, -136014, -7955, 43392, 278560], ![253810, 410805, 24393, -129795, -836032], ![-42318, -69481, -4083, 21956, 141467]]]
  hmulB := by decide  
  f := ![![![-305021, -450275, -73268, 177203, 1034734]], ![![-53192, -57495, -10254, 24542, 146164]], ![![-157670, -262004, -41383, 100446, 582556]], ![![-285828, -512195, -79487, 193351, 1116764]], ![![-134999, -175796, -29609, 71323, 419665]]]
  g := ![![![-4609, -4672, -243, 1453, 9462], ![27132, 27299, 1676, -8670, -55660], ![-136118, -136014, -7955, 43392, 278560], ![407398, 410805, 24393, -129795, -836032], ![-68959, -69481, -4083, 21956, 141467]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N2 : Nat.card (O ⧸ I79N2) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N2)

lemma isPrimeI79N2 : Ideal.IsPrime I79N2 := prime_ideal_of_norm_prime hp79.out _ NI79N2
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![2685, 1549, 169, -596, -3466]] ![![-893, -394, -59, 147, 844]]
  ![![-1838299, -1060449, -115706, 408021, 2372810]] where
 M := ![![![-1838299, -1060449, -115706, 408021, 2372810]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI79N1 : IdealMulLeCertificate' Table 
  ![![-1838299, -1060449, -115706, 408021, 2372810]] ![![-2251, -4672, -243, 1453, 9462]]
  ![![79, 0, 0, 0, 0]] where
 M := ![![![-1937947815, -1871173144, -145491614, 640660296, 3955242440]]]
 hmul := by decide  
 g := ![![![![-24530985, -23685736, -1841666, 8109624, 50066360]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1, I79N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
    exact isPrimeI79N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0 ⊙ MulI79N1)
instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1549, 1102, 104, -402, -2402]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![1549, 1102, 104, -402, -2402]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![22, 4, 43, 1, 0], ![70, 44, 75, 0, 1]] where
  M :=![![![1549, 1102, 104, -402, -2402], ![1084, -583, 30, 98, 938], ![9604, 11472, 791, -3790, -23842], ![-16440, -27732, -1602, 8747, 56418], ![4424, 5632, 374, -1842, -11649]]]
  hmulB := by decide  
  f := ![![![615, 406, 20, -198, -1094]], ![![3028, 2059, 114, -994, -5506]], ![![14812, 9888, 565, -4810, -26710]], ![![8314, 5548, 315, -2699, -14984]], ![![15482, 10352, 587, -5032, -27931]]]
  g := ![![![2151, 1306, 2380, -402, -2402], ![-804, -509, -898, 98, 938], ![21228, 12960, 23517, -3790, -23842], ![-50098, -30664, -55531, 8747, 56418], ![10366, 6332, 11485, -1842, -11649]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [22, 13, 58, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 26, 56], [16, 56, 27], [0, 1]]
 g := ![![[26, 11, 81], [79, 4, 27], [2, 21], [31, 3], [31, 25, 1], []], ![[56, 34, 28, 18], [14, 61, 77, 22], [25, 27], [44, 75], [81, 15, 10, 71], [55, 65]], ![[67, 8, 23, 41], [80, 55, 0, 59], [12, 4], [23, 25], [10, 50, 21, 75], [1, 65]]]
 h' := ![![[9, 26, 56], [5, 75, 74], [51, 65, 44], [57, 58, 42], [65, 43, 13], [0, 0, 1], [0, 1]], ![[16, 56, 27], [51, 28, 44], [13, 29, 45], [56, 47, 39], [51, 67, 65], [33, 66, 56], [9, 26, 56]], ![[0, 1], [12, 63, 48], [16, 72, 77], [23, 61, 2], [60, 56, 5], [68, 17, 26], [16, 56, 27]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52, 64], []]
 b := ![[], [39, 29, 70], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [22, 13, 58, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-50715077258, -48685134744, -2806382328, 19336033956, 114690927180]
  a := ![-2743, -2614, -230, 1086, 6422]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-102463526830, -62318434536, -113687655192, 19336033956, 114690927180]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 571787 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![615, 406, 20, -198, -1094]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![615, 406, 20, -198, -1094]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![64, 81, 1, 0, 0], ![32, 31, 0, 1, 0], ![48, 48, 0, 0, 1]] where
  M :=![![![615, 406, 20, -198, -1094], ![3028, 2059, 114, -994, -5506], ![14812, 9888, 565, -4810, -26710], ![27504, 18132, 954, -8855, -49050], ![-2176, -1400, -70, 690, 3821]]]
  hmulB := by decide  
  f := ![![![1549, 1102, 104, -402, -2402]], ![![1084, -583, 30, 98, 938]], ![![2368, 419, 119, -260, -1224]], ![![804, -127, 32, -13, 104]], ![![1576, 368, 82, -198, -987]]]
  g := ![![![701, 692, 20, -198, -1094], ![3516, 3469, 114, -994, -5506], ![17044, 16811, 565, -4810, -26710], ![31376, 30961, 954, -8855, -49050], ![-2448, -2416, -70, 690, 3821]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P1 : CertificateIrreducibleZModOfList' 83 2 2 6 [38, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [65, 82], [0, 1]]
 g := ![![[66, 59], [6, 28], [49], [3], [18, 75], [1]], ![[0, 24], [0, 55], [49], [3], [79, 8], [1]]]
 h' := ![![[65, 82], [21, 15], [5, 51], [37, 7], [63, 13], [45, 65], [0, 1]], ![[0, 1], [0, 68], [0, 32], [77, 76], [78, 70], [37, 18], [65, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [80, 55]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N1 : CertifiedPrimeIdeal' SI83N1 83 where
  n := 2
  hpos := by decide
  P := [38, 18, 1]
  hirr := P83P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-24463, -28980, -1813, 10382, 64300]
  a := ![-129, -126, -11, 50, 302]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-40085, -39643, -1813, 10382, 64300]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N1 B_one_repr
lemma NI83N1 : Nat.card (O ⧸ I83N1) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![1549, 1102, 104, -402, -2402]] ![![615, 406, 20, -198, -1094]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![32747, 52450, 3108, -16650, -107050]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![32747, 52450, 3108, -16650, -107050]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![41, 33, 25, 1, 0], ![48, 31, 57, 0, 1]] where
  M :=![![![32747, 52450, 3108, -16650, -107050], ![-166900, -267353, -15842, 84866, 545650], ![850980, 1363008, 80765, -432678, -2781882], ![-2594208, -4155444, -246234, 1319081, 8481066], ![441552, 707272, 41910, -224514, -1443515]]]
  hmulB := by decide  
  f := ![![![531, 334, 40, -130, -754]], ![![988, 479, 62, -206, -1222]], ![![804, 144, -35, -30, -114]], ![![843, 385, 33, -149, -856]], ![![1152, 441, 21, -162, -911]]]
  g := ![![![65773, 44050, 73272, -16650, -107050], ![-335254, -224529, -373478, 84866, 545650], ![1709226, 1144716, 1904101, -432678, -2781882], ![-5210873, -3489867, -5804989, 1319081, 8481066], ![886914, 593991, 988035, -224514, -1443515]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [12, 83, 21, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 60, 51], [58, 28, 38], [0, 1]]
 g := ![![[14, 64, 85], [22, 71], [26, 4], [39, 17, 4], [2, 68, 1], []], ![[53, 14, 65, 54], [15, 39], [33, 11], [7, 56, 72, 61], [86, 54, 50, 23], [4, 20]], ![[4, 69, 43, 48], [21, 81], [47, 64], [35, 0, 1, 86], [66, 23, 67, 7], [17, 20]]]
 h' := ![![[10, 60, 51], [11, 81, 68], [39, 0, 31], [66, 72, 2], [65, 86, 87], [0, 0, 1], [0, 1]], ![[58, 28, 38], [85, 38, 72], [49, 66, 67], [0, 58, 79], [20, 77, 58], [52, 5, 28], [10, 60, 51]], ![[0, 1], [26, 59, 38], [10, 23, 80], [60, 48, 8], [68, 15, 33], [45, 84, 60], [58, 28, 38]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [67, 7], []]
 b := ![[], [71, 49, 40], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [12, 83, 21, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-12828023582, -13647265059, -781771614, 5150662396, 31079244167]
  a := ![-1738, -1656, -145, 684, 4069]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-19278751706, -12888490936, -21360283697, 5150662396, 31079244167]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 704969 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![531, 334, 40, -130, -754]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![531, 334, 40, -130, -754]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![6, 40, 1, 0, 0], ![55, 73, 0, 1, 0], ![75, 50, 0, 0, 1]] where
  M :=![![![531, 334, 40, -130, -754], ![988, 479, 62, -206, -1222], ![804, 144, -35, -30, -114], ![552, 1164, 126, -383, -2094], ![584, 160, 22, -82, -507]]]
  hmulB := by decide  
  f := ![![![32747, 52450, 3108, -16650, -107050]], ![![-166900, -267353, -15842, 84866, 545650]], ![![-63242, -101308, -6003, 32158, 206762]], ![![-145807, -233567, -13840, 74141, 476694]], ![![-61207, -98052, -5810, 31124, 200115]]]
  g := ![![![719, 516, 40, -130, -754], ![1164, 833, 62, -206, -1222], ![126, 106, -35, -30, -114], ![1999, 1447, 126, -383, -2094], ![483, 344, 22, -82, -507]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P1 : CertificateIrreducibleZModOfList' 89 2 2 6 [43, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [57, 88], [0, 1]]
 g := ![![[38, 57], [53], [71], [85, 17], [66, 45], [1]], ![[83, 32], [53], [71], [75, 72], [50, 44], [1]]]
 h' := ![![[57, 88], [27, 18], [9, 26], [83, 31], [10, 27], [46, 57], [0, 1]], ![[0, 1], [74, 71], [67, 63], [70, 58], [36, 62], [2, 32], [57, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61]]
 b := ![[], [43, 75]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N1 : CertifiedPrimeIdeal' SI89N1 89 where
  n := 2
  hpos := by decide
  P := [43, 32, 1]
  hirr := P89P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1605960, -1532468, -99331, 610154, 3648628]
  a := ![-1061, -1010, -91, 418, 2484]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3463096, -2522830, -99331, 610154, 3648628]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N1 B_one_repr
lemma NI89N1 : Nat.card (O ⧸ I89N1) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![32747, 52450, 3108, -16650, -107050]] ![![531, 334, 40, -130, -754]]
  ![![89, 0, 0, 0, 0]] where
 M := ![![![89, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0)
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


def P97P0 : CertificateIrreducibleZModOfList' 97 5 2 6 [92, 23, 79, 19, 76, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [31, 68, 14, 20, 27], [47, 32, 75, 93, 2], [78, 10, 95, 24, 17], [59, 83, 10, 57, 51], [0, 1]]
 g := ![![[45, 5, 72, 15, 66], [39, 83, 46, 88], [29, 64, 14, 2], [31, 60, 17, 89], [21, 1], []], ![[80, 13, 63, 68, 90, 53, 27, 88], [76, 64, 30, 65], [3, 30, 14, 18], [8, 54, 51, 33], [49, 50, 32, 2], [5, 33, 33, 55, 40, 34, 19, 89]], ![[40, 8, 65, 74, 73, 24, 69, 50], [63, 40, 66, 53], [8, 27, 39, 91], [8, 76, 5, 2], [73, 94, 78, 64], [51, 88, 19, 0, 44, 66, 23, 8]], ![[78, 3, 92, 80, 71, 30, 3, 68], [19, 64, 86, 25], [91, 0, 4, 11], [10, 51, 95, 9], [30, 33, 95, 91], [20, 37, 21, 33, 56, 85, 15, 63]], ![[91, 47, 6, 59, 82, 33, 50, 30], [3, 88, 3, 33], [94, 16, 65, 8], [20, 25, 27, 50], [41, 95, 83, 27], [72, 24, 56, 34, 78, 0, 51, 52]]]
 h' := ![![[31, 68, 14, 20, 27], [37, 79, 4, 81, 58], [91, 26, 15, 21, 31], [25, 87, 45, 1, 83], [8, 7, 64, 7, 34], [0, 0, 0, 1], [0, 1]], ![[47, 32, 75, 93, 2], [80, 45, 93, 15, 56], [31, 66, 76, 18, 68], [4, 83, 80, 69, 55], [62, 43, 16, 34, 79], [37, 57, 22, 62, 14], [31, 68, 14, 20, 27]], ![[78, 10, 95, 24, 17], [90, 37, 59, 19, 5], [58, 83, 5, 79, 21], [42, 57, 4, 58, 24], [83, 50, 57, 16, 14], [94, 65, 4, 67, 89], [47, 32, 75, 93, 2]], ![[59, 83, 10, 57, 51], [71, 62, 10, 78, 95], [49, 82, 0, 73, 92], [46, 50, 75, 7, 60], [44, 8, 49, 48, 94], [31, 79, 90, 43, 24], [78, 10, 95, 24, 17]], ![[0, 1], [59, 68, 28, 1, 77], [74, 34, 1, 3, 79], [34, 14, 87, 59, 69], [15, 86, 8, 89, 70], [2, 90, 78, 21, 67], [59, 83, 10, 57, 51]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24, 7, 62, 96], [], [], []]
 b := ![[], [79, 41, 29, 77, 18], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 5
  hpos := by decide
  P := [92, 23, 79, 19, 76, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11563749772614812, -11876353030342533, -680457712154241, 4570564712526560, 27341697249226018]
  a := ![-1099, -1047, -93, 435, 2573]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-119213915181596, -122436629178789, -7015027960353, 47119223840480, 281873167517794]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1077, -664, -148, 346, 2146]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![-1077, -664, -148, 346, 2146]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![26, 14, 95, 1, 0], ![94, 14, 65, 0, 1]] where
  M :=![![![-1077, -664, -148, 346, 2146], ![1268, 2959, 436, -1066, -6074], ![11148, 3888, 1163, -2670, -17310], ![-20964, -22440, -3996, 9593, 57210], ![3880, 4856, 824, -1988, -11733]]]
  hmulB := by decide  
  f := ![![![1543, 1016, 60, -486, -2702]], ![![6964, 4619, 260, -2234, -12394]], ![![32748, 21840, 1207, -10590, -58734]], ![![32774, 21850, 1209, -10593, -58752]], ![![23430, 15610, 867, -7562, -41947]]]
  g := ![![![-2097, -352, -1708, 346, 2146], ![5940, 1019, 4916, -1066, -6074], ![16908, 2808, 13663, -2670, -17310], ![-55922, -9482, -45881, 9593, 57210], ![11470, 1950, 9429, -1988, -11733]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [63, 66, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [90, 34, 68], [6, 66, 33], [0, 1]]
 g := ![![[13, 38, 87], [23, 14], [2, 35, 1], [50, 96], [30, 25], [1]], ![[44, 27, 62, 21], [51, 79], [75, 2, 44, 96], [34, 56], [82, 92], [67, 46, 85, 19]], ![[51, 31, 33, 45], [39, 84], [56, 19, 48, 22], [91, 81], [53, 19], [19, 18, 82, 82]]]
 h' := ![![[90, 34, 68], [85, 5, 17], [76, 63, 32], [28, 81, 100], [59, 14, 55], [38, 35, 96], [0, 1]], ![[6, 66, 33], [52, 49, 48], [72, 19, 33], [15, 46, 89], [95, 37, 37], [3, 73, 30], [90, 34, 68]], ![[0, 1], [92, 47, 36], [78, 19, 36], [46, 75, 13], [27, 50, 9], [29, 94, 76], [6, 66, 33]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [92, 31], []]
 b := ![[], [31, 88, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [63, 66, 5, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![17586943819, 19375707017, 1109615051, -7199279514, -43639999900]
  a := ![1838, 1754, 146, -722, -4303]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![42642853483, 7238867513, 34867734281, -7199279514, -43639999900]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 1030301 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1543, -1016, -60, 486, 2702]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![-1543, -1016, -60, 486, 2702]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![25, 13, 1, 0, 0], ![27, 73, 0, 1, 0], ![62, 59, 0, 0, 1]] where
  M :=![![![-1543, -1016, -60, 486, 2702], ![-6964, -4619, -260, 2234, 12394], ![-32748, -21840, -1207, 10590, 58734], ![-61500, -40968, -2244, 19931, 110454], ![4728, 3160, 168, -1548, -8567]]]
  hmulB := by decide  
  f := ![![![1077, 664, 148, -346, -2146]], ![![-1268, -2959, -436, 1066, 6074]], ![![-7, -255, -31, 78, 422]], ![![-421, -1739, -236, 583, 3250]], ![![-118, -1369, -172, 430, 2347]]]
  g := ![![![-1789, -1932, -60, 486, 2702], ![-8210, -8867, -260, 2234, 12394], ![-38911, -42025, -1207, 10590, 58734], ![-73185, -79045, -2244, 19931, 110454], ![5678, 6133, 168, -1548, -8567]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P1 : CertificateIrreducibleZModOfList' 101 2 2 6 [63, 30, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [71, 100], [0, 1]]
 g := ![![[63, 45], [17], [77, 87], [96], [33], [71, 1]], ![[26, 56], [17], [93, 14], [96], [33], [41, 100]]]
 h' := ![![[71, 100], [49, 34], [98, 44], [82, 17], [75, 55], [72, 29], [0, 1]], ![[0, 1], [39, 67], [91, 57], [77, 84], [41, 46], [10, 72], [71, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48]]
 b := ![[], [57, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N1 : CertifiedPrimeIdeal' SI101N1 101 where
  n := 2
  hpos := by decide
  P := [63, 30, 1]
  hirr := P101P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1926552, -1857531, -115585, 735392, 4393012]
  a := ![1149, 1098, 95, -453, -2690]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2883755, -3101250, -115585, 735392, 4393012]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N1 B_one_repr
lemma NI101N1 : Nat.card (O ⧸ I101N1) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![-1077, -664, -148, 346, 2146]] ![![-1543, -1016, -60, 486, 2702]]
  ![![101, 0, 0, 0, 0]] where
 M := ![![![-101, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC101 : ContainsPrimesAboveP 101 ![I101N0, I101N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
    exact isPrimeI101N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 101 (by decide) (𝕀 ⊙ MulI101N0)
instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0, 0, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0, 0, 0]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![0, 0, 0, 103, 0], ![0, 0, 0, 0, 103]] where
  M :=![![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![0, 0, 0, 103, 0], ![0, 0, 0, 0, 103]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 5 2 6 [37, 36, 19, 99, 90, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [44, 89, 98, 85, 3], [5, 23, 26, 6, 18], [46, 12, 69, 91, 64], [21, 81, 13, 24, 18], [0, 1]]
 g := ![![[35, 87, 11, 70, 72], [75, 18, 70, 97, 38], [4, 95, 14, 73, 56], [9, 12, 31, 59], [13, 1], []], ![[28, 53, 66, 74, 52, 68, 24, 48], [4, 49, 61, 55, 46, 93, 32, 6], [24, 60, 3, 90, 68, 21, 35, 87], [74, 54, 15, 91], [91, 93, 34, 30], [52, 5, 72, 51, 35, 1, 71, 27]], ![[36, 101, 82, 15, 16, 13, 86, 28], [36, 6, 9, 102, 42, 72, 46, 79], [92, 4, 9, 70, 41, 12, 96, 61], [11, 37, 38, 56], [76, 0, 87, 36], [8, 102, 85, 54, 19, 83, 72, 64]], ![[11, 95, 59, 75, 87, 35, 94, 58], [46, 84, 68, 28, 16, 91, 78, 100], [55, 67, 27, 65, 29, 56, 2, 50], [33, 64, 39, 64], [23, 85, 98, 29], [69, 2, 7, 100, 3, 37, 54, 9]], ![[2, 90, 88, 70, 57, 61, 30, 91], [15, 63, 73, 44, 59, 0, 101, 59], [20, 26, 64, 40, 68, 43, 10, 41], [100, 69, 77, 26], [94, 48, 58, 72], [85, 65, 71, 33, 26, 48, 58, 64]]]
 h' := ![![[44, 89, 98, 85, 3], [6, 101, 4, 15, 81], [58, 50, 76, 42, 48], [102, 15, 15, 97, 46], [34, 10, 26, 33, 70], [0, 0, 0, 1], [0, 1]], ![[5, 23, 26, 6, 18], [51, 8, 41, 13, 99], [96, 38, 20, 37, 38], [61, 35, 72, 16, 82], [92, 44, 43, 12, 20], [36, 61, 4, 41, 66], [44, 89, 98, 85, 3]], ![[46, 12, 69, 91, 64], [96, 100, 9, 42, 42], [70, 17, 31, 35, 41], [18, 38, 85, 98, 49], [61, 19, 43, 59, 57], [35, 32, 32, 6, 97], [5, 23, 26, 6, 18]], ![[21, 81, 13, 24, 18], [22, 39, 34, 92, 29], [41, 93, 36, 83, 76], [81, 91, 96, 91, 2], [90, 38, 50, 47, 8], [23, 76, 55, 89, 21], [46, 12, 69, 91, 64]], ![[0, 1], [59, 61, 15, 44, 58], [89, 8, 43, 9, 3], [8, 27, 41, 7, 27], [0, 95, 44, 55, 51], [39, 37, 12, 69, 22], [21, 81, 13, 24, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29, 7, 72, 13], [], [], []]
 b := ![[], [88, 87, 3, 75, 30], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 5
  hpos := by decide
  P := [37, 36, 19, 99, 90, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-150668853477094514, -152224987681028268, -8711665460032176, 59057715468797520, 352292430531492768]
  a := ![-1823, -1737, -153, 722, 4268]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1462804402690238, -1477912501757556, -84579276310992, 573375878337840, 3420314859529056]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 11592740743 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def PBC103 : ContainsPrimesAboveP 103 ![I103N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![103, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 103 (by decide) 𝕀



lemma PB953I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB953I2 : PrimesBelowBoundCertificateInterval O 61 103 953 where
  m := 9
  g := ![3, 2, 3, 3, 2, 2, 1, 2, 1]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB953I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0, I67N1, I67N2]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1, I73N2]
    · exact ![I79N0, I79N1, I79N2]
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0]
    · exact ![I101N0, I101N1]
    · exact ![I103N0]
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
    · exact ![300763, 67, 67]
    · exact ![357911, 5041]
    · exact ![389017, 73, 73]
    · exact ![6241, 6241, 79]
    · exact ![571787, 6889]
    · exact ![704969, 7921]
    · exact ![8587340257]
    · exact ![1030301, 10201]
    · exact ![11592740743]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
      exact NI67N2
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
      exact NI79N2
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
  β := ![I67N1, I67N2, I73N1, I73N2, I79N2]
  Il := ![[I67N1, I67N2], [], [I73N1, I73N2], [I79N2], [], [], [], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
