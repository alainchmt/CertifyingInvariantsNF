
import IdealArithmetic.Examples.NF5_3_729000000_3.RI5_3_729000000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 11, -32, -6, -24]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![11, 11, -32, -6, -24]] 
 ![![157, 0, 0, 0, 0], ![0, 157, 0, 0, 0], ![129, 52, 1, 0, 0], ![43, 30, 0, 1, 0], ![85, 47, 0, 0, 1]] where
  M :=![![![11, 11, -32, -6, -24], ![96, 15, -122, -28, -84], ![168, 43, -237, -52, -168], ![288, 74, -400, -87, -282], ![252, 66, -350, -77, -247]]]
  hmulB := by decide  
  f := ![![![-25, -17, 2, 6, 0]], ![![0, -11, -34, -8, 36]], ![![-21, -18, -9, 2, 12]], ![![-7, -7, -6, 1, 6]], ![![-13, -12, -10, 1, 11]]]
  g := ![![![41, 19, -32, -6, -24], ![154, 71, -122, -28, -84], ![301, 139, -237, -52, -168], ![507, 234, -400, -87, -282], ![444, 205, -350, -77, -247]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [86, 51, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [106, 156], [0, 1]]
 g := ![![[101, 42], [27], [98, 113], [119, 49], [4, 36], [89], [1]], ![[0, 115], [27], [144, 44], [132, 108], [52, 121], [89], [1]]]
 h' := ![![[106, 156], [21, 102], [50, 98], [128, 37], [127, 150], [56, 151], [71, 106], [0, 1]], ![[0, 1], [0, 55], [76, 59], [125, 120], [13, 7], [48, 6], [3, 51], [106, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [125]]
 b := ![[], [63, 141]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [86, 51, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3850, -2461, 6342, -693, 926]
  a := ![0, -8, -3, 2, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5547, -2261, 6342, -693, 926]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 60, -146, 47, 18]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![73, 60, -146, 47, 18]] 
 ![![157, 0, 0, 0, 0], ![0, 157, 0, 0, 0], ![133, 119, 1, 0, 0], ![30, 36, 0, 1, 0], ![141, 107, 0, 0, 1]] where
  M :=![![![73, 60, -146, 47, 18], ![-72, -15, 228, -404, 318], ![-636, -644, 939, 473, -894], ![1824, 1526, -3440, 1115, 366], ![388, 494, -348, -1073, 1253]]]
  hmulB := by decide  
  f := ![![![194797, -117394, 8294, -17635, 38064]], ![![-152256, 91693, -6404, 13794, -29682]], ![![49993, -30177, 2189, -4518, 9822]], ![![2646, -1610, 132, -237, 534]], ![![71569, -43175, 3102, -6472, 14033]]]
  g := ![![![99, 88, -146, 47, 18], ![-402, -297, 228, -404, 318], ![-87, -215, 939, 473, -894], ![2384, 2112, -3440, 1115, 366], ![-623, -341, -348, -1073, 1253]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P1 : CertificateIrreducibleZModOfList' 157 2 2 7 [96, 124, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 156], [0, 1]]
 g := ![![[34, 120], [35], [61, 144], [132, 39], [36, 3], [147], [1]], ![[69, 37], [35], [103, 13], [6, 118], [135, 154], [147], [1]]]
 h' := ![![[33, 156], [105, 77], [110, 105], [45, 145], [155, 14], [128, 85], [61, 33], [0, 1]], ![[0, 1], [134, 80], [121, 52], [120, 12], [146, 143], [107, 72], [51, 124], [33, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55]]
 b := ![[], [135, 106]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N1 : CertifiedPrimeIdeal' SI157N1 157 where
  n := 2
  hpos := by decide
  P := [96, 124, 1]
  hirr := P157P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1941, 10489, -29940, 81235, -2531]
  a := ![3, -61, 2, -69, 11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![12126, 5858, -29940, 81235, -2531]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N1 B_one_repr
lemma NI157N1 : Nat.card (O ⧸ I157N1) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N1

def I157N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11761, 7089, -500, 1065, -2298]] i)))

def SI157N2: IdealEqSpanCertificate' Table ![![-11761, 7089, -500, 1065, -2298]] 
 ![![157, 0, 0, 0, 0], ![129, 1, 0, 0, 0], ![79, 0, 1, 0, 0], ![21, 0, 0, 1, 0], ![62, 0, 0, 0, 1]] where
  M :=![![![-11761, 7089, -500, 1065, -2298], ![9192, -5535, 390, -832, 1794], ![-3588, 2165, -153, 325, -702], ![-3192, 1924, -136, 289, -624], ![-3712, 2236, -158, 336, -725]]]
  hmulB := by decide  
  f := ![![![107, 91, -154, -1, 36]], ![![87, 74, -124, -3, 30]], ![![53, 44, -77, 4, 12]], ![![27, 23, -42, 0, 12]], ![![42, 36, -58, -8, 19]]]
  g := ![![![-4883, 7089, -500, 1065, -2298], ![3813, -5535, 390, -832, 1794], ![-1491, 2165, -153, 325, -702], ![-1325, 1924, -136, 289, -624], ![-1540, 2236, -158, 336, -725]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N2 : Nat.card (O ⧸ I157N2) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N2)

lemma isPrimeI157N2 : Ideal.IsPrime I157N2 := prime_ideal_of_norm_prime hp157.out _ NI157N2
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![11, 11, -32, -6, -24]] ![![73, 60, -146, 47, 18]]
  ![![107, 91, -154, -1, 36]] where
 M := ![![![107, 91, -154, -1, 36]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI157N1 : IdealMulLeCertificate' Table 
  ![![107, 91, -154, -1, 36]] ![![-11761, 7089, -500, 1065, -2298]]
  ![![157, 0, 0, 0, 0]] where
 M := ![![![157, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC157 : ContainsPrimesAboveP 157 ![I157N0, I157N1, I157N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
    exact isPrimeI157N1
    exact isPrimeI157N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 157 (by decide) (𝕀 ⊙ MulI157N0 ⊙ MulI157N1)
instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![85, -50, 4, -7, 18]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![85, -50, 4, -7, 18]] 
 ![![163, 0, 0, 0, 0], ![0, 163, 0, 0, 0], ![0, 0, 163, 0, 0], ![39, 46, 136, 1, 0], ![38, 160, 35, 0, 1]] where
  M :=![![![85, -50, 4, -7, 18], ![-72, 39, 8, 4, -6], ![12, -22, 21, 7, 6], ![24, -2, -8, 9, 30], ![12, -18, 24, -9, 31]]]
  hmulB := by decide  
  f := ![![![31, 32, -4, 1, -12]], ![![48, 53, -8, 2, -18]], ![![36, 40, -1, -1, -12]], ![![51, 56, -4, 0, -18]], ![![62, 68, -9, 2, -23]]]
  g := ![![![-2, -16, 2, -7, 18], ![0, 5, -2, 4, -6], ![-3, -8, -7, 7, 6], ![-9, -32, -14, 9, 30], ![-5, -28, 1, -9, 31]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [31, 8, 139, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [149, 118, 147], [38, 44, 16], [0, 1]]
 g := ![![[32, 144, 34], [122, 159, 161], [85, 46], [75, 115], [42, 56], [79, 24, 1], []], ![[54, 153, 109, 75], [40, 122, 57, 137], [71, 64], [44, 47], [87, 38], [25, 55, 23, 157], [86, 93]], ![[127, 53, 64, 160], [16, 67, 20, 95], [136, 87], [104, 104], [3, 100], [0, 61, 160, 126], [54, 93]]]
 h' := ![![[149, 118, 147], [130, 97, 94], [42, 35, 145], [118, 7, 32], [18, 134, 21], [159, 91, 43], [0, 0, 1], [0, 1]], ![[38, 44, 16], [8, 81, 139], [2, 88, 115], [35, 61, 155], [62, 44, 84], [92, 37, 110], [138, 134, 44], [149, 118, 147]], ![[0, 1], [126, 148, 93], [133, 40, 66], [33, 95, 139], [117, 148, 58], [84, 35, 10], [96, 29, 118], [38, 44, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24, 134], []]
 b := ![[], [88, 161, 151], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [31, 8, 139, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![50135, 48342, -80280, -1092, 42774]
  a := ![1, -6, -1, -3, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9403, -41382, -8766, -1092, 42774]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 4330747 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 32, -4, 1, -12]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![31, 32, -4, 1, -12]] 
 ![![163, 0, 0, 0, 0], ![0, 163, 0, 0, 0], ![63, 27, 1, 0, 0], ![92, 118, 0, 1, 0], ![52, 134, 0, 0, 1]] where
  M :=![![![31, 32, -4, 1, -12], ![48, 53, -8, 2, -18], ![36, 40, -1, -1, -12], ![0, 2, 8, 5, -6], ![-12, -12, 0, 3, 7]]]
  hmulB := by decide  
  f := ![![![85, -50, 4, -7, 18]], ![![-72, 39, 8, 4, -6]], ![![21, -13, 3, -2, 6]], ![![-4, 0, 8, -1, 6]], ![![-32, 16, 8, 1, 1]]]
  g := ![![![5, 10, -4, 1, -12], ![8, 15, -8, 2, -18], ![5, 11, -1, -1, -12], ![-4, 0, 8, 5, -6], ![-4, -8, 0, 3, 7]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P1 : CertificateIrreducibleZModOfList' 163 2 2 7 [149, 151, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 162], [0, 1]]
 g := ![![[94, 40], [74, 152], [1], [77], [53], [108, 144], [1]], ![[85, 123], [105, 11], [1], [77], [53], [43, 19], [1]]]
 h' := ![![[12, 162], [58, 140], [104, 106], [116, 162], [159, 136], [45, 85], [14, 12], [0, 1]], ![[0, 1], [108, 23], [72, 57], [104, 1], [161, 27], [87, 78], [158, 151], [12, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [88]]
 b := ![[], [62, 44]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N1 : CertifiedPrimeIdeal' SI163N1 163 where
  n := 2
  hpos := by decide
  P := [149, 151, 1]
  hirr := P163P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8571, 4151, 14418, -203, 20464]
  a := ![1, 26, 4, 10, 23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-12039, -19039, 14418, -203, 20464]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N1 B_one_repr
lemma NI163N1 : Nat.card (O ⧸ I163N1) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![85, -50, 4, -7, 18]] ![![31, 32, -4, 1, -12]]
  ![![163, 0, 0, 0, 0]] where
 M := ![![![163, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC163 : ContainsPrimesAboveP 163 ![I163N0, I163N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
    exact isPrimeI163N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 163 (by decide) (𝕀 ⊙ MulI163N0)
instance hp167 : Fact (Nat.Prime 167) := {out := by norm_num}

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![26279, -13842, 888, -2239, 4428]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![26279, -13842, 888, -2239, 4428]] 
 ![![167, 0, 0, 0, 0], ![0, 167, 0, 0, 0], ![0, 0, 167, 0, 0], ![82, 102, 101, 1, 0], ![50, 110, 63, 0, 1]] where
  M :=![![![26279, -13842, 888, -2239, 4428], ![-17712, 13833, -1116, 1826, -4578], ![9156, -3010, 99, -653, 900], ![7056, -3842, 248, -611, 1230], ![7436, -5288, 404, -731, 1735]]]
  hmulB := by decide  
  f := ![![![73, 68, -120, -15, 66]], ![![-264, -209, 532, -276, 42]], ![![-84, -184, -83, 787, -786]], ![![-166, -196, 199, 298, -408]], ![![-186, -188, 289, 104, -245]]]
  g := ![![![-69, -1632, -311, -2239, 4428], ![368, 1983, 616, 1826, -4578], ![106, -212, 56, -653, 900], ![-26, -460, -93, -611, 1230], ![-116, -728, -210, -731, 1735]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [146, 46, 146, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [129, 164, 80], [59, 2, 87], [0, 1]]
 g := ![![[30, 149, 107], [116, 91, 126], [46, 59, 130], [92, 144], [143, 4], [61, 21, 1], []], ![[98, 65, 61, 143], [134, 74, 85, 165], [75, 75, 118, 159], [34, 133], [94, 58], [141, 52, 0, 153], [153, 54]], ![[89, 50, 88, 42], [58, 15, 166, 64], [63, 69, 78, 58], [85, 93], [25, 122], [9, 114, 137, 115], [146, 54]]]
 h' := ![![[129, 164, 80], [98, 42, 146], [131, 80, 31], [17, 85, 56], [16, 150, 155], [112, 140, 2], [0, 0, 1], [0, 1]], ![[59, 2, 87], [70, 166, 145], [9, 156, 116], [65, 24, 65], [55, 27, 119], [98, 85, 15], [148, 2, 2], [129, 164, 80]], ![[0, 1], [25, 126, 43], [60, 98, 20], [89, 58, 46], [108, 157, 60], [90, 109, 150], [34, 165, 164], [59, 2, 87]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 164], []]
 b := ![[], [123, 161, 23], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [146, 46, 146, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4602591, -4024406, 8333010, -1605620, -2054999]
  a := ![-1, -6, -4, 13, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1376097, 2310172, 1796201, -1605620, -2054999]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 4657463 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-73, -68, 120, 15, -66]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![-73, -68, 120, 15, -66]] 
 ![![167, 0, 0, 0, 0], ![0, 167, 0, 0, 0], ![159, 66, 1, 0, 0], ![27, 66, 0, 1, 0], ![18, 50, 0, 0, 1]] where
  M :=![![![-73, -68, 120, 15, -66], ![264, 209, -532, 276, -42], ![84, 184, 83, -787, 786], ![-1704, -1594, 2808, 339, -1554], ![380, 214, -972, 1103, -683]]]
  hmulB := by decide  
  f := ![![![-26279, 13842, -888, 2239, -4428]], ![![17712, -13833, 1116, -1826, 4578]], ![![-18075, 7730, -405, 1414, -2412]], ![![2709, -3206, 296, -356, 1086]], ![![2426, -2618, 236, -301, 883]]]
  g := ![![![-110, -34, 120, 15, -66], ![468, 115, -532, 276, -42], ![-36, 44, 83, -787, 786], ![-2571, -788, 2808, 339, -1554], ![823, 154, -972, 1103, -683]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P1 : CertificateIrreducibleZModOfList' 167 2 2 7 [164, 100, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [67, 166], [0, 1]]
 g := ![![[78, 27], [165, 29], [49, 122], [18], [3], [64, 147], [1]], ![[50, 140], [104, 138], [40, 45], [18], [3], [60, 20], [1]]]
 h' := ![![[67, 166], [161, 19], [147, 153], [41, 17], [133, 128], [25, 62], [3, 67], [0, 1]], ![[0, 1], [98, 148], [44, 14], [11, 150], [25, 39], [4, 105], [150, 100], [67, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [84]]
 b := ![[], [96, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N1 : CertifiedPrimeIdeal' SI167N1 167 where
  n := 2
  hpos := by decide
  P := [164, 100, 1]
  hirr := P167P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6140, -7740, 6960, 12076, -15436]
  a := ![0, -2, 4, -26, 22]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6952, -2948, 6960, 12076, -15436]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N1 B_one_repr
lemma NI167N1 : Nat.card (O ⧸ I167N1) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![26279, -13842, 888, -2239, 4428]] ![![-73, -68, 120, 15, -66]]
  ![![167, 0, 0, 0, 0]] where
 M := ![![![-167, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC167 : ContainsPrimesAboveP 167 ![I167N0, I167N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
    exact isPrimeI167N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 167 (by decide) (𝕀 ⊙ MulI167N0)
instance hp173 : Fact (Nat.Prime 173) := {out := by norm_num}

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0, 0, 0]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0, 0, 0]] 
 ![![173, 0, 0, 0, 0], ![0, 173, 0, 0, 0], ![0, 0, 173, 0, 0], ![0, 0, 0, 173, 0], ![0, 0, 0, 0, 173]] where
  M :=![![![173, 0, 0, 0, 0], ![0, 173, 0, 0, 0], ![0, 0, 173, 0, 0], ![0, 0, 0, 173, 0], ![0, 0, 0, 0, 173]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 5 2 7 [171, 154, 128, 138, 164, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [134, 33, 97, 110, 106], [69, 73, 103, 79, 53], [107, 26, 97, 39, 39], [45, 40, 49, 118, 148], [0, 1]]
 g := ![![[67, 83, 60, 40, 85], [159, 153, 69, 81], [98, 154, 137, 136, 73], [127, 140, 21, 25, 135], [146, 147, 148, 81], [1], []], ![[32, 1, 62, 147, 109, 6, 59, 15], [168, 41, 107, 37], [130, 6, 137, 91, 15, 13, 121, 54], [172, 27, 92, 154, 149, 125, 151, 167], [75, 9, 168, 159], [168, 58, 97, 19, 86, 28, 110, 36], [98, 165, 57, 164]], ![[50, 27, 0, 130, 111, 35, 127, 82], [83, 159, 8, 130], [89, 129, 109, 46, 56, 145, 50, 146], [98, 148, 48, 113, 132, 75, 71, 131], [105, 8, 19, 1], [11, 50, 73, 86, 75, 4, 14, 75], [24, 55, 93, 41]], ![[119, 80, 139, 35, 137, 111, 36, 156], [62, 0, 91, 121], [124, 46, 6, 124, 50, 141, 24, 45], [0, 57, 37, 133, 5, 40, 57, 61], [46, 11, 14, 15], [49, 30, 32, 107, 53, 128, 135, 168], [130, 111, 123, 137]], ![[149, 28, 107, 62, 64, 33, 85, 81], [29, 24, 84, 77], [146, 50, 146, 44, 113, 112, 155, 169], [37, 117, 142, 147, 63, 113, 94, 56], [8, 170, 99, 21], [48, 81, 10, 62, 82, 18, 101, 81], [66, 80, 71, 106]]]
 h' := ![![[134, 33, 97, 110, 106], [155, 133, 100, 50, 36], [23, 81, 138, 21, 9], [81, 3, 54, 165, 65], [123, 30, 166, 114, 57], [2, 19, 45, 35, 9], [0, 0, 1], [0, 1]], ![[69, 73, 103, 79, 53], [106, 51, 79, 26, 20], [156, 49, 40, 17, 146], [139, 62, 142, 67, 70], [14, 52, 157, 121, 79], [146, 61, 61, 10, 32], [160, 137, 144, 54, 152], [134, 33, 97, 110, 106]], ![[107, 26, 97, 39, 39], [151, 18, 114, 69, 148], [136, 9, 56, 49, 87], [146, 22, 54, 48, 64], [115, 37, 33, 3, 170], [123, 127, 25, 168, 172], [138, 87, 56, 137, 59], [69, 73, 103, 79, 53]], ![[45, 40, 49, 118, 148], [146, 66, 41, 63, 171], [56, 126, 158, 124, 162], [74, 109, 36, 165, 9], [61, 52, 27, 139, 122], [90, 3, 19, 56, 19], [118, 125, 56, 115, 106], [107, 26, 97, 39, 39]], ![[0, 1], [18, 78, 12, 138, 144], [126, 81, 127, 135, 115], [171, 150, 60, 74, 138], [51, 2, 136, 142, 91], [30, 136, 23, 77, 114], [81, 170, 89, 40, 29], [45, 40, 49, 118, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [101, 103, 0, 82], [], [], []]
 b := ![[], [119, 123, 35, 13, 120], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 5
  hpos := by decide
  P := [171, 154, 128, 138, 164, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![80372160772, 103274039345, -71025218681, -228402845353, 266159425151]
  a := ![13, -6, -3, 8, -19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![464578964, 596959765, -410550397, -1320247661, 1538493787]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 154963892093 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def PBC173 : ContainsPrimesAboveP 173 ![I173N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![173, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 173 (by decide) 𝕀

instance hp179 : Fact (Nat.Prime 179) := {out := by norm_num}

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-245, -264, 40, 19, 66]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![-245, -264, 40, 19, 66]] 
 ![![179, 0, 0, 0, 0], ![0, 179, 0, 0, 0], ![0, 0, 179, 0, 0], ![86, 168, 137, 1, 0], ![99, 29, 170, 0, 1]] where
  M :=![![![-245, -264, 40, 19, 66], ![-264, -299, -132, -24, 246], ![-492, -468, 439, -231, 174], ![-216, -282, 120, 595, -642], ![444, 402, -652, 155, 85]]]
  hmulB := by decide  
  f := ![![![65, 198, -392, -65, -312]], ![![1248, 167, -1476, -342, -1014]], ![![2028, 558, -2875, -627, -2040]], ![![2774, 684, -3801, -838, -2682]], ![![2181, 671, -3210, -692, -2291]]]
  g := ![![![-47, -30, -77, 19, 66], ![-126, -19, -216, -24, 246], ![12, 186, 14, -231, 174], ![68, -456, 155, 595, -642], ![-119, -157, -203, 155, 85]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 3 2 7 [166, 67, 153, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [100, 120, 73], [105, 58, 106], [0, 1]]
 g := ![![[49, 159, 142], [98, 158, 177], [125, 27], [50, 142], [93, 120, 43], [72, 26, 1], []], ![[156, 111, 26, 170], [159, 77, 67, 97], [28, 25], [135, 129], [160, 161, 23, 54], [31, 34, 110, 163], [165, 138]], ![[169, 62, 156, 49], [6, 114, 50, 177], [117, 85], [85, 45], [162, 66, 138, 64], [23, 118, 28, 67], [132, 138]]]
 h' := ![![[100, 120, 73], [21, 147, 58], [149, 157, 101], [80, 97, 57], [135, 53, 121], [41, 168, 143], [0, 0, 1], [0, 1]], ![[105, 58, 106], [88, 56, 133], [55, 120, 135], [7, 81, 5], [20, 137, 147], [92, 64, 152], [152, 61, 58], [100, 120, 73]], ![[0, 1], [128, 155, 167], [176, 81, 122], [96, 1, 117], [85, 168, 90], [61, 126, 63], [32, 118, 120], [105, 58, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [89, 46], []]
 b := ![[], [8, 157, 95], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 3
  hpos := by decide
  P := [166, 67, 153, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![254067, 216925, -484876, 174669, 51791]
  a := ![-1, 0, 2, -8, 11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-111144, -171114, -185581, 174669, 51791]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 5735339 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![65, 198, -392, -65, -312]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![65, 198, -392, -65, -312]] 
 ![![179, 0, 0, 0, 0], ![0, 179, 0, 0, 0], ![150, 42, 1, 0, 0], ![144, 12, 0, 1, 0], ![164, 99, 0, 0, 1]] where
  M :=![![![65, 198, -392, -65, -312], ![1248, 167, -1476, -342, -1014], ![2028, 558, -2875, -627, -2040], ![3456, 906, -4824, -1057, -3414], ![3012, 804, -4228, -925, -2995]]]
  hmulB := by decide  
  f := ![![![-245, -264, 40, 19, 66]], ![![-264, -299, -132, -24, 246]], ![![-270, -294, 5, 9, 114]], ![![-216, -234, 24, 17, 66]], ![![-368, -405, -40, 5, 197]]]
  g := ![![![667, 270, -392, -65, -312], ![2448, 931, -1476, -342, -1014], ![4794, 1848, -2875, -627, -2040], ![8040, 3096, -4824, -1057, -3414], ![7048, 2715, -4228, -925, -2995]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P1 : CertificateIrreducibleZModOfList' 179 2 2 7 [88, 154, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 178], [0, 1]]
 g := ![![[136, 59], [120, 31], [155], [4], [86, 61], [127, 88], [1]], ![[0, 120], [0, 148], [155], [4], [0, 118], [0, 91], [1]]]
 h' := ![![[25, 178], [1, 136], [143, 116], [0, 79], [129, 2], [101, 132], [91, 25], [0, 1]], ![[0, 1], [0, 43], [0, 63], [6, 100], [0, 177], [0, 47], [0, 154], [25, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [105, 99]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N1 : CertifiedPrimeIdeal' SI179N1 179 where
  n := 2
  hpos := by decide
  P := [88, 154, 1]
  hirr := P179P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-15681, -11087, 27079, 707, -2121]
  a := ![3, 10, 7, -15, 35]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-21405, -5290, 27079, 707, -2121]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N1 B_one_repr
lemma NI179N1 : Nat.card (O ⧸ I179N1) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![-245, -264, 40, 19, 66]] ![![65, 198, -392, -65, -312]]
  ![![179, 0, 0, 0, 0]] where
 M := ![![![179, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC179 : ContainsPrimesAboveP 179 ![I179N0, I179N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI179N0
    exact isPrimeI179N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 179 (by decide) (𝕀 ⊙ MulI179N0)
instance hp181 : Fact (Nat.Prime 181) := {out := by norm_num}

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![279, 305, -48, 9, -110]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![279, 305, -48, 9, -110]] 
 ![![181, 0, 0, 0, 0], ![0, 181, 0, 0, 0], ![0, 0, 181, 0, 0], ![62, 74, 56, 1, 0], ![70, 51, 84, 0, 1]] where
  M :=![![![279, 305, -48, 9, -110], ![440, 469, -50, -4, -166], ![332, 357, -29, 37, -178], ![136, 132, -152, 25, 16], ![-112, -112, 26, -52, 91]]]
  hmulB := by decide  
  f := ![![![43, 27, -86, -17, -64]], ![![256, 51, -330, -74, -230]], ![![460, 119, -639, -141, -452]], ![![266, 68, -368, -81, -260]], ![![306, 81, -428, -94, -303]]]
  g := ![![![41, 29, 48, 9, -110], ![68, 51, 78, -4, -166], ![58, 37, 71, 37, -178], ![-14, -14, -16, 25, 16], ![-18, -5, -26, -52, 91]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [73, 60, 125, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [67, 150, 57], [170, 30, 124], [0, 1]]
 g := ![![[9, 159, 62], [0, 172], [29, 15, 67], [118, 9], [136, 162, 147], [180, 56, 1], []], ![[75, 156, 132, 23], [62, 117], [153, 56, 143, 89], [127, 39], [81, 77, 176, 68], [173, 37, 11, 77], [125, 172]], ![[178, 89, 1, 22], [40, 60], [154, 49, 167, 113], [138, 125], [40, 153, 142, 89], [24, 85, 110, 66], [58, 172]]]
 h' := ![![[67, 150, 57], [129, 104, 65], [55, 148, 124], [79, 81, 130], [27, 4, 178], [73, 135, 131], [0, 0, 1], [0, 1]], ![[170, 30, 124], [63, 179, 95], [8, 144, 29], [126, 132, 10], [85, 106, 138], [7, 131, 41], [70, 44, 30], [67, 150, 57]], ![[0, 1], [63, 79, 21], [102, 70, 28], [77, 149, 41], [14, 71, 46], [70, 96, 9], [50, 137, 150], [170, 30, 124]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59, 79], []]
 b := ![[], [60, 168, 78], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [73, 60, 125, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![86291, 97745, -282598, 387165, -90356]
  a := ![1, 4, 2, -6, 13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-97199, -132289, -79414, 387165, -90356]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 5929741 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-27445, 14126, -890, 2315, -4508]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![-27445, 14126, -890, 2315, -4508]] 
 ![![181, 0, 0, 0, 0], ![96, 1, 0, 0, 0], ![98, 0, 1, 0, 0], ![135, 0, 0, 1, 0], ![25, 0, 0, 0, 1]] where
  M :=![![![-27445, 14126, -890, 2315, -4508], ![18032, -14689, 1204, -1902, 4874], ![-9748, 2842, -67, 669, -832], ![-7352, 3938, -256, 631, -1262], ![-7620, 5572, -436, 759, -1835]]]
  hmulB := by decide  
  f := ![![![-249, -328, -42, 1497, -1270]], ![![-104, -145, -68, 784, -638]], ![![-206, -232, 113, 757, -682]], ![![-211, -286, -46, 1308, -1120]], ![![63, 46, -182, 234, -111]]]
  g := ![![![-8266, 14126, -890, 2315, -4508], ![7984, -14689, 1204, -1902, 4874], ![-1909, 2842, -67, 669, -832], ![-2287, 3938, -256, 631, -1262], ![-3074, 5572, -436, 759, -1835]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1

def I181N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-21, 44, -14, 14, -20]] i)))

def SI181N2: IdealEqSpanCertificate' Table ![![-21, 44, -14, 14, -20]] 
 ![![181, 0, 0, 0, 0], ![154, 1, 0, 0, 0], ![88, 0, 1, 0, 0], ![25, 0, 0, 1, 0], ![160, 0, 0, 0, 1]] where
  M :=![![![-21, 44, -14, 14, -20], ![80, 33, -32, -36, 44], ![-88, -56, 165, -18, -64], ![88, 68, -232, 233, -140], ![96, 112, -184, -42, 125]]]
  hmulB := by decide  
  f := ![![![-8879585, -2200716, 12183034, 2684618, 8598404]], ![![-7745026, -1919527, 10626388, 2341600, 7499772]], ![![-4685152, -1161168, 6428157, 1416490, 4536792]], ![![-1844157, -457056, 2530234, 557555, 1785760]], ![![-8390672, -2079544, 11512232, 2536802, 8124973]]]
  g := ![![![-15, 44, -14, 14, -20], ![-46, 33, -32, -36, 44], ![26, -56, 165, -18, -64], ![147, 68, -232, 233, -140], ![-110, 112, -184, -42, 125]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N2 : Nat.card (O ⧸ I181N2) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N2)

lemma isPrimeI181N2 : Ideal.IsPrime I181N2 := prime_ideal_of_norm_prime hp181.out _ NI181N2
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![279, 305, -48, 9, -110]] ![![-27445, 14126, -890, 2315, -4508]]
  ![![-917459, -1252885, 167782, -44148, 459266]] where
 M := ![![![-917459, -1252885, 167782, -44148, 459266]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI181N1 : IdealMulLeCertificate' Table 
  ![![-917459, -1252885, 167782, -44148, 459266]] ![![-21, 44, -14, 14, -20]]
  ![![181, 0, 0, 0, 0]] where
 M := ![![![-55524465, -42673465, 6358168, -336298, 16073162]]]
 hmul := by decide  
 g := ![![![![-306765, -235765, 35128, -1858, 88802]]]]
 hle2 := by decide  


def PBC181 : ContainsPrimesAboveP 181 ![I181N0, I181N1, I181N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
    exact isPrimeI181N1
    exact isPrimeI181N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 181 (by decide) (𝕀 ⊙ MulI181N0 ⊙ MulI181N1)
instance hp191 : Fact (Nat.Prime 191) := {out := by norm_num}

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4947761, 2981112, -210222, 447952, -966340]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![-4947761, 2981112, -210222, 447952, -966340]] 
 ![![191, 0, 0, 0, 0], ![0, 191, 0, 0, 0], ![0, 0, 191, 0, 0], ![0, 0, 0, 191, 0], ![74, 89, 34, 53, 1]] where
  M :=![![![-4947761, 2981112, -210222, 447952, -966340], ![3865360, -2329399, 164184, -350008, 755032], ![-1510064, 909732, -64303, 136676, -294992], ![-1342696, 809184, -57336, 121521, -262480], ![-1561032, 940856, -66592, 141304, -305143]]]
  hmulB := by decide  
  f := ![![![-111, -80, 238, -168, 68]], ![![-272, -345, 248, 744, -872]], ![![1744, 1604, -2961, -60, 1360]], ![![-2584, -1856, 5560, -3953, 1616]], ![![-586, -431, 1238, -819, 297]]]
  g := ![![![348489, 465892, 170918, 270492, -966340], ![-272288, -364017, -133544, -211344, 755032], ![106384, 142220, 52175, 82572, -294992], ![94664, 126544, 46424, 73471, -262480], ![110050, 147113, 53970, 85413, -305143]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 4 2 7 [18, 137, 134, 0, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [139, 173, 36, 108], [165, 172, 76, 91], [78, 36, 79, 183], [0, 1]]
 g := ![![[109, 118, 87, 60], [166, 32, 60, 69], [11, 123, 82, 5], [33, 90, 31, 150], [99, 23, 44, 2], [0, 1], []], ![[21, 88, 13, 74, 89, 78], [111, 81, 139, 144, 67, 75], [8, 142, 8, 157, 166, 1], [136, 10, 15, 175, 120, 96], [2, 10, 5, 64, 161, 117], [129, 61, 189, 65, 101, 48], [59, 136, 13]], ![[123, 176, 20, 168, 121, 71], [7, 120, 67, 57, 177, 190], [119, 172, 158, 96, 163, 41], [136, 86, 40, 92, 10, 47], [86, 184, 54, 37, 7, 35], [188, 76, 40, 21, 92, 127], [82, 80, 68]], ![[78, 90, 126, 120, 168, 99], [45, 77, 89, 135, 72, 174], [105, 31, 135, 97, 159, 148], [1, 151, 79, 122, 9, 56], [37, 45, 144, 187, 133, 91], [172, 68, 186, 154, 165, 167], [145, 73, 64]]]
 h' := ![![[139, 173, 36, 108], [68, 33, 67, 99], [184, 158, 180, 32], [170, 120, 153, 14], [128, 157, 172, 155], [0, 173, 54, 57], [0, 0, 1], [0, 1]], ![[165, 172, 76, 91], [25, 83, 166, 120], [80, 61, 108, 31], [118, 77, 123, 126], [128, 92, 97, 38], [127, 126, 93, 50], [114, 127, 177, 128], [139, 173, 36, 108]], ![[78, 36, 79, 183], [0, 99, 76, 125], [17, 85, 131, 172], [148, 65, 127, 80], [167, 38, 87, 37], [165, 6, 124, 131], [155, 156, 168, 39], [165, 172, 76, 91]], ![[0, 1], [171, 167, 73, 38], [183, 78, 154, 147], [90, 120, 170, 162], [113, 95, 26, 152], [9, 77, 111, 144], [36, 99, 36, 24], [78, 36, 79, 183]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [183, 159, 40], []]
 b := ![[], [], [134, 53, 110, 115], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 4
  hpos := by decide
  P := [18, 137, 134, 0, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3390658, -2676060, 6726306, -3227294, 397832]
  a := ![4, -1, -1, 3, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-171886, -199388, -35602, -127290, 397832]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 1330863361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![111, 80, -238, 168, -68]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![111, 80, -238, 168, -68]] 
 ![![191, 0, 0, 0, 0], ![62, 1, 0, 0, 0], ![179, 0, 1, 0, 0], ![150, 0, 0, 1, 0], ![71, 0, 0, 0, 1]] where
  M :=![![![111, 80, -238, 168, -68], ![272, 345, -248, -744, 872], ![-1744, -1604, 2961, 60, -1360], ![2584, 1856, -5560, 3953, -1616], ![1848, 1864, -2768, -1336, 2585]]]
  hmulB := by decide  
  f := ![![![4947761, -2981112, 210222, -447952, 966340]], ![![1585842, -955495, 67380, -143576, 309728]], ![![4644813, -2798580, 197351, -420524, 907172]], ![![3892706, -2345424, 165396, -352431, 760280]], ![![1847393, -1113088, 78494, -167256, 360813]]]
  g := ![![![91, 80, -238, 168, -68], ![382, 345, -248, -744, 872], ![-1805, -1604, 2961, 60, -1360], ![2118, 1856, -5560, 3953, -1616], ![2087, 1864, -2768, -1336, 2585]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![-4947761, 2981112, -210222, 447952, -966340]] ![![111, 80, -238, 168, -68]]
  ![![191, 0, 0, 0, 0]] where
 M := ![![![-191, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC191 : ContainsPrimesAboveP 191 ![I191N0, I191N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI191N0
    exact isPrimeI191N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 191 (by decide) (𝕀 ⊙ MulI191N0)
instance hp193 : Fact (Nat.Prime 193) := {out := by norm_num}

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-167, -1254, 148, -80, 446]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![-167, -1254, 148, -80, 446]] 
 ![![193, 0, 0, 0, 0], ![0, 193, 0, 0, 0], ![0, 0, 193, 0, 0], ![1, 123, 15, 1, 0], ![124, 8, 164, 0, 1]] where
  M :=![![![-167, -1254, 148, -80, 446], ![-1784, -1071, 168, 10, 412], ![-824, -1210, 165, -48, 442], ![8, -284, 32, -13, 92], ![536, 234, -48, -8, -89]]]
  hmulB := by decide  
  f := ![![![201, 50, -276, -60, -194]], ![![776, 193, -1064, -238, -748]], ![![1496, 366, -2051, -452, -1462]], ![![625, 155, -857, -191, -604]], ![![1444, 354, -1980, -436, -1409]]]
  g := ![![![-287, 26, -372, -80, 446], ![-274, -29, -350, 10, 412], ![-288, 6, -371, -48, 442], ![-59, 3, -77, -13, 92], ![60, 10, 76, -8, -89]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 3 2 7 [108, 11, 161, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [77, 100, 122], [148, 92, 71], [0, 1]]
 g := ![![[94, 72, 131], [174, 86], [163, 42], [173, 139], [0, 186], [26, 59], [1]], ![[75, 27, 53, 77], [172, 42], [167, 110], [32, 187], [154, 54], [28, 83], [127, 32, 192, 104]], ![[105, 162, 135, 10], [145, 7], [132, 56], [180, 169], [79, 32], [159, 187], [177, 128, 125, 89]]]
 h' := ![![[77, 100, 122], [178, 100, 18], [40, 11, 146], [184, 141, 106], [98, 24, 116], [171, 157, 147], [85, 182, 32], [0, 1]], ![[148, 92, 71], [86, 43, 153], [110, 111, 106], [2, 176, 127], [131, 57, 90], [92, 101, 61], [75, 177, 58], [77, 100, 122]], ![[0, 1], [83, 50, 22], [127, 71, 134], [115, 69, 153], [107, 112, 180], [98, 128, 178], [155, 27, 103], [148, 92, 71]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77, 76], []]
 b := ![[], [80, 148, 50], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 3
  hpos := by decide
  P := [108, 11, 161, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![15238445, -20579313, 70717472, -251838918, 48985625]
  a := ![7, -46, -24, 25, -119]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-30088809, 158361257, -21685706, -251838918, 48985625]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 7189057 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 0, 6, -7, 4]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![-1, 0, 6, -7, 4]] 
 ![![193, 0, 0, 0, 0], ![74, 1, 0, 0, 0], ![157, 0, 1, 0, 0], ![137, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![-1, 0, 6, -7, 4], ![-16, -17, 24, 22, -34], ![68, 60, -119, 19, 32], ![-56, -30, 144, -165, 106], ![-84, -80, 136, 23, -83]]]
  hmulB := by decide  
  f := ![![![-441, -650, 1558, 279, 1202]], ![![-194, -253, 628, 114, 482]], ![![-401, -540, 1327, 240, 1020]], ![![-385, -480, 1206, 220, 924]], ![![-72, -30, 120, 25, 87]]]
  g := ![![![0, 0, 6, -7, 4], ![-28, -17, 24, 22, -34], ![60, 60, -119, 19, 32], ![9, -30, 144, -165, 106], ![-95, -80, 136, 23, -83]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1

def I193N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-26471, -6560, 36318, 8003, 25632]] i)))

def SI193N2: IdealEqSpanCertificate' Table ![![-26471, -6560, 36318, 8003, 25632]] 
 ![![193, 0, 0, 0, 0], ![89, 1, 0, 0, 0], ![189, 0, 1, 0, 0], ![37, 0, 0, 1, 0], ![45, 0, 0, 0, 1]] where
  M :=![![![-26471, -6560, 36318, 8003, 25632], ![-102528, -25411, 140672, 30998, 99282], ![-198564, -49212, 272435, 60033, 192276], ![-333288, -82602, 457280, 100765, 322734], ![-292076, -72388, 400736, 88305, 282827]]]
  hmulB := by decide  
  f := ![![![2689, 3082, -426, 149, -1206]], ![![1265, 1447, -202, 69, -564]], ![![2649, 3036, -415, 144, -1188]], ![![517, 592, -82, 36, -240]], ![![625, 716, -106, 36, -277]]]
  g := ![![![-40188, -6560, 36318, 8003, 25632], ![-155661, -25411, 140672, 30998, 99282], ![-301464, -49212, 272435, 60033, 192276], ![-506005, -82602, 457280, 100765, 322734], ![-443436, -72388, 400736, 88305, 282827]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N2 : Nat.card (O ⧸ I193N2) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N2)

lemma isPrimeI193N2 : Ideal.IsPrime I193N2 := prime_ideal_of_norm_prime hp193.out _ NI193N2
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![-167, -1254, 148, -80, 446]] ![![-1, 0, 6, -7, 4]]
  ![![-2689, -3082, 426, -149, 1206]] where
 M := ![![![-2689, -3082, 426, -149, 1206]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI193N1 : IdealMulLeCertificate' Table 
  ![![-2689, -3082, 426, -149, 1206]] ![![-26471, -6560, 36318, 8003, 25632]]
  ![![193, 0, 0, 0, 0]] where
 M := ![![![-193, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC193 : ContainsPrimesAboveP 193 ![I193N0, I193N1, I193N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI193N0
    exact isPrimeI193N1
    exact isPrimeI193N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 193 (by decide) (𝕀 ⊙ MulI193N0 ⊙ MulI193N1)
instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0, 0, 0]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0, 0, 0]] 
 ![![197, 0, 0, 0, 0], ![0, 197, 0, 0, 0], ![0, 0, 197, 0, 0], ![0, 0, 0, 197, 0], ![0, 0, 0, 0, 197]] where
  M :=![![![197, 0, 0, 0, 0], ![0, 197, 0, 0, 0], ![0, 0, 197, 0, 0], ![0, 0, 0, 197, 0], ![0, 0, 0, 0, 197]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 5 2 7 [46, 140, 156, 13, 12, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [154, 177, 143, 143, 178], [44, 156, 125, 70, 102], [109, 129, 111, 70, 133], [75, 128, 15, 111, 178], [0, 1]]
 g := ![![[108, 172, 88, 122, 105], [21, 159, 102, 15], [148, 21, 90, 180, 134], [145, 41, 25, 40], [181, 20, 130, 22], [185, 1], []], ![[115, 186, 162, 191, 71, 192, 154, 187], [48, 124, 160, 85], [20, 110, 9, 182, 126, 177, 167, 107], [71, 191, 50, 101], [37, 90, 170, 59], [188, 38, 61, 88], [92, 127, 61, 107, 185, 141, 186, 36]], ![[98, 2, 78, 157, 73, 134, 116, 179], [82, 129, 190, 53], [142, 189, 60, 27, 193, 73, 152, 194], [54, 7, 159, 164], [43, 68, 87, 10], [172, 39], [16, 36, 177, 23, 127, 83, 88, 166]], ![[172, 46, 1, 119, 2, 193, 189, 28], [113, 157, 148, 64], [48, 146, 69, 160, 61, 132, 129, 132], [57, 25, 5, 22], [94, 53, 129, 144], [172, 130, 138, 41], [142, 174, 113, 193, 21, 83, 90, 63]], ![[62, 23, 149, 156, 93, 44, 25, 7], [150, 123, 136, 25], [195, 46, 165, 138, 103, 12, 182, 158], [109, 186, 164, 114], [21, 89, 43, 43], [88, 144, 72, 182], [169, 141, 162, 89, 149, 162, 5, 36]]]
 h' := ![![[154, 177, 143, 143, 178], [102, 29, 51, 161, 41], [87, 24, 79, 164, 139], [51, 171, 185, 136, 79], [90, 145, 81, 109, 146], [158, 58, 156, 0, 131], [0, 0, 0, 1], [0, 1]], ![[44, 156, 125, 70, 102], [95, 186, 136, 71, 150], [50, 67, 52, 53, 26], [148, 110, 195, 187, 141], [38, 196, 69, 7, 62], [19, 126, 40, 89, 16], [183, 161, 44, 99, 132], [154, 177, 143, 143, 178]], ![[109, 129, 111, 70, 133], [105, 59, 110, 59, 107], [79, 47, 59, 55, 29], [62, 196, 10, 132, 94], [173, 119, 123, 113, 19], [56, 183, 136, 135, 73], [132, 89, 10, 32], [44, 156, 125, 70, 102]], ![[75, 128, 15, 111, 178], [33, 142, 162, 102, 23], [75, 60, 58, 8, 8], [112, 26, 90, 179, 54], [166, 151, 96, 89, 131], [64, 23, 97, 102, 12], [117, 57, 196, 112, 89], [109, 129, 111, 70, 133]], ![[0, 1], [169, 175, 132, 1, 73], [78, 196, 146, 114, 192], [57, 88, 111, 154, 26], [151, 177, 25, 76, 36], [138, 4, 162, 68, 162], [7, 87, 144, 150, 173], [75, 128, 15, 111, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54, 23, 144, 43], [], [], []]
 b := ![[], [44, 14, 152, 156, 23], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 5
  hpos := by decide
  P := [46, 140, 156, 13, 12, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2195918246216, 1733665576572, -3738311632066, 254884956402, 729868879884]
  a := ![1, -12, -7, 9, -36]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![11146793128, 8800332876, -18976201178, 1293832266, 3704918172]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 296709280757 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def PBC197 : ContainsPrimesAboveP 197 ![I197N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![197, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 197 (by decide) 𝕀



lemma PB1321I4_primes (p : ℕ) :
  p ∈ Set.range ![157, 163, 167, 173, 179, 181, 191, 193, 197] ↔ Nat.Prime p ∧ 151 < p ∧ p ≤ 197 := by
  rw [← List.mem_ofFn']
  convert primes_range 151 197 (by omega)

def PB1321I4 : PrimesBelowBoundCertificateInterval O 151 197 1321 where
  m := 9
  g := ![3, 2, 2, 1, 2, 3, 2, 3, 1]
  P := ![157, 163, 167, 173, 179, 181, 191, 193, 197]
  hP := PB1321I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I157N0, I157N1, I157N2]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1]
    · exact ![I173N0]
    · exact ![I179N0, I179N1]
    · exact ![I181N0, I181N1, I181N2]
    · exact ![I191N0, I191N1]
    · exact ![I193N0, I193N1, I193N2]
    · exact ![I197N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC157
    · exact PBC163
    · exact PBC167
    · exact PBC173
    · exact PBC179
    · exact PBC181
    · exact PBC191
    · exact PBC193
    · exact PBC197
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![24649, 24649, 157]
    · exact ![4330747, 26569]
    · exact ![4657463, 27889]
    · exact ![154963892093]
    · exact ![5735339, 32041]
    · exact ![5929741, 181, 181]
    · exact ![1330863361, 191]
    · exact ![7189057, 193, 193]
    · exact ![296709280757]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
      exact NI157N1
      exact NI157N2
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
      exact NI163N1
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
      exact NI179N1
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
      exact NI181N2
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
      exact NI193N2
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
  β := ![I157N2, I181N1, I181N2, I191N1, I193N1, I193N2]
  Il := ![[I157N2], [], [], [], [], [I181N1, I181N2], [I191N1], [I193N1, I193N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
