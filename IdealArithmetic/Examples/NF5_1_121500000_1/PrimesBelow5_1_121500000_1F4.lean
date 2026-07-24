
import IdealArithmetic.Examples.NF5_1_121500000_1.RI5_1_121500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7645, -1219, -2618, -2670, -1727]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![7645, -1219, -2618, -2670, -1727]] 
 ![![157, 0, 0, 0, 0], ![0, 157, 0, 0, 0], ![0, 0, 157, 0, 0], ![48, 120, 106, 1, 0], ![7, 148, 16, 0, 1]] where
  M :=![![![7645, -1219, -2618, -2670, -1727], ![-10362, 14446, -5616, -9792, -10839], ![-65034, 50103, -6185, -18930, -26235], ![-73524, 39525, 5277, -3449, -12018], ![37310, -28449, 3338, 10552, 14748]]]
  hmulB := by decide  
  f := ![![![-99, 57, 98, -2, 203]], ![![1218, -1424, 258, -216, -621]], ![![-3726, 5607, -2261, 1110, 567]], ![![-1608, 2691, -1277, 577, -12]], ![![781, -778, 6, -90, -543]]]
  g := ![![![942, 3661, 1962, -2670, -1727], ![3411, 17794, 7680, -9792, -10839], ![6543, 39519, 15415, -18930, -26235], ![1122, 14217, 3587, -3449, -12018], ![-3646, -22149, -8606, 10552, 14748]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [154, 85, 100, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 35, 117], [51, 121, 40], [0, 1]]
 g := ![![[2, 15, 30], [71, 17], [106, 118, 154], [57, 44, 14], [154, 120, 105], [57, 1], []], ![[153, 89, 123, 144], [42, 127], [22, 6, 61, 100], [132, 138, 146, 31], [116, 122, 76, 14], [73, 40], [9, 30]], ![[19, 30, 154, 46], [119, 143], [141, 25, 38, 64], [139, 42, 0, 99], [5, 56, 132, 39], [69, 126], [86, 30]]]
 h' := ![![[6, 35, 117], [72, 126, 40], [4, 18, 71], [14, 78, 25], [148, 26, 64], [14, 25, 24], [0, 0, 1], [0, 1]], ![[51, 121, 40], [51, 19, 114], [32, 109, 21], [16, 123, 62], [97, 133, 110], [106, 93, 20], [63, 59, 121], [6, 35, 117]], ![[0, 1], [125, 12, 3], [125, 30, 65], [107, 113, 70], [132, 155, 140], [40, 39, 113], [33, 98, 35], [51, 121, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55, 96], []]
 b := ![[], [80, 150, 128], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [154, 85, 100, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6179768, -7807760, 2187566, -1431982, -2047796]
  a := ![0, -8, -10, -22, -37]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![568468, 2975184, 1189442, -1431982, -2047796]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 3869893 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![99, -57, -98, 2, -203]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![99, -57, -98, 2, -203]] 
 ![![157, 0, 0, 0, 0], ![0, 157, 0, 0, 0], ![117, 102, 1, 0, 0], ![156, 38, 0, 1, 0], ![25, 103, 0, 0, 1]] where
  M :=![![![99, -57, -98, 2, -203], ![-1218, 1424, -258, 216, 621], ![3726, -5607, 2261, -1110, -567], ![-1092, 3711, -3513, 1055, -2790], ![-2662, 1505, 1752, -92, 3836]]]
  hmulB := by decide  
  f := ![![![-7645, 1219, 2618, 2670, 1727]], ![![10362, -14446, 5616, 9792, 10839]], ![![1449, -8796, 5639, 8472, 8496]], ![![-4620, -2537, 3927, 5045, 4416]], ![![5343, -9102, 4080, 6782, 7292]]]
  g := ![![![104, 196, -98, 2, -203], ![-129, -283, -258, 216, 621], ![-468, -864, 2261, -1110, -567], ![2007, 3881, -3513, 1055, -2790], ![-1842, -3623, 1752, -92, 3836]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P1 : CertificateIrreducibleZModOfList' 157 2 2 7 [129, 68, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [89, 156], [0, 1]]
 g := ![![[20, 4], [82], [64, 42], [101, 93], [40, 1], [71], [1]], ![[62, 153], [82], [34, 115], [57, 64], [129, 156], [71], [1]]]
 h' := ![![[89, 156], [84, 155], [65, 125], [2, 102], [21, 67], [103, 156], [28, 89], [0, 1]], ![[0, 1], [63, 2], [43, 32], [131, 55], [18, 90], [14, 1], [99, 68], [89, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [94, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N1 : CertifiedPrimeIdeal' SI157N1 157 where
  n := 2
  hpos := by decide
  P := [129, 68, 1]
  hirr := P157P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1986230, -1976240, 456097, -376043, -335490]
  a := ![3, -126, -123, -313, -430]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![99827, 2210, 456097, -376043, -335490]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N1 B_one_repr
lemma NI157N1 : Nat.card (O ⧸ I157N1) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![7645, -1219, -2618, -2670, -1727]] ![![99, -57, -98, 2, -203]]
  ![![157, 0, 0, 0, 0]] where
 M := ![![![-157, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC157 : ContainsPrimesAboveP 157 ![I157N0, I157N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
    exact isPrimeI157N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 157 (by decide) (𝕀 ⊙ MulI157N0)
instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![425, -110, 43, 76, 107]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![425, -110, 43, 76, 107]] 
 ![![163, 0, 0, 0, 0], ![0, 163, 0, 0, 0], ![0, 0, 163, 0, 0], ![95, 108, 152, 1, 0], ![2, 3, 92, 0, 1]] where
  M :=![![![425, -110, 43, 76, 107], ![642, -205, 73, 100, 135], ![810, -130, 30, 176, 195], ![264, -72, 84, 49, 168], ![-206, -38, -35, -74, -174]]]
  hmulB := by decide  
  f := ![![![39, 2, -19, -22, -17]], ![![-102, 117, -37, -70, -81]], ![![-486, 358, -34, -122, -177]], ![![-501, 414, -67, -173, -229]], ![![-274, 203, -20, -70, -101]]]
  g := ![![![-43, -53, -131, 76, 107], ![-56, -70, -169, 100, 135], ![-100, -121, -274, 176, 195], ![-29, -36, -140, 49, 168], ![44, 52, 167, -74, -174]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [122, 63, 24, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [117, 9, 142], [22, 153, 21], [0, 1]]
 g := ![![[142, 49, 40], [40, 14, 43], [1, 156], [132, 4], [78, 1], [24, 139, 1], []], ![[58, 144, 149, 162], [130, 112, 11, 79], [110, 1], [68, 71], [7, 14], [118, 12, 145, 19], [122, 115]], ![[68, 15, 112, 36], [117, 162, 28, 46], [27, 55], [158, 97], [68, 135], [126, 79, 86, 71], [80, 115]]]
 h' := ![![[117, 9, 142], [10, 95, 140], [30, 77, 83], [57, 131, 51], [137, 57, 2], [6, 112, 162], [0, 0, 1], [0, 1]], ![[22, 153, 21], [142, 49, 28], [156, 129, 161], [79, 96, 162], [15, 87, 87], [124, 80, 103], [109, 113, 153], [117, 9, 142]], ![[0, 1], [125, 19, 158], [35, 120, 82], [118, 99, 113], [117, 19, 74], [10, 134, 61], [15, 50, 9], [22, 153, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [129, 46], []]
 b := ![[], [48, 20, 41], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [122, 63, 24, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2507916, -3434994, 1378887, -645912, -74673]
  a := ![1, -9, -9, -23, -33]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![392754, 408267, 652929, -645912, -74673]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 4330747 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-27813, 7506, -2777, -4864, -6647]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![-27813, 7506, -2777, -4864, -6647]] 
 ![![163, 0, 0, 0, 0], ![45, 1, 0, 0, 0], ![94, 0, 1, 0, 0], ![63, 0, 0, 1, 0], ![152, 0, 0, 0, 1]] where
  M :=![![![-27813, 7506, -2777, -4864, -6647], ![-39882, 11075, -4005, -6852, -9243], ![-55458, 13962, -5020, -10080, -13383], ![-20208, 6024, -2748, -3331, -5544], ![20450, -5098, 2403, 3754, 5984]]]
  hmulB := by decide  
  f := ![![![-1591579, 929602, 61121, -152346, -336487]], ![![-451779, 260765, 19578, -39984, -92310]], ![![-914332, 524386, 42034, -77394, -183355]], ![![-576879, 330186, 26997, -48133, -114999]], ![![-1486774, 873854, 53177, -148048, -319964]]]
  g := ![![![7437, 7506, -2777, -4864, -6647], ![10275, 11075, -4005, -6852, -9243], ![15076, 13962, -5020, -10080, -13383], ![6255, 6024, -2748, -3331, -5544], ![-6884, -5098, 2403, 3754, 5984]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1

def I163N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1270019, -974656, 118198, 365850, 508554]] i)))

def SI163N2: IdealEqSpanCertificate' Table ![![1270019, -974656, 118198, 365850, 508554]] 
 ![![163, 0, 0, 0, 0], ![140, 1, 0, 0, 0], ![123, 0, 1, 0, 0], ![122, 0, 0, 1, 0], ![64, 0, 0, 0, 1]] where
  M :=![![![1270019, -974656, 118198, 365850, 508554], ![3051324, -1805811, -100252, 316838, 669438], ![4016628, -1418156, -819535, -588866, -107286], ![-1847520, 2582520, -1007028, -1753967, -1940388], ![-2194620, 741768, 471506, 356458, 92729]]]
  hmulB := by decide  
  f := ![![![9165857, -2484504, 907262, 1598398, 2164770]], ![![7952200, -2155291, 787088, 1386846, 1878306]], ![![7030533, -1906252, 696243, 1225820, 1660488]], ![![6901342, -1870584, 682720, 1203525, 1629336]], ![![3555164, -963152, 352022, 620178, 840413]]]
  g := ![![![282223, -974656, 118198, 365850, 508554], ![1145384, -1805811, -100252, 316838, 669438], ![2343983, -1418156, -819535, -588866, -107286], ![605110, 2582520, -1007028, -1753967, -1940388], ![-1309570, 741768, 471506, 356458, 92729]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N2 : Nat.card (O ⧸ I163N2) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N2)

lemma isPrimeI163N2 : Ideal.IsPrime I163N2 := prime_ideal_of_norm_prime hp163.out _ NI163N2
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![425, -110, 43, 76, 107]] ![![-27813, 7506, -2777, -4864, -6647]]
  ![![-9165857, 2484504, -907262, -1598398, -2164770]] where
 M := ![![![-9165857, 2484504, -907262, -1598398, -2164770]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI163N1 : IdealMulLeCertificate' Table 
  ![![-9165857, 2484504, -907262, -1598398, -2164770]] ![![1270019, -974656, 118198, 365850, 508554]]
  ![![163, 0, 0, 0, 0]] where
 M := ![![![-163, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC163 : ContainsPrimesAboveP 163 ![I163N0, I163N1, I163N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
    exact isPrimeI163N1
    exact isPrimeI163N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 163 (by decide) (𝕀 ⊙ MulI163N0 ⊙ MulI163N1)
instance hp167 : Fact (Nat.Prime 167) := {out := by norm_num}

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17927, -5502, 1566, 3050, 4266]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![17927, -5502, 1566, 3050, 4266]] 
 ![![167, 0, 0, 0, 0], ![0, 167, 0, 0, 0], ![0, 0, 167, 0, 0], ![164, 110, 163, 1, 0], ![81, 35, 43, 0, 1]] where
  M :=![![![17927, -5502, 1566, 3050, 4266], ![25596, -7319, 1814, 3750, 5502], ![33012, -7354, 1933, 3874, 5994], ![5184, 2090, 350, -125, -120], ![-12480, 2442, -492, -1114, -1921]]]
  hmulB := by decide  
  f := ![![![1345, -2030, 850, -402, -150]], ![![-900, 2843, -2582, 794, -1962]], ![![-11772, 11046, 1675, 1142, 10650]], ![![-10568, 10402, 845, 1197, 8886]], ![![-2721, 2689, 203, 312, 2273]]]
  g := ![![![-4957, -2936, -4066, 3050, 4266], ![-6198, -3667, -5066, 3750, 5502], ![-6514, -3852, -5313, 3874, 5994], ![212, 120, 155, -125, -120], ![1951, 1151, 1579, -1114, -1921]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [59, 84, 11, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [63, 27, 69], [93, 139, 98], [0, 1]]
 g := ![![[98, 28, 77], [79, 161, 48], [13, 9, 47], [165, 29], [87, 12], [37, 156, 1], []], ![[119, 48, 9, 109], [1, 64, 114, 164], [27, 6, 13, 23], [0, 44], [76, 127], [23, 53, 65, 155], [119, 85]], ![[95, 45, 162, 130], [107, 88, 75, 18], [23, 103, 72, 32], [129, 115], [131, 49], [138, 58, 39, 133], [90, 85]]]
 h' := ![![[63, 27, 69], [15, 12, 113], [68, 71, 86], [58, 18, 61], [21, 65, 14], [155, 46, 124], [0, 0, 1], [0, 1]], ![[93, 139, 98], [82, 125, 2], [84, 32, 153], [56, 83, 35], [132, 50, 85], [21, 97, 36], [121, 81, 139], [63, 27, 69]], ![[0, 1], [16, 30, 52], [72, 64, 95], [1, 66, 71], [40, 52, 68], [134, 24, 7], [166, 86, 27], [93, 139, 98]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43, 128], []]
 b := ![[], [140, 46, 124], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [59, 84, 11, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-407303417, 557081736, -200606053, 101740762, 67351685]
  a := ![1, 44, 49, 114, 175]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-135019610, -77794677, -117847142, 101740762, 67351685]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 4657463 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2236761, -1381392, -32154, 292732, 550156]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![2236761, -1381392, -32154, 292732, 550156]] 
 ![![167, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![163, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![137, 0, 0, 0, 1]] where
  M :=![![![2236761, -1381392, -32154, 292732, 550156], ![3300936, -1353753, -538504, -286424, 105924], ![635544, 1734540, -1534253, -2148128, -2036316], ![-7759416, 6280564, -955700, -2576917, -3442872], ![-219244, -1069068, 866772, 1234816, 1187687]]]
  hmulB := by decide  
  f := ![![![-384833, 490280, -135262, 82548, 141916]], ![![490, -2697, 2660, -848, 2116]], ![![-373117, 483164, -142011, 82788, 126248]], ![![-46269, 53396, -7282, 8007, 27396]], ![![-272443, 345300, -94926, 57756, 100075]]]
  g := ![![![-395263, -1381392, -32154, 292732, 550156], ![479834, -1353753, -538504, -286424, 105924], ![3189637, 1734540, -1534253, -2148128, -2036316], ![3681813, 6280564, -955700, -2576917, -3442872], ![-1831033, -1069068, 866772, 1234816, 1187687]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1

def I167N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-71255, 44013, 716, -9674, -17825]] i)))

def SI167N2: IdealEqSpanCertificate' Table ![![-71255, 44013, 716, -9674, -17825]] 
 ![![167, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![131, 0, 1, 0, 0], ![105, 0, 0, 1, 0], ![98, 0, 0, 0, 1]] where
  M :=![![![-71255, 44013, 716, -9674, -17825], ![-106950, 44562, 16514, 8060, -4569], ![-27414, -50393, 48053, 66346, 62067], ![239676, -196023, 30753, 81475, 108222], ![10778, 31375, -27192, -38224, -36330]]]
  hmulB := by decide  
  f := ![![![-1182261, 958723, 372464, 61422, 1278787]], ![![3468, -23638, 27148, -7544, 25179]], ![![-1051995, 947370, 203573, 87992, 1006912]], ![![-754935, 531870, 346761, 10819, 928155]], ![![-550748, 442573, 178990, 27184, 601328]]]
  g := ![![![13973, 44013, 716, -9674, -17825], ![-17582, 44562, 16514, 8060, -4569], ![-114185, -50393, 48053, 66346, 62067], ![-130380, -196023, 30753, 81475, 108222], ![65620, 31375, -27192, -38224, -36330]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N2 : Nat.card (O ⧸ I167N2) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N2)

lemma isPrimeI167N2 : Ideal.IsPrime I167N2 := prime_ideal_of_norm_prime hp167.out _ NI167N2
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![17927, -5502, 1566, 3050, 4266]] ![![2236761, -1381392, -32154, 292732, 550156]]
  ![![-1669587225, -4499626, 766548404, 867871170, 656895050]] where
 M := ![![![-1669587225, -4499626, 766548404, 867871170, 656895050]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI167N1 : IdealMulLeCertificate' Table 
  ![![-1669587225, -4499626, 766548404, 867871170, 656895050]] ![![-71255, 44013, 716, -9674, -17825]]
  ![![167, 0, 0, 0, 0]] where
 M := ![![![313521420160639, -261825356753669, 44392571071958, 112573387425424, 147416067461127]]]
 hmul := by decide  
 g := ![![![![1877373773417, -1567816507507, 265823778874, 674092140272, 882730942881]]]]
 hle2 := by decide  


def PBC167 : ContainsPrimesAboveP 167 ![I167N0, I167N1, I167N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
    exact isPrimeI167N1
    exact isPrimeI167N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 167 (by decide) (𝕀 ⊙ MulI167N0 ⊙ MulI167N1)
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


def P173P0 : CertificateIrreducibleZModOfList' 173 5 2 7 [16, 48, 29, 3, 92, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 170, 85, 83, 125], [143, 49, 112, 91, 71], [19, 135, 40, 67, 139], [64, 164, 109, 105, 11], [0, 1]]
 g := ![![[128, 14, 166, 36, 43], [66, 0, 49, 83], [122, 85, 162, 171, 9], [13, 31, 6, 109, 122], [70, 95, 18, 160], [1], []], ![[64, 4, 54, 119, 129, 109, 61, 102], [4, 146, 153, 34], [137, 114, 89, 134, 133, 109, 166, 120], [167, 60, 17, 40, 7, 47, 23, 147], [22, 151, 66, 167], [70, 104, 131, 108, 25, 148, 29, 156], [97, 153, 120, 55]], ![[129, 128, 14, 105, 127, 127, 79, 111], [53, 29, 112, 118], [55, 52, 116, 26, 56, 78, 126, 28], [18, 154, 74, 55, 43, 0, 93, 170], [138, 147, 89, 22], [92, 69, 25, 36, 89, 122, 156, 143], [6, 132, 161, 24]], ![[89, 39, 49, 11, 99, 167, 61, 109], [29, 20, 113, 55], [138, 124, 160, 28, 165, 136, 81, 132], [5, 162, 4, 138, 115, 151, 92, 144], [92, 5, 27, 118], [83, 162, 71, 148, 35, 69, 153, 121], [7, 27, 158, 118]], ![[56, 128, 22, 144, 103, 148, 11, 108], [34, 74, 5, 43], [146, 57, 93, 115, 160, 77, 14, 102], [90, 125, 1, 144, 163, 154, 50, 107], [33, 62, 17, 163], [94, 138, 118, 145, 22, 77, 15, 102], [102, 166, 1, 121]]]
 h' := ![![[28, 170, 85, 83, 125], [134, 75, 151, 171, 40], [124, 64, 131, 68, 157], [138, 92, 1, 80, 3], [1, 116, 160, 124, 45], [157, 125, 144, 170, 81], [0, 0, 1], [0, 1]], ![[143, 49, 112, 91, 71], [45, 38, 2, 120, 148], [52, 28, 8, 37, 42], [122, 136, 81, 147, 118], [111, 125, 53, 71, 33], [64, 70, 82, 148, 72], [97, 167, 131, 36, 127], [28, 170, 85, 83, 125]], ![[19, 135, 40, 67, 139], [72, 73, 113, 38, 2], [48, 124, 74, 144, 139], [130, 149, 11, 98, 153], [84, 116, 73, 58, 70], [40, 105, 84, 63, 117], [112, 23, 89, 132, 53], [143, 49, 112, 91, 71]], ![[64, 164, 109, 105, 11], [33, 34, 137, 115, 132], [155, 38, 61, 153, 48], [51, 41, 31, 81, 77], [169, 1, 64, 156, 97], [118, 162, 129, 102, 139], [76, 37, 148, 129, 161], [19, 135, 40, 67, 139]], ![[0, 1], [138, 126, 116, 75, 24], [63, 92, 72, 117, 133], [140, 101, 49, 113, 168], [45, 161, 169, 110, 101], [153, 57, 80, 36, 110], [42, 119, 150, 49, 5], [64, 164, 109, 105, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52, 40, 171, 171], [], [], []]
 b := ![[], [63, 70, 62, 80, 36], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 5
  hpos := by decide
  P := [16, 48, 29, 3, 92, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![13441151154685, -17219668003600, 4335569871998, -2934066365697, -5760149437770]
  a := ![-1, -7, -13, -23, -54]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![77694515345, -99535653200, 25061097526, -16959921189, -33295661490]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3987, 1013, -340, -618, -869]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![-3987, 1013, -340, -618, -869]] 
 ![![179, 0, 0, 0, 0], ![0, 179, 0, 0, 0], ![0, 0, 179, 0, 0], ![14, 87, 172, 1, 0], ![145, 131, 151, 0, 1]] where
  M :=![![![-3987, 1013, -340, -618, -869], ![-5214, 1138, -474, -796, -1101], ![-6606, 1223, -759, -1134, -1473], ![-1812, 337, -455, -589, -642], ![2234, -289, 284, 384, 482]]]
  hmulB := by decide  
  f := ![![![91, -89, -8, -10, -77]], ![![-462, 612, -176, 108, 171]], ![![1026, -1727, 891, -370, 135]], ![![772, -1369, 765, -303, 199]], ![![591, -1071, 617, -240, 185]]]
  g := ![![![730, 942, 1325, -618, -869], ![925, 1199, 1691, -796, -1101], ![1245, 1636, 2328, -1134, -1473], ![556, 758, 1105, -589, -642], ![-408, -541, -774, 384, 482]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 3 2 7 [96, 136, 163, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [41, 1, 86], [154, 177, 93], [0, 1]]
 g := ![![[35, 118, 47], [120, 160, 101], [115, 36], [117, 42], [153, 30, 36], [120, 16, 1], []], ![[131, 156, 54, 136], [61, 47, 26, 38], [147, 158], [177, 88], [46, 62, 16, 35], [147, 57, 150, 165], [10, 57]], ![[42, 66, 32, 156], [126, 171, 152, 1], [172, 142], [33, 25], [52, 97, 20, 100], [72, 126, 48, 93], [3, 57]]]
 h' := ![![[41, 1, 86], [115, 92, 88], [140, 70, 97], [145, 113, 173], [169, 98, 20], [115, 44, 6], [0, 0, 1], [0, 1]], ![[154, 177, 93], [31, 14, 39], [94, 102, 98], [94, 159, 64], [170, 64, 154], [159, 177, 13], [5, 52, 177], [41, 1, 86]], ![[0, 1], [84, 73, 52], [112, 7, 163], [131, 86, 121], [163, 17, 5], [142, 137, 160], [158, 127, 1], [154, 177, 93]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62, 108], []]
 b := ![[], [143, 61, 82], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 3
  hpos := by decide
  P := [96, 136, 163, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-107616, -8394608, 11523132, -2854340, 11959752]
  a := ![0, -4, 10, -2, 36]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9465424, -7412260, -7281860, -2854340, 11959752]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 5735339 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![91, -89, -8, -10, -77]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![91, -89, -8, -10, -77]] 
 ![![179, 0, 0, 0, 0], ![0, 179, 0, 0, 0], ![23, 14, 1, 0, 0], ![18, 93, 0, 1, 0], ![108, 155, 0, 0, 1]] where
  M :=![![![91, -89, -8, -10, -77], ![-462, 612, -176, 108, 171], ![1026, -1727, 891, -370, 135], ![636, -5, -893, 147, -1398], ![-1810, 1801, 118, 212, 1494]]]
  hmulB := by decide  
  f := ![![![-3987, 1013, -340, -618, -869]], ![![-5214, 1138, -474, -796, -1101]], ![![-957, 226, -85, -148, -206]], ![![-3120, 695, -283, -479, -663]], ![![-6908, 1595, -614, -1060, -1475]]]
  g := ![![![49, 72, -8, -10, -77], ![-94, -187, -176, 108, 171], ![-153, -4, 891, -370, 135], ![947, 1204, -893, 147, -1398], ![-948, -1403, 118, 212, 1494]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P1 : CertificateIrreducibleZModOfList' 179 2 2 7 [76, 165, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 178], [0, 1]]
 g := ![![[127, 106], [89, 48], [13], [67], [7, 70], [79, 17], [1]], ![[0, 73], [45, 131], [13], [67], [92, 109], [138, 162], [1]]]
 h' := ![![[14, 178], [38, 74], [68, 76], [124, 27], [5, 70], [82, 41], [103, 14], [0, 1]], ![[0, 1], [0, 105], [58, 103], [144, 152], [90, 109], [119, 138], [120, 165], [14, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [126]]
 b := ![[], [96, 63]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N1 : CertifiedPrimeIdeal' SI179N1 179 where
  n := 2
  hpos := by decide
  P := [76, 165, 1]
  hirr := P179P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![26458, -28010, 521, -9704, -24855]
  a := ![13, -8, -12, -24, -49]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![16053, 26367, 521, -9704, -24855]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N1 B_one_repr
lemma NI179N1 : Nat.card (O ⧸ I179N1) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![-3987, 1013, -340, -618, -869]] ![![91, -89, -8, -10, -77]]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5871, -3965, 159, 1126, 1796]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![5871, -3965, 159, 1126, 1796]] 
 ![![181, 0, 0, 0, 0], ![0, 181, 0, 0, 0], ![0, 0, 181, 0, 0], ![40, 114, 140, 1, 0], ![44, 53, 143, 0, 1]] where
  M :=![![![5871, -3965, 159, 1126, 1796], ![10776, -5416, -1043, 104, 1368], ![8208, 261, -3944, -4510, -3480], ![-15828, 14765, -3343, -7281, -8994], ![-4244, -439, 2251, 2618, 2065]]]
  hmulB := by decide  
  f := ![![![935491, -253141, 92719, 163312, 221620]], ![![1329720, -359818, 131791, 232134, 315012]], ![![1890072, -511439, 187328, 329960, 447768]], ![![2509924, -679171, 248763, 438169, 594610]], ![![2106088, -569894, 208738, 367670, 498941]]]
  g := ![![![-653, -1257, -2289, 1126, 1796], ![-296, -496, -1167, 104, 1368], ![1888, 3861, 6216, -4510, -3480], ![3708, 7301, 12719, -7281, -8994], ![-1104, -2256, -3644, 2618, 2065]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [114, 114, 8, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [115, 165, 174], [58, 15, 7], [0, 1]]
 g := ![![[153, 147, 169], [133, 165], [138, 68, 144], [172, 99], [75, 68, 55], [131, 173, 1], []], ![[42, 146, 15, 26], [46, 33], [161, 88, 170, 150], [99, 138], [108, 84, 79, 128], [55, 17, 141, 54], [13, 49]], ![[151, 179, 53, 120], [65, 45], [132, 11, 1, 97], [126, 79], [63, 120, 149, 128], [27, 54, 112, 163], [180, 49]]]
 h' := ![![[115, 165, 174], [86, 5, 168], [15, 125, 105], [160, 81, 12], [138, 126, 113], [89, 96, 112], [0, 0, 1], [0, 1]], ![[58, 15, 7], [42, 93, 132], [134, 167, 157], [161, 48, 156], [15, 142, 89], [158, 148, 103], [159, 112, 15], [115, 165, 174]], ![[0, 1], [50, 83, 62], [138, 70, 100], [77, 52, 13], [88, 94, 160], [70, 118, 147], [39, 69, 165], [58, 15, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [98, 158], []]
 b := ![[], [172, 173, 126], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [114, 114, 8, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![124531, -140004, 24429, -11210, -40995]
  a := ![-1, -4, -1, -8, -3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![13131, 18291, 41194, -11210, -40995]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 5929741 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![935491, -253141, 92719, 163312, 221620]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![935491, -253141, 92719, 163312, 221620]] 
 ![![181, 0, 0, 0, 0], ![0, 181, 0, 0, 0], ![162, 82, 1, 0, 0], ![55, 68, 0, 1, 0], ![10, 58, 0, 0, 1]] where
  M :=![![![935491, -253141, 92719, 163312, 221620], ![1329720, -359818, 131791, 232134, 315012], ![1890072, -511439, 187328, 329960, 447768], ![678444, -183599, 67249, 118433, 160722], ![-715132, 193521, -70885, -124840, -169419]]]
  hmulB := by decide  
  f := ![![![5871, -3965, 159, 1126, 1796]], ![![10776, -5416, -1043, 104, 1368]], ![![10182, -6001, -352, 1030, 2208]], ![![5745, -3158, -362, 341, 1010]], ![![3754, -1957, -313, 110, 549]]]
  g := ![![![-139687, -175775, 92719, 163312, 221620], ![-198552, -249848, 131791, 232134, 315012], ![-282224, -355139, 187328, 329960, 447768], ![-101309, -127477, 67249, 118433, 160722], ![106788, 134373, -70885, -124840, -169419]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P1 : CertificateIrreducibleZModOfList' 181 2 2 7 [71, 136, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [45, 180], [0, 1]]
 g := ![![[58, 148], [121], [142, 37], [126], [82, 52], [27, 34], [1]], ![[21, 33], [121], [178, 144], [126], [69, 129], [109, 147], [1]]]
 h' := ![![[45, 180], [117, 94], [54, 170], [99, 134], [151, 44], [74, 41], [110, 45], [0, 1]], ![[0, 1], [3, 87], [102, 11], [156, 47], [140, 137], [109, 140], [144, 136], [45, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [84]]
 b := ![[], [141, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N1 : CertifiedPrimeIdeal' SI181N1 181 where
  n := 2
  hpos := by decide
  P := [71, 136, 1]
  hirr := P181P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![16112, -12074, -3125, 631, -11634]
  a := ![3, 3, 14, 13, 42]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3337, 4840, -3125, 631, -11634]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N1 B_one_repr
lemma NI181N1 : Nat.card (O ⧸ I181N1) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![5871, -3965, 159, 1126, 1796]] ![![935491, -253141, 92719, 163312, 221620]]
  ![![181, 0, 0, 0, 0]] where
 M := ![![![181, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC181 : ContainsPrimesAboveP 181 ![I181N0, I181N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
    exact isPrimeI181N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 181 (by decide) (𝕀 ⊙ MulI181N0)
instance hp191 : Fact (Nat.Prime 191) := {out := by norm_num}

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0, 0, 0]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0, 0, 0]] 
 ![![191, 0, 0, 0, 0], ![0, 191, 0, 0, 0], ![0, 0, 191, 0, 0], ![0, 0, 0, 191, 0], ![0, 0, 0, 0, 191]] where
  M :=![![![191, 0, 0, 0, 0], ![0, 191, 0, 0, 0], ![0, 0, 191, 0, 0], ![0, 0, 0, 191, 0], ![0, 0, 0, 0, 191]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 5 2 7 [175, 52, 19, 92, 171, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [79, 126, 172, 180, 40], [56, 52, 41, 174, 36], [138, 54, 44, 101, 189], [129, 149, 125, 118, 117], [0, 1]]
 g := ![![[184, 190, 72, 53, 97], [104, 113, 77, 130, 75], [60, 1, 141, 150, 138], [5, 52, 144, 163, 107], [163, 39, 4, 118, 18], [1], []], ![[50, 139, 77, 184, 171, 22, 92, 85], [139, 123, 184, 90, 76, 38, 17, 67], [15, 165, 82, 68, 178, 17, 68, 72], [174, 130, 14, 94, 1, 37, 10, 85], [91, 179, 48, 4, 89, 78, 162, 120], [6, 14, 66, 169, 187, 58, 74, 162], [140, 121, 178, 72]], ![[44, 75, 135, 190, 110, 18, 159, 5], [29, 20, 121, 2, 152, 65, 2, 45], [45, 79, 66, 50, 181, 152, 100, 39], [84, 129, 109, 189, 87, 46, 149, 64], [125, 8, 158, 134, 143, 182, 92, 13], [108, 24, 149, 57, 164, 140, 142, 180], [123, 131, 57, 150]], ![[3, 68, 43, 72, 137, 11, 65, 11], [154, 174, 62, 58, 110, 72, 13, 165], [99, 152, 103, 67, 35, 165, 24, 33], [28, 154, 5, 172, 64, 85, 68, 55], [54, 174, 176, 131, 130, 41, 6, 167], [187, 121, 69, 33, 115, 133, 155, 159], [141, 121, 58, 4]], ![[132, 119, 67, 51, 6, 73, 90, 177], [120, 82, 93, 15, 43, 184, 156, 24], [136, 14, 155, 4, 93, 123, 79, 135], [23, 9, 33, 69, 189, 70, 108, 1], [150, 21, 121, 56, 15, 57, 27, 78], [147, 140, 173, 159, 92, 128, 65, 50], [64, 145, 185, 128]]]
 h' := ![![[79, 126, 172, 180, 40], [136, 54, 173, 104, 80], [5, 49, 141, 141, 71], [80, 153, 0, 124, 105], [125, 44, 151, 72, 38], [16, 139, 172, 99, 20], [0, 0, 1], [0, 1]], ![[56, 52, 41, 174, 36], [39, 179, 152, 105, 44], [12, 48, 176, 77, 187], [140, 145, 187, 48, 68], [127, 55, 69, 104, 44], [155, 46, 167, 66, 24], [77, 48, 85, 178, 102], [79, 126, 172, 180, 40]], ![[138, 54, 44, 101, 189], [62, 49, 18, 133, 125], [122, 71, 161, 48, 7], [101, 150, 51, 138, 141], [88, 64, 61, 48, 65], [120, 129, 40, 79, 173], [138, 187, 14, 24, 177], [56, 52, 41, 174, 36]], ![[129, 149, 125, 118, 117], [180, 83, 180, 166, 89], [12, 106, 76, 99, 83], [78, 74, 93, 109, 156], [5, 129, 142, 163, 100], [3, 147, 109, 153, 48], [99, 149, 141, 80, 187], [138, 54, 44, 101, 189]], ![[0, 1], [144, 17, 50, 65, 44], [2, 108, 19, 17, 34], [142, 51, 51, 154, 103], [172, 90, 150, 186, 135], [150, 112, 85, 176, 117], [93, 189, 141, 100, 107], [129, 149, 125, 118, 117]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46, 56, 146, 76], [], [], []]
 b := ![[], [19, 142, 71, 62, 170], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 5
  hpos := by decide
  P := [175, 52, 19, 92, 171, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-728785462554, 1059775380582, -405845212977, 203402435256, 137516671825]
  a := ![1, 6, 9, 18, 37]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3815630694, 5548562202, -2124844047, 1064934216, 719982575]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 254194901951 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def PBC191 : ContainsPrimesAboveP 191 ![I191N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI191N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![191, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 191 (by decide) 𝕀

instance hp193 : Fact (Nat.Prime 193) := {out := by norm_num}

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![606163, -163675, 59923, 105954, 143692]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![606163, -163675, 59923, 105954, 143692]] 
 ![![193, 0, 0, 0, 0], ![0, 193, 0, 0, 0], ![1, 90, 1, 0, 0], ![148, 4, 0, 1, 0], ![86, 173, 0, 0, 1]] where
  M :=![![![606163, -163675, 59923, 105954, 143692], ![862152, -233804, 85971, 150324, 204648], ![1227888, -334089, 121168, 213618, 288000], ![432924, -109761, 40779, 78433, 106530], ![-458272, 117267, -42379, -82574, -110205]]]
  hmulB := by decide  
  f := ![![![-1250925, 355065, 317327, 274240, 122684]], ![![736104, -1518146, 751989, 1212006, 1277388]], ![![376491, -738444, 357345, 580000, 614132]], ![![-892440, 211435, 256415, 239579, 130694]], ![![79522, -1184181, 812716, 1201114, 1189631]]]
  g := ![![![-142448, -159789, 59923, 105954, 143692], ![-202443, -227858, 85971, 150324, 204648], ![-286408, -320817, 121168, 213618, 288000], ![-105583, -116701, 40779, 78433, 106530], ![110273, 120866, -42379, -82574, -110205]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [53, 174, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 192], [0, 1]]
 g := ![![[189, 86], [191], [72], [84], [55], [101], [19, 1]], ![[86, 107], [191], [72], [84], [55], [101], [38, 192]]]
 h' := ![![[19, 192], [192, 47], [47, 159], [179, 119], [81, 85], [78, 172], [151, 115], [0, 1]], ![[0, 1], [120, 146], [173, 34], [124, 74], [152, 108], [65, 21], [20, 78], [19, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [158]]
 b := ![[], [118, 79]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [53, 174, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1053, -146, -584, -167, -1554]
  a := ![4, 0, -2, -1, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![829, 1668, -584, -167, -1554]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-170017, 78426, 21498, 5626, -14424]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![-170017, 78426, 21498, 5626, -14424]] 
 ![![193, 0, 0, 0, 0], ![0, 193, 0, 0, 0], ![177, 2, 1, 0, 0], ![16, 87, 0, 1, 0], ![98, 123, 0, 0, 1]] where
  M :=![![![-170017, 78426, 21498, 5626, -14424], ![-86544, -41925, 69628, 88722, 77028], ![462168, -467390, 123825, 251366, 301248], ![947016, -614726, 7798, 155265, 263712], ![-272400, 269598, -68766, -141986, -171493]]]
  hmulB := by decide  
  f := ![![![-9497761, 2570078, -941386, -1658054, -2250096]], ![![-13500576, 3653471, -1338072, -2356742, -3198036]], ![![-8949705, 2421770, -887061, -1562380, -2120256]], ![![-6908824, 1869631, -684758, -1206049, -1636596]], ![![-13389074, 3623211, -1327038, -2337312, -3171745]]]
  g := ![![![-13739, 6840, 21498, 5626, -14424], ![-110772, -90023, 69628, 88722, 77028], ![-284969, -309002, 123825, 251366, 301248], ![-149022, -241321, 7798, 155265, 263712], ![160504, 175407, -68766, -141986, -171493]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P1 : CertificateIrreducibleZModOfList' 193 2 2 7 [96, 55, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [138, 192], [0, 1]]
 g := ![![[83, 191], [137], [139], [184], [143], [191], [138, 1]], ![[0, 2], [137], [139], [184], [143], [191], [83, 192]]]
 h' := ![![[138, 192], [133, 34], [57, 41], [85, 77], [147, 143], [128, 170], [69, 34], [0, 1]], ![[0, 1], [0, 159], [118, 152], [96, 116], [2, 50], [42, 23], [129, 159], [138, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [76]]
 b := ![[], [80, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N1 : CertifiedPrimeIdeal' SI193N1 193 where
  n := 2
  hpos := by decide
  P := [96, 55, 1]
  hirr := P193P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![151450, -142455, -7497, -24946, -110362]
  a := ![7, -19, -43, -59, -124]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![65767, 80919, -7497, -24946, -110362]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N1 B_one_repr
lemma NI193N1 : Nat.card (O ⧸ I193N1) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N1

def I193N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-27, 11, -3, -6, -8]] i)))

def SI193N2: IdealEqSpanCertificate' Table ![![-27, 11, -3, -6, -8]] 
 ![![193, 0, 0, 0, 0], ![101, 1, 0, 0, 0], ![28, 0, 1, 0, 0], ![176, 0, 0, 1, 0], ![48, 0, 0, 0, 1]] where
  M :=![![![-27, 11, -3, -6, -8], ![-48, 20, -3, -8, -12], ![-72, 25, 0, -6, -12], ![-12, -7, 5, 7, 6], ![32, -11, -1, 2, 5]]]
  hmulB := by decide  
  f := ![![![-43, 55, -31, 4, -16]], ![![-23, 29, -16, 2, -8]], ![![-4, 5, -4, 0, -4]], ![![-44, 57, -31, 5, -14]], ![![-8, 9, -5, 0, -3]]]
  g := ![![![2, 11, -3, -6, -8], ![0, 20, -3, -8, -12], ![-5, 25, 0, -6, -12], ![-5, -7, 5, 7, 6], ![3, -11, -1, 2, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N2 : Nat.card (O ⧸ I193N2) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N2)

lemma isPrimeI193N2 : Ideal.IsPrime I193N2 := prime_ideal_of_norm_prime hp193.out _ NI193N2
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![606163, -163675, 59923, 105954, 143692]] ![![-170017, 78426, 21498, 5626, -14424]]
  ![![-43, 55, -31, 4, -16]] where
 M := ![![![-43, 55, -31, 4, -16]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI193N1 : IdealMulLeCertificate' Table 
  ![![-43, 55, -31, 4, -16]] ![![-27, 11, -3, -6, -8]]
  ![![193, 0, 0, 0, 0]] where
 M := ![![![193, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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


def P197P0 : CertificateIrreducibleZModOfList' 197 5 2 7 [123, 27, 4, 195, 33, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [32, 78, 10, 55, 185], [156, 89, 196, 156, 98], [186, 147, 127, 138, 78], [184, 79, 61, 45, 33], [0, 1]]
 g := ![![[59, 181, 161, 141, 23], [137, 58, 190, 132], [141, 124, 16, 103, 37], [45, 67, 150, 40], [90, 103, 98, 7], [164, 1], []], ![[103, 29, 137, 91, 191, 34, 61, 152], [114, 174, 106, 6], [164, 181, 174, 65, 127, 187, 169, 78], [104, 36, 120, 178], [50, 70], [131, 18, 4, 83], [51, 77, 179, 17, 117, 49, 14, 45]], ![[191, 178, 15, 77, 84, 191, 128, 185], [71, 1, 12, 196], [143, 106, 133, 108, 46, 63, 133, 149], [147, 131, 11, 19], [164, 118, 77, 10], [185, 14, 2, 54], [163, 11, 65, 171, 116, 6, 195, 123]], ![[3, 192, 166, 58, 183, 121, 134, 17], [170, 12, 52, 150], [77, 11, 70, 118, 162, 126, 12, 80], [160, 80, 156, 85], [73, 31, 104, 174], [16, 160, 107, 92], [56, 39, 125, 4, 190, 13, 36, 176]], ![[196, 97, 185, 33, 164, 172, 175, 6], [71, 19, 151, 43], [89, 107, 158, 176, 166, 125, 166, 144], [196, 118, 117, 143], [74, 47, 68, 55], [195, 12, 74, 100], [28, 110, 111, 21, 129, 6, 72, 83]]]
 h' := ![![[32, 78, 10, 55, 185], [140, 196, 115, 5, 90], [190, 155, 169, 122, 59], [156, 92, 182, 110, 49], [136, 38, 148, 26, 51], [119, 177, 105, 127, 106], [0, 0, 0, 1], [0, 1]], ![[156, 89, 196, 156, 98], [166, 96, 8, 75, 168], [2, 37, 120, 47, 20], [62, 40, 95, 67, 17], [190, 15, 66, 133, 104], [191, 6, 86, 142], [97, 51, 75, 112, 87], [32, 78, 10, 55, 185]], ![[186, 147, 127, 138, 78], [99, 148, 188, 77, 157], [178, 15, 68, 50, 183], [10, 82, 155, 68, 117], [19, 147, 98, 24, 120], [57, 183, 90, 120, 124], [74, 20, 79, 169, 137], [156, 89, 196, 156, 98]], ![[184, 79, 61, 45, 33], [129, 83, 22, 106, 182], [74, 168, 123, 40, 97], [163, 41, 62, 84, 57], [145, 176, 29, 159, 171], [72, 118, 85, 157, 119], [55, 166, 139, 64, 180], [186, 147, 127, 138, 78]], ![[0, 1], [113, 68, 61, 131, 191], [93, 19, 111, 135, 35], [81, 139, 97, 65, 154], [67, 18, 53, 52, 145], [111, 107, 28, 45, 45], [72, 157, 101, 48, 187], [184, 79, 61, 45, 33]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [67, 184, 144, 123], [], [], []]
 b := ![[], [38, 99, 184, 73, 158], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 5
  hpos := by decide
  P := [123, 27, 4, 195, 33, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![372033631427, -404704671301, 22534227968, -55764638310, -259185316485]
  a := ![1, -3, -9, -11, -27]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1888495591, -2054338433, 114386944, -283069230, -1315661505]
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



lemma PB687I4_primes (p : ℕ) :
  p ∈ Set.range ![157, 163, 167, 173, 179, 181, 191, 193, 197] ↔ Nat.Prime p ∧ 151 < p ∧ p ≤ 197 := by
  rw [← List.mem_ofFn']
  convert primes_range 151 197 (by omega)

def PB687I4 : PrimesBelowBoundCertificateInterval O 151 197 687 where
  m := 9
  g := ![2, 3, 3, 1, 2, 2, 1, 3, 1]
  P := ![157, 163, 167, 173, 179, 181, 191, 193, 197]
  hP := PB687I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1, I163N2]
    · exact ![I167N0, I167N1, I167N2]
    · exact ![I173N0]
    · exact ![I179N0, I179N1]
    · exact ![I181N0, I181N1]
    · exact ![I191N0]
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
    · exact ![3869893, 24649]
    · exact ![4330747, 163, 163]
    · exact ![4657463, 167, 167]
    · exact ![154963892093]
    · exact ![5735339, 32041]
    · exact ![5929741, 32761]
    · exact ![254194901951]
    · exact ![37249, 37249, 193]
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
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
      exact NI163N1
      exact NI163N2
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
      exact NI167N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
      exact NI193N2
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
  β := ![I163N1, I163N2, I167N1, I167N2, I193N2]
  Il := ![[], [I163N1, I163N2], [I167N1, I167N2], [], [], [], [], [I193N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
