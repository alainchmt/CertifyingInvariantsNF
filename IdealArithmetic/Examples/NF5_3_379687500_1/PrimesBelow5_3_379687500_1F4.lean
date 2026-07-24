
import IdealArithmetic.Examples.NF5_3_379687500_1.RI5_3_379687500_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1035833, -431548, 1881896, -846764, -2147346]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![1035833, -431548, 1881896, -846764, -2147346]] 
 ![![157, 0, 0, 0, 0], ![0, 157, 0, 0, 0], ![0, 0, 157, 0, 0], ![84, 36, 49, 1, 0], ![10, 9, 137, 0, 1]] where
  M :=![![![1035833, -431548, 1881896, -846764, -2147346], ![-453818, 189069, -824494, 370984, 940794], ![198826, -82834, 361227, -162530, -412170], ![-87110, 36296, -158254, 71237, 180630], ![82096, -34204, 149150, -67118, -170201]]]
  hmulB := by decide  
  f := ![![![-27, 172, 724, -328, -810]], ![![-154, -355, -2, 8, -6]], ![![-22, -146, -325, 170, 438]], ![![-56, -34, 285, -121, -300]], ![![-30, -137, -237, 128, 331]]]
  g := ![![![596417, 314510, 2150062, -846764, -2147346], ![-261302, -137793, -941984, 370984, 940794], ![114478, 60368, 412691, -162530, -412170], ![-50174, -26458, -180861, 71237, 180630], ![47274, 24929, 170417, -67118, -170201]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [62, 102, 58, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [112, 156, 103], [144, 0, 54], [0, 1]]
 g := ![![[140, 152, 109], [58, 100], [132], [16, 82, 121], [30, 61, 126], [99, 1], []], ![[145, 115, 103, 103], [123, 81], [113, 65, 101, 139], [111, 83, 48, 92], [40, 134, 71, 45], [], [69, 90]], ![[85, 0, 72, 98], [14, 47], [64, 67, 55, 18], [130, 113, 55, 152], [10, 144, 95, 123], [6, 1], [118, 90]]]
 h' := ![![[112, 156, 103], [101, 32, 57], [137, 26, 10], [107, 140], [24, 134, 146], [142, 45, 122], [0, 0, 1], [0, 1]], ![[144, 0, 54], [79, 65, 156], [144, 137, 9], [87, 17, 133], [94, 142, 143], [42, 91, 82], [102, 32], [112, 156, 103]], ![[0, 1], [35, 60, 101], [78, 151, 138], [14, 0, 24], [126, 38, 25], [72, 21, 110], [75, 125, 156], [144, 0, 54]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62, 40], []]
 b := ![[], [54, 113, 24], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [62, 102, 58, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![68701149, -94332243, -179309529, -886907554, -1895088615]
  a := ![5, -3, -9, -44, -105]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![595667655, 311402148, 1929339496, -886907554, -1895088615]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 3869893 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, -2, 3, 17, 66]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![-5, -2, 3, 17, 66]] 
 ![![157, 0, 0, 0, 0], ![131, 1, 0, 0, 0], ![109, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![73, 0, 0, 0, 1]] where
  M :=![![![-5, -2, 3, 17, 66], ![32, 12, -17, -104, -408], ![-200, -72, 108, 663, 2568], ![1242, 463, -651, -4029, -15810], ![-674, -249, 356, 2199, 8599]]]
  hmulB := by decide  
  f := ![![![1587, 2661, 1381, -696, -1578]], ![![1323, 2226, 1166, -587, -1332]], ![![1099, 1840, 961, -484, -1098]], ![![80, 132, 63, -32, -72]], ![![739, 1240, 645, -325, -737]]]
  g := ![![![-32, -2, 3, 17, 66], ![197, 12, -17, -104, -408], ![-1244, -72, 108, 663, 2568], ![7630, 463, -651, -4029, -15810], ![-4154, -249, 356, 2199, 8599]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1

def I157N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3109, -5897, 3809, -1546, -4236]] i)))

def SI157N2: IdealEqSpanCertificate' Table ![![-3109, -5897, 3809, -1546, -4236]] 
 ![![157, 0, 0, 0, 0], ![134, 1, 0, 0, 0], ![99, 0, 1, 0, 0], ![79, 0, 0, 1, 0], ![72, 0, 0, 0, 1]] where
  M :=![![![-3109, -5897, 3809, -1546, -4236], ![-1144, -4655, -6299, 2943, 7080], ![1194, 1799, -2906, 1252, 3246], ![742, 2446, 2309, -1098, -2598], ![-516, -1297, -354, 193, 403]]]
  hmulB := by decide  
  f := ![![![262415, -109332, 476771, -214497, -543924]], ![![223240, -93010, 405595, -182476, -462726]], ![![165791, -69076, 301223, -135512, -343626]], ![![131913, -54951, 239644, -107846, -273528]], ![![120470, -50197, 218890, -98459, -249647]]]
  g := ![![![5332, -5897, 3809, -1546, -4236], ![3210, -4655, -6299, 2943, 7080], ![-1814, 1799, -2906, 1252, 3246], ![-1795, 2446, 2309, -1098, -2598], ![1045, -1297, -354, 193, 403]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N2 : Nat.card (O ⧸ I157N2) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N2)

lemma isPrimeI157N2 : Ideal.IsPrime I157N2 := prime_ideal_of_norm_prime hp157.out _ NI157N2
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![1035833, -431548, 1881896, -846764, -2147346]] ![![-5, -2, 3, 17, 66]]
  ![![262415, -109332, 476771, -214497, -543924]] where
 M := ![![![262415, -109332, 476771, -214497, -543924]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI157N1 : IdealMulLeCertificate' Table 
  ![![262415, -109332, 476771, -214497, -543924]] ![![-3109, -5897, 3809, -1546, -4236]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 274, 619, -287, -700]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![59, 274, 619, -287, -700]] 
 ![![163, 0, 0, 0, 0], ![0, 163, 0, 0, 0], ![0, 0, 163, 0, 0], ![153, 66, 3, 1, 0], ![28, 143, 105, 0, 1]] where
  M :=![![![59, 274, 619, -287, -700], ![-126, -228, 113, -60, -154], ![-34, -186, -254, 17, 98], ![64, -17, -233, -553, -952], ![-14, 27, 122, 117, 181]]]
  hmulB := by decide  
  f := ![![![-47, -21, 35, 164, 644]], ![![316, 117, -173, -1041, -4060]], ![![-1978, -725, 1054, 6490, 25298]], ![![123, 42, -58, -396, -1540]], ![![-1046, -383, 555, 3430, 13369]]]
  g := ![![![390, 732, 460, -287, -700], ![82, 158, 101, -60, -154], ![-33, -94, -65, 17, 98], ![683, 1059, 622, -553, -952], ![-141, -206, -118, 117, 181]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [51, 26, 23, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 66, 137], [126, 96, 26], [0, 1]]
 g := ![![[102, 22, 161], [98, 52, 4], [121, 84], [42, 46], [5, 95], [14, 140, 1], []], ![[143, 92, 129, 76], [145, 112, 107, 149], [95, 55], [52, 143], [109, 61], [102, 7, 92, 157], [91, 24]], ![[55, 49, 10, 81], [22, 120, 144, 4], [141, 53], [54, 144], [157, 87], [78, 139, 126, 134], [39, 24]]]
 h' := ![![[14, 66, 137], [55, 55, 145], [56, 127, 161], [149, 27, 35], [3, 7, 32], [101, 157, 62], [0, 0, 1], [0, 1]], ![[126, 96, 26], [150, 104, 102], [129, 130, 92], [128, 144, 50], [160, 138, 119], [60, 158, 77], [119, 51, 96], [14, 66, 137]], ![[0, 1], [52, 4, 79], [20, 69, 73], [107, 155, 78], [116, 18, 12], [25, 11, 24], [32, 112, 66], [126, 96, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 89], []]
 b := ![[], [43, 103, 110], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [51, 26, 23, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![107774693667, -210958567519, -356530108292, -1739987629873, -3508762225092]
  a := ![59, -60, -118, -533, -1236]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2236633278324, 3781479896885, 2290082616049, -1739987629873, -3508762225092]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 4330747 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![165, 609, 714, -335, -800]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![165, 609, 714, -335, -800]] 
 ![![163, 0, 0, 0, 0], ![42, 1, 0, 0, 0], ![29, 0, 1, 0, 0], ![86, 0, 0, 1, 0], ![74, 0, 0, 0, 1]] where
  M :=![![![165, 609, 714, -335, -800], ![-130, -170, 404, -181, -470], ![-108, -311, -243, 147, 388], ![94, 39, -258, -72, -422], ![-26, 40, 152, 32, 215]]]
  hmulB := by decide  
  f := ![![![28575, -11701, 52320, -21895, -56648]], ![![7284, -2974, 13354, -5519, -14330]], ![![5105, -2038, 9451, -3536, -9456]], ![![14980, -5793, 28104, -9034, -25374]], ![![13008, -5416, 23640, -10608, -26921]]]
  g := ![![![257, 609, 714, -335, -800], ![280, -170, 404, -181, -470], ![-131, -311, -243, 147, 388], ![266, 39, -258, -72, -422], ![-152, 40, 152, 32, 215]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1

def I163N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5615, 2339, -10201, 4590, 11640]] i)))

def SI163N2: IdealEqSpanCertificate' Table ![![-5615, 2339, -10201, 4590, 11640]] 
 ![![163, 0, 0, 0, 0], ![118, 1, 0, 0, 0], ![94, 0, 1, 0, 0], ![155, 0, 0, 1, 0], ![86, 0, 0, 0, 1]] where
  M :=![![![-5615, 2339, -10201, 4590, 11640], ![2460, -1025, 4469, -2011, -5100], ![-1078, 449, -1958, 882, 2238], ![474, -196, 857, -392, -1002], ![-446, 185, -808, 367, 935]]]
  hmulB := by decide  
  f := ![![![35, 424, 1075, -515, -1248]], ![![24, 304, 779, -374, -906]], ![![20, 242, 616, -301, -726]], ![![35, 399, 1014, -524, -1248]], ![![18, 225, 570, -263, -643]]]
  g := ![![![-6351, 2339, -10201, 4590, 11640], ![2783, -1025, 4469, -2011, -5100], ![-1222, 449, -1958, 882, 2238], ![552, -196, 857, -392, -1002], ![-513, 185, -808, 367, 935]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N2 : Nat.card (O ⧸ I163N2) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N2)

lemma isPrimeI163N2 : Ideal.IsPrime I163N2 := prime_ideal_of_norm_prime hp163.out _ NI163N2
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![59, 274, 619, -287, -700]] ![![165, 609, 714, -335, -800]]
  ![![-101515, -242351, -29949, 19898, 34806]] where
 M := ![![![-101515, -242351, -29949, 19898, 34806]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI163N1 : IdealMulLeCertificate' Table 
  ![![-101515, -242351, -29949, 19898, 34806]] ![![-5615, 2339, -10201, 4590, 11640]]
  ![![163, 0, 0, 0, 0]] where
 M := ![![![16463, 58191, 57376, -27221, -64548]]]
 hmul := by decide  
 g := ![![![![101, 357, 352, -167, -396]]]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![12099, -3107, 16180, -15973, -51540]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![12099, -3107, 16180, -15973, -51540]] 
 ![![167, 0, 0, 0, 0], ![0, 167, 0, 0, 0], ![0, 0, 167, 0, 0], ![162, 111, 55, 1, 0], ![96, 80, 147, 0, 1]] where
  M :=![![![12099, -3107, 16180, -15973, -51540], ![-19594, -3874, 514, 53879, 205314], ![97556, 34285, -47551, -315427, -1227420], ![-596566, -217871, 315424, 1954710, 7618206], ![323846, 118018, -170468, -1060318, -4132079]]]
  hmulB := by decide  
  f := ![![![733, 2815, 3502, -1609, -3876]], ![![-658, -876, 1864, -595, -1686]], ![![-496, -1253, -975, 1865, 3672]], ![![110, 1744, 4319, -1290, -3576]], ![![-330, 95, 2049, 417, 169]]]
  g := ![![![45195, 35288, 50725, -15973, -51540], ![-170408, -134189, -198467, 53879, 205314], ![1012150, 797846, 1184022, -315427, -1227420], ![-6279086, -4949983, -7347724, 1954710, 7618206], ![3405838, 2684908, 3985405, -1060318, -4132079]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [162, 116, 64, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [129, 122, 73], [141, 44, 94], [0, 1]]
 g := ![![[126, 7, 87], [148, 108, 16], [72, 112, 77], [70, 9], [117, 127], [139, 103, 1], []], ![[57, 38, 54, 160], [133, 112, 89, 45], [165, 63, 149, 90], [158, 54], [60, 50], [22, 32, 136, 46], [68, 152]], ![[21, 97, 66, 21], [19, 46, 136, 157], [28, 135, 10, 89], [127, 84], [65, 14], [65, 57, 106, 137], [47, 152]]]
 h' := ![![[129, 122, 73], [72, 80, 134], [26, 58, 4], [166, 158, 54], [145, 52, 3], [27, 89, 36], [0, 0, 1], [0, 1]], ![[141, 44, 94], [117, 27, 46], [115, 93, 68], [151, 72, 49], [14, 63, 87], [81, 115, 65], [114, 133, 44], [129, 122, 73]], ![[0, 1], [160, 60, 154], [158, 16, 95], [162, 104, 64], [23, 52, 77], [115, 130, 66], [76, 34, 122], [141, 44, 94]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51, 28], []]
 b := ![[], [46, 26, 114], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [162, 116, 64, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![30519940, -64117263, -106192855, -516968532, -1030864589]
  a := ![4, -3, -7, -36, -83]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1094266004, 837057227, 1077030964, -516968532, -1030864589]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 4657463 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![733, 2815, 3502, -1609, -3876]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![733, 2815, 3502, -1609, -3876]] 
 ![![167, 0, 0, 0, 0], ![0, 167, 0, 0, 0], ![35, 112, 1, 0, 0], ![88, 16, 0, 1, 0], ![32, 108, 0, 0, 1]] where
  M :=![![![733, 2815, 3502, -1609, -3876], ![-658, -876, 1864, -595, -1686], ![-496, -1253, -975, 1865, 3672], ![-58, 1369, 670, 8698, 15906], ![74, -104, 196, -2452, -4585]]]
  hmulB := by decide  
  f := ![![![12099, -3107, 16180, -15973, -51540]], ![![-19594, -3874, 514, 53879, 205314]], ![![-10021, -3044, 3451, 30898, 119544]], ![![926, -3313, 10464, 8450, 38130]], ![![-8414, -2394, 2412, 25434, 98159]]]
  g := ![![![861, 329, 3502, -1609, -3876], ![242, -108, 1864, -595, -1686], ![-1485, -1907, -975, 1865, 3672], ![-7772, -11561, 670, 8698, 15906], ![2130, 3068, 196, -2452, -4585]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P1 : CertificateIrreducibleZModOfList' 167 2 2 7 [89, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [138, 166], [0, 1]]
 g := ![![[66, 152], [25, 93], [119, 87], [16], [81], [145, 6], [1]], ![[0, 15], [0, 74], [101, 80], [16], [81], [138, 161], [1]]]
 h' := ![![[138, 166], [113, 73], [97, 107], [121, 33], [84, 163], [121, 9], [78, 138], [0, 1]], ![[0, 1], [0, 94], [0, 60], [166, 134], [33, 4], [27, 158], [84, 29], [138, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42]]
 b := ![[], [54, 21]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N1 : CertifiedPrimeIdeal' SI167N1 167 where
  n := 2
  hpos := by decide
  P := [89, 29, 1]
  hirr := P167P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-493487, 515113, 1093910, 5470753, 12229814]
  a := ![-26, 23, 50, 230, 547]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5458447, -9163801, 1093910, 5470753, 12229814]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N1 B_one_repr
lemma NI167N1 : Nat.card (O ⧸ I167N1) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![12099, -3107, 16180, -15973, -51540]] ![![733, 2815, 3502, -1609, -3876]]
  ![![167, 0, 0, 0, 0]] where
 M := ![![![167, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5161, -2156, 9361, -4213, -10686]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![5161, -2156, 9361, -4213, -10686]] 
 ![![173, 0, 0, 0, 0], ![0, 173, 0, 0, 0], ![0, 0, 173, 0, 0], ![0, 0, 0, 173, 0], ![142, 171, 74, 72, 1]] where
  M :=![![![5161, -2156, 9361, -4213, -10686], ![-2260, 948, -4109, 1856, 4716], ![1004, -404, 1800, -853, -2220], ![-514, 151, -743, 619, 1914], ![452, -155, 718, -475, -1393]]]
  hmulB := by decide  
  f := ![![![9, 19, -5, 2, 6]], ![![2, 11, 19, -7, -18]], ![![-4, -5, 8, 8, 12]], ![![-4, 4, 7, 72, 132]], ![![6, 26, 21, 28, 47]]]
  g := ![![![8801, 10550, 4625, 4423, -10686], ![-3884, -4656, -2041, -1952, 4716], ![1828, 2192, 960, 919, -2220], ![-1574, -1891, -823, -793, 1914], ![1146, 1376, 600, 577, -1393]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 4 2 7 [147, 6, 13, 45, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 98, 106, 10], [104, 104, 108, 119], [9, 143, 132, 44], [0, 1]]
 g := ![![[127, 144, 144, 118], [154, 137, 41], [43, 15, 96, 139], [84, 161, 93, 41], [36, 30, 117], [128, 1], []], ![[170, 75, 103, 23, 140, 60], [166, 85, 31], [110, 51, 40, 78, 72, 137], [149, 75, 135, 89, 71, 169], [134, 106, 132], [123, 51, 64, 5, 166, 149], [145, 42, 100]], ![[56, 115, 105, 155, 4, 109], [45, 89, 92], [102, 7, 62, 96, 57, 56], [12, 116, 66, 152, 82, 10], [72, 36, 138], [43, 167, 57, 64, 117, 22], [127, 14, 148]], ![[65, 127, 71, 166, 152, 125], [80, 104, 150], [69, 39, 52, 63, 151, 76], [1, 30, 4, 141, 71, 87], [117, 51, 119], [0, 152, 4, 31, 39, 168], [129, 97, 33]]]
 h' := ![![[15, 98, 106, 10], [24, 146, 126, 34], [80, 32, 27, 120], [108, 14, 130, 73], [22, 97, 126, 53], [41, 123, 60, 109], [0, 0, 1], [0, 1]], ![[104, 104, 108, 119], [100, 63, 84, 122], [52, 127, 15, 107], [125, 41, 135, 66], [108, 137, 88, 22], [118, 103, 3, 85], [16, 48, 99, 84], [15, 98, 106, 10]], ![[9, 143, 132, 44], [107, 77, 49, 138], [119, 7, 23, 28], [134, 129, 111, 66], [54, 123, 125, 81], [36, 74, 24, 22], [105, 128, 101, 122], [104, 104, 108, 119]], ![[0, 1], [100, 60, 87, 52], [142, 7, 108, 91], [41, 162, 143, 141], [64, 162, 7, 17], [89, 46, 86, 130], [148, 170, 145, 140], [9, 143, 132, 44]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [61, 152, 122], []]
 b := ![[], [], [150, 19, 109, 124], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 4
  hpos := by decide
  P := [147, 6, 13, 45, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7882887588510, 4497926212486, 13016461071808, 66742676084820, 163619492137896]
  a := ![11, -6, -16, -92, -232]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-134345958214854, -161701937742010, -69912288769552, -67710177791004, 163619492137896]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 895745041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9, -19, 5, -2, -6]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![-9, -19, 5, -2, -6]] 
 ![![173, 0, 0, 0, 0], ![107, 1, 0, 0, 0], ![142, 0, 1, 0, 0], ![30, 0, 0, 1, 0], ![117, 0, 0, 0, 1]] where
  M :=![![![-9, -19, 5, -2, -6], ![-2, -11, -19, 7, 18], ![4, 5, -8, -8, -12], ![4, -4, -7, -72, -132], ![-2, -1, 2, 19, 35]]]
  hmulB := by decide  
  f := ![![![-5161, 2156, -9361, 4213, 10686]], ![![-3179, 1328, -5766, 2595, 6582]], ![![-4242, 1772, -7694, 3463, 8784]], ![![-892, 373, -1619, 727, 1842]], ![![-3493, 1459, -6335, 2852, 7235]]]
  g := ![![![12, -19, 5, -2, -6], ![9, -11, -19, 7, 18], ![13, 5, -8, -8, -12], ![110, -4, -7, -72, -132], ![-28, -1, 2, 19, 35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![5161, -2156, 9361, -4213, -10686]] ![![-9, -19, 5, -2, -6]]
  ![![173, 0, 0, 0, 0]] where
 M := ![![![-173, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC173 : ContainsPrimesAboveP 173 ![I173N0, I173N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
    exact isPrimeI173N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 173 (by decide) (𝕀 ⊙ MulI173N0)
instance hp179 : Fact (Nat.Prime 179) := {out := by norm_num}

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2617, -1055, 4733, -2130, -5400]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![2617, -1055, 4733, -2130, -5400]] 
 ![![179, 0, 0, 0, 0], ![0, 179, 0, 0, 0], ![0, 0, 179, 0, 0], ![0, 0, 0, 179, 0], ![50, 65, 63, 71, 1]] where
  M :=![![![2617, -1055, 4733, -2130, -5400], ![-1140, 487, -2045, 923, 2340], ![494, -217, 916, -394, -1014], ![-226, 100, -385, 302, 690], ![210, -85, 372, -203, -497]]]
  hmulB := by decide  
  f := ![![![-1, -6, -11, 5, 12]], ![![2, 4, -3, 2, 6]], ![![2, 4, 4, -5, -18]], ![![-8, -3, 7, 27, 96]], ![![-2, 0, 0, 11, 37]]]
  g := ![![![1523, 1955, 1927, 2130, -5400], ![-660, -847, -835, -923, 2340], ![286, 367, 362, 400, -1014], ![-194, -250, -245, -272, 690], ![140, 180, 177, 196, -497]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 4 2 7 [46, 122, 56, 119, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [167, 14, 66, 115], [159, 141, 144, 143], [92, 23, 148, 100], [0, 1]]
 g := ![![[117, 149, 159, 101], [131, 156, 61, 93], [149, 27, 161], [160, 148, 25], [33, 130, 178, 43], [60, 1], []], ![[108, 55, 116, 78, 5, 79], [86, 16, 45, 129, 34, 163], [119, 150, 19], [44, 121, 172], [45, 109, 17, 177, 122, 115], [110, 8, 116, 79, 48, 119], [146, 137, 158]], ![[148, 86, 75, 91, 18, 170], [136, 44, 176, 79, 44, 79], [171, 29, 51], [17, 49, 116], [34, 16, 41, 74, 98, 160], [99, 15, 26, 41, 173, 123], [31, 88, 43]], ![[35, 60, 59, 103, 65, 126], [86, 157, 104, 132, 112, 46], [10, 178, 75], [118, 98, 76], [95, 175, 122, 82, 64, 151], [57, 122, 150, 78, 96, 101], [122, 57, 155]]]
 h' := ![![[167, 14, 66, 115], [60, 14, 72, 97], [170, 26, 118, 123], [36, 106, 125, 124], [93, 94, 171, 174], [104, 152, 98, 143], [0, 0, 1], [0, 1]], ![[159, 141, 144, 143], [94, 165, 25, 133], [162, 172, 81, 89], [96, 36, 49, 52], [35, 80, 5, 72], [65, 41, 115, 1], [51, 73, 106, 53], [167, 14, 66, 115]], ![[92, 23, 148, 100], [27, 34, 75, 90], [14, 165, 53, 58], [2, 86, 105, 87], [28, 98, 59, 37], [23, 42, 71, 128], [48, 134, 29, 82], [159, 141, 144, 143]], ![[0, 1], [110, 145, 7, 38], [96, 174, 106, 88], [52, 130, 79, 95], [17, 86, 123, 75], [65, 123, 74, 86], [167, 151, 43, 44], [92, 23, 148, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [2, 154, 98], []]
 b := ![[], [], [103, 85, 1, 132], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 4
  hpos := by decide
  P := [46, 122, 56, 119, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1029537329162, -376360438604, 548503849888, 3380865059656, 13168468123608]
  a := ![-4, 2, 8, 24, 84]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3684094656478, -4783948538956, -4631647977304, -5204359618528, 13168468123608]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 1026625681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 6, 11, -5, -12]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![1, 6, 11, -5, -12]] 
 ![![179, 0, 0, 0, 0], ![78, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![23, 0, 0, 1, 0], ![61, 0, 0, 0, 1]] where
  M :=![![![1, 6, 11, -5, -12], ![-2, -4, 3, -2, -6], ![-2, -4, -4, 5, 18], ![8, 3, -7, -27, -96], ![-4, -1, 4, 13, 49]]]
  hmulB := by decide  
  f := ![![![-2617, 1055, -4733, 2130, 5400]], ![![-1134, 457, -2051, 923, 2340]], ![![-32, 13, -58, 26, 66]], ![![-335, 135, -606, 272, 690]], ![![-893, 360, -1615, 727, 1843]]]
  g := ![![![2, 6, 11, -5, -12], ![4, -4, 3, -2, -6], ![-5, -4, -4, 5, 18], ![35, 3, -7, -27, -96], ![-18, -1, 4, 13, 49]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![2617, -1055, 4733, -2130, -5400]] ![![1, 6, 11, -5, -12]]
  ![![179, 0, 0, 0, 0]] where
 M := ![![![-179, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17143, -7143, 31145, -14018, -35546]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![17143, -7143, 31145, -14018, -35546]] 
 ![![181, 0, 0, 0, 0], ![0, 181, 0, 0, 0], ![0, 0, 181, 0, 0], ![38, 109, 166, 1, 0], ![24, 69, 12, 0, 1]] where
  M :=![![![17143, -7143, 31145, -14018, -35546], ![-7510, 3125, -13651, 6115, 15526], ![3296, -1395, 5944, -2852, -7112], ![-1408, 444, -2839, 132, 1120], ![1350, -525, 2526, -837, -2329]]]
  hmulB := by decide  
  f := ![![![-65, 48, 611, -275, -686]], ![![-136, -340, -91, 52, 112]], ![![8, -84, -296, 121, 280]], ![![-88, -271, -198, 85, 182]], ![![-60, -129, 27, -9, -31]]]
  g := ![![![7751, 21953, 15385, -14018, -35546], ![-3384, -9584, -6713, 6115, 15526], ![1560, 4421, 3120, -2852, -7112], ![-184, -504, -211, 132, 1120], ![492, 1389, 936, -837, -2329]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [37, 41, 103, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [100, 2, 143], [159, 178, 38], [0, 1]]
 g := ![![[56, 134, 9], [], [93, 102, 33], [97, 138], [33, 107, 94], [70, 78, 1], []], ![[85, 129, 141, 5], [125, 12], [43, 120, 57, 11], [15, 12], [151, 58, 84, 133], [35, 130, 172, 20], [79, 177]], ![[0, 44, 6, 176], [172, 12], [8, 164, 10, 121], [19, 133], [94, 10, 23, 167], [126, 148, 51, 152], [3, 177]]]
 h' := ![![[100, 2, 143], [4, 155, 178], [179, 97], [156, 142, 157], [46, 177, 89], [125, 36, 53], [0, 0, 1], [0, 1]], ![[159, 178, 38], [65, 57, 92], [105, 13, 115], [168, 70, 106], [162, 137, 66], [154, 77, 102], [18, 24, 178], [100, 2, 143]], ![[0, 1], [0, 150, 92], [36, 71, 66], [26, 150, 99], [27, 48, 26], [97, 68, 26], [11, 157, 2], [159, 178, 38]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [81, 17], []]
 b := ![[], [180, 13, 110], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [37, 41, 103, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-63432907, 96938910, 177318087, 873381033, 1833498801]
  a := ![-4, 8, 13, 41, 97]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-426828085, -1224381276, -921579663, 873381033, 1833498801]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 5929741 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-173, -496, -408, 196, 460]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![-173, -496, -408, 196, 460]] 
 ![![181, 0, 0, 0, 0], ![26, 1, 0, 0, 0], ![48, 0, 1, 0, 0], ![19, 0, 0, 1, 0], ![179, 0, 0, 0, 1]] where
  M :=![![![-173, -496, -408, 196, 460], ![68, 23, -368, 164, 412], ![84, 232, 103, -52, -116], ![-12, 32, 192, -85, -212], ![-12, -56, -96, 44, 107]]]
  hmulB := by decide  
  f := ![![![-2249, -816, 1176, 7356, 28660]], ![![-246, -89, 128, 804, 3132]], ![![-1076, -392, 567, 3524, 13732]], ![![2749, 1008, -1464, -9017, -35152]], ![![-3843, -1400, 2024, 12584, 49039]]]
  g := ![![![-297, -496, -408, 196, 460], ![-330, 23, -368, 164, 412], ![60, 232, 103, -52, -116], ![163, 32, 192, -85, -212], ![-77, -56, -96, 44, 107]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1

def I181N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-61289, 25534, -111350, 50102, 127056]] i)))

def SI181N2: IdealEqSpanCertificate' Table ![![-61289, 25534, -111350, 50102, 127056]] 
 ![![181, 0, 0, 0, 0], ![170, 1, 0, 0, 0], ![60, 0, 1, 0, 0], ![117, 0, 0, 1, 0], ![18, 0, 0, 0, 1]] where
  M :=![![![-61289, 25534, -111350, 50102, 127056], ![26852, -11187, 48784, -21952, -55668], ![-11764, 4900, -21375, 9608, 24372], ![5156, -2156, 9352, -4271, -10788], ![-4858, 2026, -8822, 3986, 10097]]]
  hmulB := by decide  
  f := ![![![555, 734, -430, -626, -2568]], ![![514, 689, -396, -564, -2316]], ![![232, 260, -167, -368, -1476]], ![![55, 362, -118, 591, 2220]], ![![220, 134, -130, -602, -2359]]]
  g := ![![![-32431, 25534, -111350, 50102, 127056], ![14210, -11187, 48784, -21952, -55668], ![-6216, 4900, -21375, 9608, 24372], ![2787, -2156, 9352, -4271, -10788], ![-2586, 2026, -8822, 3986, 10097]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N2 : Nat.card (O ⧸ I181N2) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N2)

lemma isPrimeI181N2 : Ideal.IsPrime I181N2 := prime_ideal_of_norm_prime hp181.out _ NI181N2
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![17143, -7143, 31145, -14018, -35546]] ![![-173, -496, -408, 196, 460]]
  ![![-240515, 100423, -436825, 196542, 498438]] where
 M := ![![![-240515, 100423, -436825, 196542, 498438]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI181N1 : IdealMulLeCertificate' Table 
  ![![-240515, 100423, -436825, 196542, 498438]] ![![-61289, 25534, -111350, 50102, 127056]]
  ![![181, 0, 0, 0, 0]] where
 M := ![![![21168250279, -8819093775, 38458356005, -17304439840, -43883086914]]]
 hmul := by decide  
 g := ![![![![116951659, -48724275, 212477105, -95604640, -242447994]]]]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79761, -33222, 144925, -65145, -165248]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![79761, -33222, 144925, -65145, -165248]] 
 ![![191, 0, 0, 0, 0], ![0, 191, 0, 0, 0], ![42, 21, 1, 0, 0], ![73, 174, 0, 1, 0], ![89, 2, 0, 0, 1]] where
  M :=![![![79761, -33222, 144925, -65145, -165248], ![-34958, 14616, -63409, 28948, 73126], ![15230, -6010, 28334, -10049, -27326], ![-7228, 5181, -8831, 21457, 42484], ![6458, -3259, 10606, -9353, -20593]]]
  hmulB := by decide  
  f := ![![![967, 1813, -911, 140, 176]], ![![-104, 1107, 2057, 413, 2888]], ![![212, 522, 23, 33, 190]], ![![195, 1669, 1564, 690, 3710]], ![![493, 874, -425, -71, -435]]]
  g := ![![![70448, 44969, 144925, -65145, -165248], ![-31378, -20089, -63409, 28948, 73126], ![10423, 6294, 28334, -10049, -27326], ![-26093, -18994, -8831, 21457, 42484], ![10872, 7553, 10606, -9353, -20593]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [140, 160, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 190], [0, 1]]
 g := ![![[83, 136], [126, 158], [84, 59], [173, 54], [81, 128], [101, 6], [1]], ![[97, 55], [58, 33], [3, 132], [128, 137], [38, 63], [96, 185], [1]]]
 h' := ![![[31, 190], [123, 161], [82, 106], [37, 170], [120, 98], [185, 117], [51, 31], [0, 1]], ![[0, 1], [148, 30], [121, 85], [150, 21], [102, 93], [183, 74], [57, 160], [31, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40]]
 b := ![[], [72, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [140, 160, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1890, 5506, 8792, 42419, 81431]
  a := ![2, -3, -4, -20, -43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-56100, -40434, 8792, 42419, 81431]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-55, -118, 14, 4, 12]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![-55, -118, 14, 4, 12]] 
 ![![191, 0, 0, 0, 0], ![23, 1, 0, 0, 0], ![44, 0, 1, 0, 0], ![134, 0, 0, 1, 0], ![46, 0, 0, 0, 1]] where
  M :=![![![-55, -118, 14, 4, 12], ![4, -51, -118, 10, -36], ![-56, 14, 15, 268, 1032], ![496, 212, -214, -1621, -6288], ![-272, -118, 128, 874, 3397]]]
  hmulB := by decide  
  f := ![![![-4727169, 1969430, -8588290, 3864328, 9799716]], ![![-558397, 232639, -1014492, 456474, 1157592]], ![![-1093732, 455670, -1987085, 894096, 2267376]], ![![-3314362, 1380828, -6021510, 2709403, 6870888]], ![![-1140442, 475130, -2071948, 932278, 2364205]]]
  g := ![![![5, -118, 14, 4, 12], ![35, -51, -118, 10, -36], ![-442, 14, 15, 268, 1032], ![2678, 212, -214, -1621, -6288], ![-1448, -118, 128, 874, 3397]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1

def I191N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5625, 1860, -8769, 6119, 18276]] i)))

def SI191N2: IdealEqSpanCertificate' Table ![![-5625, 1860, -8769, 6119, 18276]] 
 ![![191, 0, 0, 0, 0], ![69, 1, 0, 0, 0], ![14, 0, 1, 0, 0], ![180, 0, 0, 1, 0], ![179, 0, 0, 0, 1]] where
  M :=![![![-5625, 1860, -8769, 6119, 18276], ![6038, 494, 1941, -14402, -53694], ![-24890, -8364, 10982, 79271, 307914], ![149372, 54381, -78465, -488895, -1905156], ![-81174, -29421, 42246, 265269, 1033529]]]
  hmulB := by decide  
  f := ![![![84825, 190281, -12873, 694, 13500]], ![![30707, 69188, -3714, -179, 3828]], ![![6028, 13581, -736, -24, 774]], ![![79874, 179058, -12507, 882, 13242]], ![![79557, 178500, -11955, 583, 12503]]]
  g := ![![![-22953, 1860, -8769, 6119, 18276], ![63604, 494, 1941, -14402, -53694], ![-361188, -8364, 10982, 79271, 307914], ![2233087, 54381, -78465, -488895, -1905156], ![-1211480, -29421, 42246, 265269, 1033529]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N2 : Nat.card (O ⧸ I191N2) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N2)

lemma isPrimeI191N2 : Ideal.IsPrime I191N2 := prime_ideal_of_norm_prime hp191.out _ NI191N2

def I191N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7633, 15353, -6640, 2559, 7358]] i)))

def SI191N3: IdealEqSpanCertificate' Table ![![7633, 15353, -6640, 2559, 7358]] 
 ![![191, 0, 0, 0, 0], ![78, 1, 0, 0, 0], ![28, 0, 1, 0, 0], ![108, 0, 0, 1, 0], ![152, 0, 0, 0, 1]] where
  M :=![![![7633, 15353, -6640, 2559, 7358], ![2240, 10192, 15672, -7285, -17608], ![-3038, -5045, 5945, -2525, -6634], ![-1584, -5563, -5986, 2824, 6728], ![1194, 3130, 1218, -628, -1379]]]
  hmulB := by decide  
  f := ![![![-19961, 5323, -27286, 25731, 82330]], ![![-7990, 2204, -11142, 10069, 31952]], ![![-3718, 503, -3617, 6329, 22018]], ![![-6452, 4775, -17984, -1292, -15184]], ![![-18510, 3280, -20334, 29070, 99005]]]
  g := ![![![-12559, 15353, -6640, 2559, 7358], ![11684, 10192, 15672, -7285, -17608], ![7880, -5045, 5945, -2525, -6634], ![-3810, -5563, -5986, 2824, 6728], ![2, 3130, 1218, -628, -1379]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N3 : Nat.card (O ⧸ I191N3) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N3)

lemma isPrimeI191N3 : Ideal.IsPrime I191N3 := prime_ideal_of_norm_prime hp191.out _ NI191N3
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![79761, -33222, 144925, -65145, -165248]] ![![-55, -118, 14, 4, 12]]
  ![![-7, -2, 11, 17, 28]] where
 M := ![![![-7, -2, 11, 17, 28]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI191N1 : IdealMulLeCertificate' Table 
  ![![-7, -2, 11, 17, 28]] ![![-5625, 1860, -8769, 6119, 18276]]
  ![![19961, -5323, 27286, -25731, -82330]] where
 M := ![![![19961, -5323, 27286, -25731, -82330]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI191N2 : IdealMulLeCertificate' Table 
  ![![19961, -5323, 27286, -25731, -82330]] ![![7633, 15353, -6640, 2559, 7358]]
  ![![191, 0, 0, 0, 0]] where
 M := ![![![-191, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC191 : ContainsPrimesAboveP 191 ![I191N0, I191N1, I191N2, I191N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI191N0
    exact isPrimeI191N1
    exact isPrimeI191N2
    exact isPrimeI191N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 191 (by decide) (𝕀 ⊙ MulI191N0 ⊙ MulI191N1 ⊙ MulI191N2)
instance hp193 : Fact (Nat.Prime 193) := {out := by norm_num}

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![21281, -8672, 38081, -18007, -46772]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![21281, -8672, 38081, -18007, -46772]] 
 ![![193, 0, 0, 0, 0], ![0, 193, 0, 0, 0], ![120, 172, 1, 0, 0], ![11, 65, 0, 1, 0], ![8, 178, 0, 0, 1]] where
  M :=![![![21281, -8672, 38081, -18007, -46772], ![-10758, 3274, -15921, 12594, 38830], ![13642, 1836, 2226, -34803, -131162], ![-61556, -21161, 28589, 197547, 768028], ![34090, 11181, -14218, -107709, -417973]]]
  hmulB := by decide  
  f := ![![![-30447, -111959, -130673, 61466, 146956]], ![![24024, 31019, -74517, 32513, 83320]], ![![2574, -41675, -147422, 67080, 165362]], ![![6317, 4048, -32325, 14357, 36194]], ![![20892, 23919, -74272, 32593, 83081]]]
  g := ![![![-20602, 15219, 38081, -18007, -46772], ![7516, -25848, -15921, 12594, 38830], ![6107, 130715, 2226, -34803, -131162], ![-61189, -800456, 28589, 197547, 768028], ![32481, 434492, -14218, -107709, -417973]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [105, 40, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [153, 192], [0, 1]]
 g := ![![[175, 55], [75], [189], [128], [184], [85], [153, 1]], ![[98, 138], [75], [189], [128], [184], [85], [113, 192]]]
 h' := ![![[153, 192], [6, 21], [57, 123], [71, 31], [1, 163], [139, 143], [147, 144], [0, 1]], ![[0, 1], [131, 172], [155, 70], [182, 162], [43, 30], [16, 50], [177, 49], [153, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [70]]
 b := ![[], [121, 35]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [105, 40, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-15056, -737, 14087, 76097, 234618]
  a := ![-3, 3, 13, 23, 66]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-22899, -254570, 14087, 76097, 234618]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-45, -26, 234, -104, -262]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![-45, -26, 234, -104, -262]] 
 ![![193, 0, 0, 0, 0], ![0, 193, 0, 0, 0], ![82, 147, 1, 0, 0], ![105, 89, 0, 1, 0], ![3, 127, 0, 0, 1]] where
  M :=![![![-45, -26, 234, -104, -262], ![-54, -149, -76, 38, 86], ![10, -16, -121, 54, 134], ![26, 64, 12, -7, -10], ![-12, -22, 18, -8, -23]]]
  hmulB := by decide  
  f := ![![![-189, 78, -342, 152, 386]], ![![82, -37, 148, -74, -178]], ![![-18, 5, -33, 8, 28]], ![![-65, 25, -118, 47, 126]], ![![51, -23, 92, -46, -111]]]
  g := ![![![-39, 42, 234, -104, -262], ![10, -17, -76, 38, 86], ![20, -21, -121, 54, 134], ![-1, 1, 12, -7, -10], ![-3, 5, 18, -8, -23]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P1 : CertificateIrreducibleZModOfList' 193 2 2 7 [177, 144, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [49, 192], [0, 1]]
 g := ![![[184, 12], [118], [85], [65], [42], [165], [49, 1]], ![[0, 181], [118], [85], [65], [42], [165], [98, 192]]]
 h' := ![![[49, 192], [21, 165], [16, 120], [59, 144], [62, 114], [82, 87], [12, 101], [0, 1]], ![[0, 1], [0, 28], [106, 73], [167, 49], [51, 79], [99, 106], [136, 92], [49, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [158]]
 b := ![[], [91, 79]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N1 : CertifiedPrimeIdeal' SI193N1 193 where
  n := 2
  hpos := by decide
  P := [177, 144, 1]
  hirr := P193P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-52857, 32590, 90104, 461611, 1120499]
  a := ![-8, 5, 12, 68, 169]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-307109, -1018650, 90104, 461611, 1120499]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N1 B_one_repr
lemma NI193N1 : Nat.card (O ⧸ I193N1) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N1

def I193N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 609, 815, -382, -918]] i)))

def SI193N2: IdealEqSpanCertificate' Table ![![151, 609, 815, -382, -918]] 
 ![![193, 0, 0, 0, 0], ![67, 1, 0, 0, 0], ![143, 0, 1, 0, 0], ![69, 0, 0, 1, 0], ![181, 0, 0, 0, 1]] where
  M :=![![![151, 609, 815, -382, -918], ![-154, -231, 381, -171, -438], ![-96, -325, -306, 102, 264], ![60, 6, -283, -156, -204], ![-4, 53, 160, 1, -43]]]
  hmulB := by decide  
  f := ![![![-15465, 6062, -26955, 13839, 37266]], ![![-5319, 2096, -9304, 4725, 12666]], ![![-11571, 4462, -19947, 10586, 28890]], ![![-4915, 2387, -9948, 2950, 5544]], ![![-14839, 5567, -25115, 14064, 39173]]]
  g := ![![![183, 609, 815, -382, -918], ![269, -231, 381, -171, -438], ![55, -325, -306, 102, 264], ![455, 6, -283, -156, -204], ![-97, 53, 160, 1, -43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N2 : Nat.card (O ⧸ I193N2) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N2)

lemma isPrimeI193N2 : Ideal.IsPrime I193N2 := prime_ideal_of_norm_prime hp193.out _ NI193N2
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![21281, -8672, 38081, -18007, -46772]] ![![-45, -26, 234, -104, -262]]
  ![![-15465, 6062, -26955, 13839, 37266]] where
 M := ![![![-15465, 6062, -26955, 13839, 37266]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI193N1 : IdealMulLeCertificate' Table 
  ![![-15465, 6062, -26955, 13839, 37266]] ![![151, 609, 815, -382, -918]]
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

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-21, -11, -7, 80, 300]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![-21, -11, -7, 80, 300]] 
 ![![197, 0, 0, 0, 0], ![0, 197, 0, 0, 0], ![0, 0, 197, 0, 0], ![110, 155, 107, 1, 0], ![163, 0, 110, 0, 1]] where
  M :=![![![-21, -11, -7, 80, 300], ![140, 59, -71, -447, -1740], ![-846, -307, 458, 2770, 10806], ![5266, 1924, -2803, -17288, -67362], ![-2856, -1045, 1518, 9373, 36527]]]
  hmulB := by decide  
  f := ![![![-281, 134, -537, 241, 612]], ![![130, -40, 245, -112, -282]], ![![-58, 18, -94, 33, 90]], ![![-86, 53, -158, 64, 168]], ![![-265, 121, -497, 218, 557]]]
  g := ![![![-293, -63, -211, 80, 300], ![1690, 352, 1214, -447, -1740], ![-10492, -2181, -7536, 2770, 10806], ![65416, 13612, 46989, -17288, -67362], ![-35471, -7380, -25479, 9373, 36527]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 3 2 7 [62, 133, 174, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [44, 4, 185], [176, 192, 12], [0, 1]]
 g := ![![[12, 175, 173], [133, 158], [31, 53, 101], [2, 143], [118, 134], [139, 135], [1]], ![[31, 171, 133, 95], [32, 174], [152, 150, 69, 94], [36, 70], [100, 62], [90, 160], [18, 151, 5, 45]], ![[130, 54, 85, 52], [141, 182], [193, 152, 104, 87], [75, 9], [4, 146], [179, 62], [26, 173, 154, 152]]]
 h' := ![![[44, 4, 185], [165, 55, 166], [48, 16, 143], [50, 23, 62], [119, 132, 145], [151, 76, 79], [135, 64, 23], [0, 1]], ![[176, 192, 12], [173, 18, 86], [160, 68, 78], [173, 102, 5], [89, 43, 55], [173, 196, 72], [146, 50, 102], [44, 4, 185]], ![[0, 1], [164, 124, 142], [89, 113, 173], [17, 72, 130], [147, 22, 194], [196, 122, 46], [159, 83, 72], [176, 192, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [140, 8], []]
 b := ![[], [49, 95, 132], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 3
  hpos := by decide
  P := [62, 133, 174, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-41816068, 60030730, 112262619, 554301543, 1175717798]
  a := ![-4, 4, 7, 37, 88]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1282522776, -435820855, -956989646, 554301543, 1175717798]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 7645373 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-281, 134, -537, 241, 612]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![-281, 134, -537, 241, 612]] 
 ![![197, 0, 0, 0, 0], ![0, 197, 0, 0, 0], ![25, 90, 1, 0, 0], ![114, 2, 0, 1, 0], ![115, 146, 0, 0, 1]] where
  M :=![![![-281, 134, -537, 241, 612], ![130, -40, 245, -112, -282], ![-58, 18, -94, 33, 90], ![24, -25, 27, -73, -144], ![-22, 15, -38, 33, 73]]]
  hmulB := by decide  
  f := ![![![-21, -11, -7, 80, 300]], ![![140, 59, -71, -447, -1740]], ![![57, 24, -31, -180, -702]], ![![16, 4, -19, -46, -186]], ![![77, 32, -49, -237, -929]]]
  g := ![![![-430, -210, -537, 241, 612], ![199, 98, 245, -112, -282], ![-60, -24, -94, 33, 90], ![123, 95, 27, -73, -144], ![-57, -37, -38, 33, 73]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P1 : CertificateIrreducibleZModOfList' 197 2 2 7 [85, 31, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [166, 196], [0, 1]]
 g := ![![[5, 51], [175], [27, 40], [112], [154], [61], [166, 1]], ![[0, 146], [175], [166, 157], [112], [154], [61], [135, 196]]]
 h' := ![![[166, 196], [130, 144], [69, 136], [32, 146], [80, 30], [94, 101], [74, 88], [0, 1]], ![[0, 1], [0, 53], [187, 61], [37, 51], [135, 167], [115, 96], [104, 109], [166, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [150, 105]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N1 : CertifiedPrimeIdeal' SI197N1 197 where
  n := 2
  hpos := by decide
  P := [85, 31, 1]
  hirr := P197P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-78007, 67642, 155624, 788798, 1817522]
  a := ![-11, 10, -4, 98, 238]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1537597, -1425758, 155624, 788798, 1817522]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N1 B_one_repr
lemma NI197N1 : Nat.card (O ⧸ I197N1) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![-21, -11, -7, 80, 300]] ![![-281, 134, -537, 241, 612]]
  ![![197, 0, 0, 0, 0]] where
 M := ![![![197, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC197 : ContainsPrimesAboveP 197 ![I197N0, I197N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
    exact isPrimeI197N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 197 (by decide) (𝕀 ⊙ MulI197N0)


lemma PB953I4_primes (p : ℕ) :
  p ∈ Set.range ![157, 163, 167, 173, 179, 181, 191, 193, 197] ↔ Nat.Prime p ∧ 151 < p ∧ p ≤ 197 := by
  rw [← List.mem_ofFn']
  convert primes_range 151 197 (by omega)

def PB953I4 : PrimesBelowBoundCertificateInterval O 151 197 953 where
  m := 9
  g := ![3, 3, 2, 2, 2, 3, 4, 3, 2]
  P := ![157, 163, 167, 173, 179, 181, 191, 193, 197]
  hP := PB953I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I157N0, I157N1, I157N2]
    · exact ![I163N0, I163N1, I163N2]
    · exact ![I167N0, I167N1]
    · exact ![I173N0, I173N1]
    · exact ![I179N0, I179N1]
    · exact ![I181N0, I181N1, I181N2]
    · exact ![I191N0, I191N1, I191N2, I191N3]
    · exact ![I193N0, I193N1, I193N2]
    · exact ![I197N0, I197N1]
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
    · exact ![3869893, 157, 157]
    · exact ![4330747, 163, 163]
    · exact ![4657463, 27889]
    · exact ![895745041, 173]
    · exact ![1026625681, 179]
    · exact ![5929741, 181, 181]
    · exact ![36481, 191, 191, 191]
    · exact ![37249, 37249, 193]
    · exact ![7645373, 38809]
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
      exact NI163N2
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
      exact NI173N1
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
      exact NI191N2
      exact NI191N3
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
      exact NI193N2
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
      exact NI197N1
  β := ![I157N1, I157N2, I163N1, I163N2, I173N1, I179N1, I181N1, I181N2, I191N1, I191N2, I191N3, I193N2]
  Il := ![[I157N1, I157N2], [I163N1, I163N2], [], [I173N1], [I179N1], [I181N1, I181N2], [I191N1, I191N2, I191N3], [I193N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
