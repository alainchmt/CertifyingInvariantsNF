
import IdealArithmetic.Examples.NF5_3_1125000000_3.RI5_3_1125000000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-279, -276, 326, -36, -374]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![-279, -276, 326, -36, -374]] 
 ![![157, 0, 0, 0, 0], ![0, 157, 0, 0, 0], ![0, 0, 157, 0, 0], ![22, 93, 115, 1, 0], ![15, 43, 25, 0, 1]] where
  M :=![![![-279, -276, 326, -36, -374], ![1064, 833, -880, 848, 460], ![-968, 516, -1639, -5184, 5864], ![-1874, -2212, 2952, 1071, -4438], ![1232, 2124, -3202, -3008, 6179]]]
  hmulB := by decide  
  f := ![![![93, -188, -26, -148, -62]], ![![-872, -691, 280, -1104, -1060]], ![![-4856, -4948, 1605, -7328, -6712]], ![![-4076, -4075, 1343, -6065, -5574]], ![![-1025, -1017, 337, -1516, -1395]]]
  g := ![![![39, 122, 88, -36, -374], ![-156, -623, -700, 848, 460], ![160, 1468, 2853, -5184, 5864], ![262, 567, -59, 1071, -4438], ![-161, 103, 1199, -3008, 6179]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [81, 19, 77, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 98, 50], [56, 58, 107], [0, 1]]
 g := ![![[116, 17, 35], [152, 90], [59, 52, 14], [7, 53, 56], [62, 12, 153], [80, 1], []], ![[104, 61, 111, 23], [93, 93], [70, 2, 36, 135], [131, 28, 128, 74], [105, 33, 14, 38], [6, 67], [48, 145]], ![[13, 15], [125, 12], [140, 3, 73, 134], [110, 111, 144, 84], [100, 148, 46, 28], [54, 27], [148, 145]]]
 h' := ![![[24, 98, 50], [142, 14, 52], [88, 115, 54], [61, 131, 93], [2, 13, 29], [114, 126, 101], [0, 0, 1], [0, 1]], ![[56, 58, 107], [12, 98, 105], [154, 56, 90], [83, 119, 12], [36, 14, 134], [53, 61, 69], [142, 54, 58], [24, 98, 50]], ![[0, 1], [4, 45], [148, 143, 13], [90, 64, 52], [89, 130, 151], [11, 127, 144], [97, 103, 98], [56, 58, 107]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [79, 50], []]
 b := ![[], [139, 5, 156], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [81, 19, 77, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6283675820, -6309484948, 2360377442, -8858003114, -8900371164]
  a := ![-176, -194, 145, -109, -324]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2051579364, 7644590858, 7920637036, -8858003114, -8900371164]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 3869893 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-93, 188, 26, 148, 62]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![-93, 188, 26, 148, 62]] 
 ![![157, 0, 0, 0, 0], ![0, 157, 0, 0, 0], ![110, 33, 1, 0, 0], ![12, 102, 0, 1, 0], ![63, 4, 0, 0, 1]] where
  M :=![![![-93, 188, 26, 148, 62], ![872, 691, -280, 1104, 1060], ![4856, 4948, -1605, 7328, 6712], ![2442, 2356, -808, 3557, 3294], ![3424, 3436, -1134, 5120, 4705]]]
  hmulB := by decide  
  f := ![![![279, 276, -326, 36, 374]], ![![-1064, -833, 880, -848, -460]], ![![-22, 15, -33, -120, 128]], ![![-658, -506, 528, -555, -242]], ![![77, 76, -88, 12, 99]]]
  g := ![![![-55, -102, 26, 148, 62], ![-308, -681, -280, 1104, 1060], ![-2098, -4563, -1605, 7328, 6712], ![-1012, -2210, -808, 3557, 3294], ![-1463, -3186, -1134, 5120, 4705]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P1 : CertificateIrreducibleZModOfList' 157 2 2 7 [31, 28, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [129, 156], [0, 1]]
 g := ![![[87, 76], [93], [65, 42], [61, 9], [65, 113], [156], [1]], ![[0, 81], [93], [145, 115], [123, 148], [41, 44], [156], [1]]]
 h' := ![![[129, 156], [148, 95], [26, 67], [150, 102], [26, 3], [50, 37], [126, 129], [0, 1]], ![[0, 1], [0, 62], [34, 90], [120, 55], [99, 154], [113, 120], [125, 28], [129, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [98]]
 b := ![[], [58, 49]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N1 : CertifiedPrimeIdeal' SI157N1 157 where
  n := 2
  hpos := by decide
  P := [31, 28, 1]
  hirr := P157P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![153603002, 148431006, -22899712, 274391926, 186928429]
  a := ![-2547, -2778, 1994, -1752, -4457]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-78959381, -177271138, -22899712, 274391926, 186928429]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N1 B_one_repr
lemma NI157N1 : Nat.card (O ⧸ I157N1) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![-279, -276, 326, -36, -374]] ![![-93, 188, 26, 148, 62]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0, 0, 0]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0, 0, 0]] 
 ![![163, 0, 0, 0, 0], ![0, 163, 0, 0, 0], ![0, 0, 163, 0, 0], ![0, 0, 0, 163, 0], ![0, 0, 0, 0, 163]] where
  M :=![![![163, 0, 0, 0, 0], ![0, 163, 0, 0, 0], ![0, 0, 163, 0, 0], ![0, 0, 0, 163, 0], ![0, 0, 0, 0, 163]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 5 2 7 [43, 70, 96, 27, 4, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [127, 39, 20, 88, 11], [21, 22, 67, 44, 84], [160, 64, 55, 37, 11], [14, 37, 21, 157, 57], [0, 1]]
 g := ![![[16, 25, 64, 25, 96], [118, 134, 157, 30, 34], [146, 85, 73, 60], [79, 69, 27, 81], [69, 131, 152, 16], [1], []], ![[64, 109, 7, 19, 128, 82, 14, 48], [98, 75, 110, 133, 141, 22, 154, 31], [83, 54, 90, 132], [17, 42, 39, 143], [30, 136], [133, 47, 57, 56, 11, 138, 20, 138], [154, 87, 148, 121]], ![[107, 72, 64, 148, 76, 147, 17, 144], [137, 57, 122, 1, 121, 57, 126, 150], [154, 145, 131, 81], [67, 76, 95, 43], [162, 46, 20, 77], [74, 40, 162, 132, 155, 84, 151, 57], [68, 59, 32, 47]], ![[85, 44, 156, 116, 84, 73, 115, 19], [61, 119, 40, 162, 75, 30, 104, 105], [46, 153, 115, 64], [33, 145, 46, 55], [55, 83, 58, 9], [119, 12, 21, 101, 132, 66, 160, 92], [156, 111, 4, 121]], ![[91, 153, 74, 86, 152, 53, 81, 83], [80, 2, 132, 145, 31, 40, 154, 96], [93, 132, 149, 118], [104, 158, 40, 60], [131, 63, 4, 15], [77, 99, 121, 101, 151, 127, 95, 25], [13, 71, 12, 152]]]
 h' := ![![[127, 39, 20, 88, 11], [142, 11, 65, 87, 52], [34, 50, 0, 124, 94], [66, 3, 91, 85, 68], [23, 121, 117, 101, 9], [120, 93, 67, 136, 159], [0, 0, 1], [0, 1]], ![[21, 22, 67, 44, 84], [3, 27, 151, 86, 69], [98, 107, 72, 34, 92], [9, 14, 82, 110, 28], [67, 3, 108, 69, 119], [85, 88, 145, 138], [53, 112, 64, 77, 63], [127, 39, 20, 88, 11]], ![[160, 64, 55, 37, 11], [24, 63, 81, 71, 5], [70, 79, 25, 160, 95], [3, 78, 64, 143, 9], [90, 70, 91, 74, 80], [84, 37, 150, 6, 136], [125, 147, 66, 44, 96], [21, 22, 67, 44, 84]], ![[14, 37, 21, 157, 57], [9, 98, 27, 146, 77], [36, 122, 137, 15, 39], [104, 14, 68, 150, 155], [43, 109, 122, 32, 50], [146, 95, 126, 93, 160], [147, 60, 82, 159, 110], [160, 64, 55, 37, 11]], ![[0, 1], [19, 127, 2, 99, 123], [49, 131, 92, 156, 6], [25, 54, 21, 1, 66], [52, 23, 51, 50, 68], [44, 13, 1, 116, 34], [126, 7, 113, 46, 57], [14, 37, 21, 157, 57]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [118, 12, 61, 70], [], [], []]
 b := ![[], [73, 22, 126, 94, 127], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 5
  hpos := by decide
  P := [43, 70, 96, 27, 4, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-112511921975018607, -111910149571450036, 37343729808002982, -166894132176789774, -153888496432093484]
  a := ![-139, -151, 107, -99, -239]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-690257190030789, -686565334794172, 229102636858914, -1023890381452698, -944101205104868]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 115063617043 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def PBC163 : ContainsPrimesAboveP 163 ![I163N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![163, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 163 (by decide) 𝕀

instance hp167 : Fact (Nat.Prime 167) := {out := by norm_num}

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0, 0, 0]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0, 0, 0]] 
 ![![167, 0, 0, 0, 0], ![0, 167, 0, 0, 0], ![0, 0, 167, 0, 0], ![0, 0, 0, 167, 0], ![0, 0, 0, 0, 167]] where
  M :=![![![167, 0, 0, 0, 0], ![0, 167, 0, 0, 0], ![0, 0, 167, 0, 0], ![0, 0, 0, 167, 0], ![0, 0, 0, 0, 167]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 5 2 7 [13, 7, 41, 73, 79, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [114, 100, 40, 77, 61], [23, 33, 157, 49, 43], [150, 98, 160, 65, 82], [135, 102, 144, 143, 148], [0, 1]]
 g := ![![[94, 6, 15, 1, 57], [90, 143, 13, 25, 61], [105, 63, 80, 106, 121], [42, 28, 105, 162], [140, 69, 123, 62], [1], []], ![[101, 33, 147, 14, 109, 90, 92, 85], [123, 125, 47, 151, 68, 62, 78, 28], [112, 160, 25, 78, 4, 153, 82, 93], [59, 76, 148, 128], [28, 138, 120, 14], [150, 143, 2, 37, 39, 122, 70, 31], [2, 127, 3, 47]], ![[52, 83, 43, 65, 115, 79, 158, 60], [93, 150, 59, 13, 100, 136, 147, 159], [155, 53, 47, 98, 98, 18, 74, 90], [24, 31, 64, 132], [144, 77, 58, 50], [3, 126, 72, 95, 53, 85, 88, 20], [79, 165, 93, 12]], ![[110, 79, 70, 139, 51, 165, 9, 41], [56, 128, 152, 21, 94, 118, 82, 53], [22, 29, 163, 121, 120, 20, 41, 30], [136, 114, 161, 76], [94, 64, 77, 116], [139, 129, 50, 69, 85, 2, 101, 39], [109, 129, 3, 44]], ![[93, 124, 132, 124, 105, 107, 1, 34], [145, 41, 112, 139, 137, 151, 79, 34], [147, 134, 55, 8, 69, 101, 119, 109], [74, 57, 146, 63], [115, 18, 36, 31], [87, 23, 39, 106, 149, 64, 106, 161], [110, 80, 115, 27]]]
 h' := ![![[114, 100, 40, 77, 61], [166, 22, 14, 6, 97], [138, 106, 165, 34, 140], [149, 62, 157, 130, 156], [19, 142, 140, 114, 50], [154, 160, 126, 94, 88], [0, 0, 1], [0, 1]], ![[23, 33, 157, 49, 43], [0, 54, 81, 134, 151], [161, 54, 50, 112, 61], [166, 77, 60, 48, 95], [91, 54, 1, 14, 104], [11, 17, 78, 140, 101], [111, 93, 74, 32, 152], [114, 100, 40, 77, 61]], ![[150, 98, 160, 65, 82], [125, 143, 131, 107, 81], [15, 144, 87, 24, 148], [9, 1, 114, 108, 89], [133, 80, 65, 107, 74], [1, 126, 35, 0, 102], [3, 156, 36, 112, 163], [23, 33, 157, 49, 43]], ![[135, 102, 144, 143, 148], [4, 43, 52, 45, 77], [137, 106, 139, 126, 57], [107, 131, 69, 6, 100], [47, 125, 136, 120, 57], [10, 39, 79, 166, 139], [41, 73, 89, 114, 59], [150, 98, 160, 65, 82]], ![[0, 1], [142, 72, 56, 42, 95], [103, 91, 60, 38, 95], [96, 63, 101, 42, 61], [35, 100, 159, 146, 49], [148, 159, 16, 101, 71], [95, 12, 134, 76, 127], [135, 102, 144, 143, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56, 114, 41], [], [], []]
 b := ![[], [124, 163, 164, 128], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 5
  hpos := by decide
  P := [13, 7, 41, 73, 79, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2397207218061343382743, 2385208444955003319301, -797778215129549893462, 3552153961115499800691, 3282866636391377315619]
  a := ![1030, 1133, -838, 655, 1873]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![14354534239888283729, 14282685299131756403, -4777115060655987386, 21270383000691615573, 19657884050247768357]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 129891985607 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def PBC167 : ContainsPrimesAboveP 167 ![I167N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![167, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 167 (by decide) 𝕀

instance hp173 : Fact (Nat.Prime 173) := {out := by norm_num}

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, -25, 61, 156, -192]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![19, -25, 61, 156, -192]] 
 ![![173, 0, 0, 0, 0], ![0, 173, 0, 0, 0], ![0, 0, 173, 0, 0], ![45, 2, 131, 1, 0], ![68, 127, 89, 0, 1]] where
  M :=![![![19, -25, 61, 156, -192], ![606, 756, -1033, -492, 1632], ![-4902, -4895, 5988, -324, -7200], ![1424, 1076, -1100, 1261, 400], ![-3214, -2911, 3359, -1244, -3259]]]
  hmulB := by decide  
  f := ![![![-2065, -4489, -2533, 1452, 3648]], ![![-2094, -5274, -3001, 1692, 4320]], ![![-2598, -6011, -3402, 1932, 4896]], ![![-2519, -5758, -3257, 1853, 4688]], ![![-3682, -8720, -4944, 2804, 7117]]]
  g := ![![![35, 139, -19, 156, -192], ![-510, -1188, -473, -492, 1632], ![2886, 5261, 3984, -324, -7200], ![-477, -302, -1167, 1261, 400], ![1586, 2390, 2638, -1244, -3259]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [6, 56, 134, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [135, 102, 20], [77, 70, 153], [0, 1]]
 g := ![![[64, 76, 157], [101, 40], [129, 110, 55], [7, 147, 21], [45, 90], [81, 39, 1], []], ![[72, 153, 165, 168], [149, 138], [90, 104, 27, 58], [47, 94, 94, 18], [94, 163], [161, 23, 126, 82], [131, 54]], ![[106, 40, 2, 59], [17, 126], [51, 135, 76, 58], [68, 146, 133, 59], [47, 124], [137, 144, 129, 39], [171, 54]]]
 h' := ![![[135, 102, 20], [63, 93, 147], [91, 108, 127], [131, 150, 48], [127, 94, 59], [33, 74, 104], [0, 0, 1], [0, 1]], ![[77, 70, 153], [8, 15, 40], [146, 115, 151], [65, 48, 132], [85, 53, 128], [86, 106, 110], [139, 158, 70], [135, 102, 20]], ![[0, 1], [154, 65, 159], [157, 123, 68], [154, 148, 166], [120, 26, 159], [103, 166, 132], [59, 15, 102], [77, 70, 153]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [160, 137], []]
 b := ![[], [48, 39, 71], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [6, 56, 134, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-14530223447, -14941194339, 5900045412, -19627853130, -22280042509]
  a := ![-241, -275, 228, -100, -509]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![13778994555, 16496415668, 26358801091, -19627853130, -22280042509]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 5177717 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2065, -4489, -2533, 1452, 3648]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![-2065, -4489, -2533, 1452, 3648]] 
 ![![173, 0, 0, 0, 0], ![0, 173, 0, 0, 0], ![8, 158, 1, 0, 0], ![97, 40, 0, 1, 0], ![70, 135, 0, 0, 1]] where
  M :=![![![-2065, -4489, -2533, 1452, 3648], ![-2094, -5274, -3001, 1692, 4320], ![-2598, -6011, -3402, 1932, 4896], ![1664, 3860, 2188, -1247, -3152], ![594, 1469, 837, -476, -1207]]]
  hmulB := by decide  
  f := ![![![19, -25, 61, 156, -192]], ![![606, 756, -1033, -492, 1632]], ![![526, 661, -906, -444, 1440]], ![![159, 167, -211, -19, 272]], ![![462, 563, -762, -328, 1177]]]
  g := ![![![-2185, -895, -2533, 1452, 3648], ![-2570, -1052, -3001, 1692, 4320], ![-2922, -1195, -3402, 1932, 4896], ![1883, 772, 2188, -1247, -3152], ![720, 296, 837, -476, -1207]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P1 : CertificateIrreducibleZModOfList' 173 2 2 7 [152, 133, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 172], [0, 1]]
 g := ![![[109, 140], [150], [155, 21], [65, 15], [151], [113, 43], [1]], ![[0, 33], [150], [130, 152], [146, 158], [151], [103, 130], [1]]]
 h' := ![![[40, 172], [22, 60], [141, 82], [154, 59], [36, 19], [124, 155], [21, 40], [0, 1]], ![[0, 1], [0, 113], [134, 91], [92, 114], [104, 154], [96, 18], [64, 133], [40, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [143]]
 b := ![[], [127, 158]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N1 : CertifiedPrimeIdeal' SI173N1 173 where
  n := 2
  hpos := by decide
  P := [152, 133, 1]
  hirr := P173P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![282694, 184142, 19964, 641888, -78032]
  a := ![98, 126, -136, -32, 304]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-327618, -104690, 19964, 641888, -78032]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N1 B_one_repr
lemma NI173N1 : Nat.card (O ⧸ I173N1) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![19, -25, 61, 156, -192]] ![![-2065, -4489, -2533, 1452, 3648]]
  ![![173, 0, 0, 0, 0]] where
 M := ![![![173, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![551, -140, -206, 28, 288]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![551, -140, -206, 28, 288]] 
 ![![179, 0, 0, 0, 0], ![0, 179, 0, 0, 0], ![0, 0, 179, 0, 0], ![37, 139, 63, 1, 0], ![122, 165, 156, 0, 1]] where
  M :=![![![551, -140, -206, 28, 288], ![-548, -79, 324, -112, -352], ![792, 272, -335, 848, -192], ![36, 296, -324, -289, 600], ![148, -96, 186, 580, -653]]]
  hmulB := by decide  
  f := ![![![-155, -324, -154, 44, 192]], ![![-364, -557, -116, -224, -32]], ![![-1656, -1872, 275, -2096, -1728]], ![![-901, -1161, -23, -909, -600]], ![![-1890, -2371, 30, -2012, -1413]]]
  g := ![![![-199, -288, -262, 28, 288], ![260, 411, 348, -112, -352], ![-40, -480, -133, 848, -192], ![-349, -327, -423, -289, 600], ![326, 151, 366, 580, -653]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 3 2 7 [79, 1, 7, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [104, 15, 64], [68, 163, 115], [0, 1]]
 g := ![![[44, 21, 31], [19, 153, 4], [146, 47], [148, 57], [73, 20, 173], [48, 172, 1], []], ![[123, 153, 44, 87], [18, 56], [31, 82], [166, 141], [156, 124, 91, 168], [106, 4, 147, 95], [98, 158]], ![[78, 25, 34, 6], [50, 172, 176, 102], [26, 27], [88, 88], [163, 98, 50, 175], [16, 121, 112, 99], [47, 158]]]
 h' := ![![[104, 15, 64], [110, 161, 63], [51, 89, 177], [32, 140, 88], [140, 152, 86], [146, 147, 129], [0, 0, 1], [0, 1]], ![[68, 163, 115], [12, 178, 167], [116, 28], [136, 1, 34], [177, 127, 118], [101, 139, 5], [31, 27, 163], [104, 15, 64]], ![[0, 1], [73, 19, 128], [164, 62, 2], [41, 38, 57], [38, 79, 154], [34, 72, 45], [16, 152, 15], [68, 163, 115]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59, 120], []]
 b := ![[], [86, 43, 110], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 3
  hpos := by decide
  P := [79, 1, 7, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![59680688051, 60044898474, -22499003304, 83950893125, 85102841813]
  a := ![374, 413, -313, 219, 701]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-75022620440, -143302224274, -103840494933, 83950893125, 85102841813]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 5735339 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-155, -324, -154, 44, 192]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![-155, -324, -154, 44, 192]] 
 ![![179, 0, 0, 0, 0], ![0, 179, 0, 0, 0], ![91, 139, 1, 0, 0], ![95, 173, 0, 1, 0], ![1, 31, 0, 0, 1]] where
  M :=![![![-155, -324, -154, 44, 192], ![-364, -557, -116, -224, -32], ![-1656, -1872, 275, -2096, -1728], ![-620, -472, 380, -1155, -1192], ![-1004, -944, 398, -1580, -1503]]]
  hmulB := by decide  
  f := ![![![551, -140, -206, 28, 288]], ![![-548, -79, 324, -112, -352]], ![![-141, -131, 145, -68, -128]], ![![-237, -149, 202, -95, -184]], ![![-91, -15, 56, -16, -63]]]
  g := ![![![53, 42, -154, 44, 192], ![176, 309, -116, -224, -32], ![973, 2101, 275, -2096, -1728], ![423, 1025, 380, -1155, -1192], ![639, 1473, 398, -1580, -1503]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P1 : CertificateIrreducibleZModOfList' 179 2 2 7 [128, 111, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [68, 178], [0, 1]]
 g := ![![[61, 42], [64, 46], [141], [76], [176, 46], [63, 149], [1]], ![[53, 137], [149, 133], [141], [76], [82, 133], [171, 30], [1]]]
 h' := ![![[68, 178], [42, 20], [53, 15], [77, 118], [26, 75], [170, 164], [51, 68], [0, 1]], ![[0, 1], [149, 159], [178, 164], [46, 61], [114, 104], [45, 15], [21, 111], [68, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [144]]
 b := ![[], [58, 72]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N1 : CertifiedPrimeIdeal' SI179N1 179 where
  n := 2
  hpos := by decide
  P := [128, 111, 1]
  hirr := P179P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![236303, 231685, -42340, 409513, 306024]
  a := ![-100, -107, 72, -79, -161]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-196204, -414612, -42340, 409513, 306024]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N1 B_one_repr
lemma NI179N1 : Nat.card (O ⧸ I179N1) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![551, -140, -206, 28, 288]] ![![-155, -324, -154, 44, 192]]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0, 0, 0]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0, 0, 0]] 
 ![![181, 0, 0, 0, 0], ![0, 181, 0, 0, 0], ![0, 0, 181, 0, 0], ![0, 0, 0, 181, 0], ![0, 0, 0, 0, 181]] where
  M :=![![![181, 0, 0, 0, 0], ![0, 181, 0, 0, 0], ![0, 0, 181, 0, 0], ![0, 0, 0, 181, 0], ![0, 0, 0, 0, 181]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 5 2 7 [40, 51, 23, 115, 118, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [90, 25, 92, 88, 52], [168, 129, 119, 44, 66], [152, 162, 117, 7, 28], [15, 45, 34, 42, 35], [0, 1]]
 g := ![![[43, 124, 119, 99, 177], [39, 68, 173, 52], [54, 128, 139, 153, 43], [160, 97, 99, 42], [29, 85, 139, 76, 168], [1], []], ![[167, 123, 46, 159, 54, 176, 137, 52], [144, 89, 89, 16], [17, 126, 99, 79, 61, 72, 45, 11], [50, 150, 33, 33], [28, 162, 94, 60, 15, 119, 12, 167], [126, 157, 178, 18, 112, 115, 65, 65], [35, 168, 133, 170]], ![[176, 131, 128, 42, 131, 9, 159, 123], [100, 31, 177, 42], [0, 175, 14, 88, 104, 8, 138, 17], [98, 65, 42, 152], [5, 165, 86, 164, 36, 108, 11, 104], [29, 74, 10, 120, 137, 2, 160, 50], [75, 102, 48, 12]], ![[101, 92, 149, 36, 122, 0, 47, 88], [60, 39, 45, 43], [31, 110, 79, 139, 179, 82, 90, 155], [20, 111, 165, 4], [56, 25, 153, 35, 57, 129, 19, 118], [120, 174, 54, 169, 113, 90, 144, 74], [20, 87, 9, 60]], ![[72, 44, 74, 12, 141, 68, 164, 88], [180, 118, 101, 44], [180, 94, 63, 113, 0, 113, 37, 76], [107, 43, 78, 49], [86, 145, 4, 180, 111, 121, 180, 109], [77, 7, 170, 116, 15, 33, 91, 23], [28, 165, 113, 139]]]
 h' := ![![[90, 25, 92, 88, 52], [32, 142, 61, 174, 143], [12, 89, 105, 146, 140], [162, 118, 17, 79, 119], [107, 160, 34, 63, 122], [141, 130, 158, 66, 63], [0, 0, 1], [0, 1]], ![[168, 129, 119, 44, 66], [28, 125, 71, 9, 1], [38, 57, 125, 47, 177], [66, 161, 121, 135, 126], [165, 152, 23, 161, 24], [114, 77, 120, 22, 48], [3, 158, 139, 54, 77], [90, 25, 92, 88, 52]], ![[152, 162, 117, 7, 28], [126, 176, 8, 25, 119], [169, 0, 3, 47, 122], [63, 142, 11, 134, 148], [1, 69, 73, 3, 40], [25, 24, 107, 15, 36], [65, 144, 175, 93, 53], [168, 129, 119, 44, 66]], ![[15, 45, 34, 42, 35], [96, 23, 130, 134, 36], [163, 47, 65, 39, 119], [43, 38, 131, 155, 66], [149, 146, 87, 114, 2], [27, 111, 125, 13, 62], [41, 41, 83, 115, 149], [152, 162, 117, 7, 28]], ![[0, 1], [83, 77, 92, 20, 63], [119, 169, 64, 83, 166], [89, 84, 82, 40, 84], [176, 16, 145, 21, 174], [49, 20, 33, 65, 153], [10, 19, 145, 100, 83], [15, 45, 34, 42, 35]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60, 31, 138, 140], [], [], []]
 b := ![[], [92, 165, 180, 126, 53], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 5
  hpos := by decide
  P := [40, 51, 23, 115, 118, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6941298700237095274, 6915563346041662863, -2315392441667972623, 10273104122244405642, 9548810928207401850]
  a := ![325, 365, -289, 164, 647]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![38349716575895554, 38207532298572723, -12792223434629683, 56757481338366882, 52755861481808850]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 194264244901 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def PBC181 : ContainsPrimesAboveP 181 ![I181N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![181, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 181 (by decide) 𝕀

instance hp191 : Fact (Nat.Prime 191) := {out := by norm_num}

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-245, 88, 72, -18, -102]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![-245, 88, 72, -18, -102]] 
 ![![191, 0, 0, 0, 0], ![0, 191, 0, 0, 0], ![66, 109, 1, 0, 0], ![165, 130, 0, 1, 0], ![18, 158, 0, 0, 1]] where
  M :=![![![-245, 88, 72, -18, -102], ![156, -59, -44, 12, 60], ![-96, 44, 13, -24, -24], ![52, -32, -10, -3, 14], ![-22, 16, -4, -10, -1]]]
  hmulB := by decide  
  f := ![![![305, 728, 412, -234, -594]], ![![348, 835, 476, -276, -684]], ![![306, 733, 417, -240, -600]], ![![499, 1194, 678, -389, -976]], ![![316, 758, 432, -250, -621]]]
  g := ![![![-1, 56, 72, -18, -102], ![0, -33, -44, 12, 60], ![18, 29, 13, -24, -24], ![5, -4, -10, -3, 14], ![10, 10, -4, -10, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [17, 121, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [70, 190], [0, 1]]
 g := ![![[97, 45], [128, 20], [42, 59], [13, 115], [103, 121], [67, 125], [1]], ![[0, 146], [0, 171], [161, 132], [41, 76], [169, 70], [31, 66], [1]]]
 h' := ![![[70, 190], [116, 42], [50, 163], [161, 170], [159, 45], [7, 180], [174, 70], [0, 1]], ![[0, 1], [0, 149], [0, 28], [28, 21], [62, 146], [1, 11], [108, 121], [70, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77]]
 b := ![[], [85, 134]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [17, 121, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![860918, 789849, -54764, 1672503, 841776]
  a := ![194, 219, -176, 93, 393]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1500731, -1799303, -54764, 1672503, 841776]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-41, 18, 14, -4, -20]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![-41, 18, 14, -4, -20]] 
 ![![191, 0, 0, 0, 0], ![24, 1, 0, 0, 0], ![188, 0, 1, 0, 0], ![92, 0, 0, 1, 0], ![70, 0, 0, 0, 1]] where
  M :=![![![-41, 18, 14, -4, -20], ![28, -7, -6, 0, 8], ![-20, 6, 9, -8, -16], ![8, -8, -4, -1, 4], ![-8, -2, 2, -4, -5]]]
  hmulB := by decide  
  f := ![![![-39, -30, 54, -4, -68]], ![![-4, -3, 6, 0, -8]], ![![-40, -30, 53, -8, -64]], ![![-20, -16, 28, -1, -36]], ![![-14, -10, 18, -4, -21]]]
  g := ![![![-7, 18, 14, -4, -20], ![4, -7, -6, 0, 8], ![0, 6, 9, -8, -16], ![4, -8, -4, -1, 4], ![2, -2, 2, -4, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1

def I191N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![26, 49, 26, -13, -36]] i)))

def SI191N2: IdealEqSpanCertificate' Table ![![26, 49, 26, -13, -36]] 
 ![![191, 0, 0, 0, 0], ![68, 1, 0, 0, 0], ![151, 0, 1, 0, 0], ![167, 0, 0, 1, 0], ![61, 0, 0, 0, 1]] where
  M :=![![![26, 49, 26, -13, -36], ![32, 68, 29, -2, -32], ![102, 137, 12, 88, 48], ![17, -6, -35, 66, 82], ![45, 35, -26, 81, 83]]]
  hmulB := by decide  
  f := ![![![118, 19, -18, 173, -102]], ![![44, 10, -11, 58, -28]], ![![68, -12, 20, 141, -126]], ![![113, 25, -25, 157, -82]], ![![19, -12, 16, 52, -57]]]
  g := ![![![-15, 49, 26, -13, -36], ![-35, 68, 29, -2, -32], ![-150, 137, 12, 88, 48], ![-54, -6, -35, 66, 82], ![-89, 35, -26, 81, 83]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N2 : Nat.card (O ⧸ I191N2) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N2)

lemma isPrimeI191N2 : Ideal.IsPrime I191N2 := prime_ideal_of_norm_prime hp191.out _ NI191N2

def I191N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![66, 63, -74, 15, 80]] i)))

def SI191N3: IdealEqSpanCertificate' Table ![![66, 63, -74, 15, 80]] 
 ![![191, 0, 0, 0, 0], ![181, 1, 0, 0, 0], ![91, 0, 1, 0, 0], ![176, 0, 0, 1, 0], ![36, 0, 0, 0, 1]] where
  M :=![![![66, 63, -74, 15, 80], ![-224, -164, 163, -218, -40], ![26, -321, 628, 1200, -1664], ![497, 562, -735, -198, 1054], ![-419, -615, 886, 653, -1577]]]
  hmulB := by decide  
  f := ![![![52470, -18803, -15362, 3833, 21910]], ![![49550, -17751, -14507, 3625, 20694]], ![![25136, -8976, -7360, 1869, 10518]], ![![48291, -17290, -14139, 3544, 20176]], ![![9937, -3539, -2910, 749, 4165]]]
  g := ![![![-53, 63, -74, 15, 80], ![285, -164, 163, -218, -40], ![-787, -321, 628, 1200, -1664], ![-196, 562, -735, -198, 1054], ![-146, -615, 886, 653, -1577]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N3 : Nat.card (O ⧸ I191N3) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N3)

lemma isPrimeI191N3 : Ideal.IsPrime I191N3 := prime_ideal_of_norm_prime hp191.out _ NI191N3
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![-245, 88, 72, -18, -102]] ![![-41, 18, 14, -4, -20]]
  ![![11741, -4246, -3442, 830, 4890]] where
 M := ![![![11741, -4246, -3442, 830, 4890]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI191N1 : IdealMulLeCertificate' Table 
  ![![11741, -4246, -3442, 830, 4890]] ![![26, 49, 26, -13, -36]]
  ![![52470, -18803, -15362, 3833, 21910]] where
 M := ![![![52470, -18803, -15362, 3833, 21910]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI191N2 : IdealMulLeCertificate' Table 
  ![![52470, -18803, -15362, 3833, 21910]] ![![66, 63, -74, 15, 80]]
  ![![191, 0, 0, 0, 0]] where
 M := ![![![191, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-68932, 24915, 20222, -4913, -28750]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![-68932, 24915, 20222, -4913, -28750]] 
 ![![193, 0, 0, 0, 0], ![0, 193, 0, 0, 0], ![0, 0, 193, 0, 0], ![47, 120, 36, 1, 0], ![35, 105, 88, 0, 1]] where
  M :=![![![-68932, 24915, 20222, -4913, -28750], ![44180, -16224, -12933, 2838, 18196], ![-29854, 9063, 8816, -3952, -13688], ![16867, -6970, -4931, 306, 6440], ![-8703, 1913, 2582, -1895, -4481]]]
  hmulB := by decide  
  f := ![![![324, 351, -446, -73, 604]], ![![-1760, -1594, 1851, -666, -1792]], ![![4858, 3039, -2514, 6544, -1744]], ![![-103, -329, 559, 777, -1266]], ![![1321, 580, -213, 2632, -1687]]]
  g := ![![![6053, 18825, 14130, -4913, -28750], ![-3762, -11748, -8893, 2838, 18196], ![3290, 9951, 7024, -3952, -13688], ![-1155, -3730, -3019, 306, 6440], ![1229, 3626, 2410, -1895, -4481]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 3 2 7 [120, 121, 33, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [167, 142, 148], [186, 50, 45], [0, 1]]
 g := ![![[190, 54, 144], [24, 118], [192, 6], [8, 95], [6, 110], [34, 124], [1]], ![[163, 103, 140, 188], [21, 131], [58, 16], [154, 9], [165, 95], [136, 172], [53, 12, 125, 164]], ![[135, 135, 135, 90], [133, 175], [156, 56], [15, 181], [153, 55], [97, 147], [91, 56, 169, 29]]]
 h' := ![![[167, 142, 148], [58, 41, 181], [129, 85, 73], [3, 114, 149], [34, 53, 148], [91, 10, 66], [73, 72, 160], [0, 1]], ![[186, 50, 45], [136, 98, 64], [95, 185, 18], [140, 25, 4], [51, 150, 190], [101, 92, 148], [189, 80, 128], [167, 142, 148]], ![[0, 1], [43, 54, 141], [131, 116, 102], [138, 54, 40], [104, 183, 48], [69, 91, 172], [124, 41, 98], [186, 50, 45]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66, 52], []]
 b := ![[], [119, 131, 177], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 3
  hpos := by decide
  P := [120, 121, 33, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3936320203, 3960362268, -1483330852, 5538071656, 5613106568]
  a := ![151, 167, -127, 88, 284]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2346175013, -6476603244, -3600037764, 5538071656, 5613106568]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 7189057 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-324, -351, 446, 73, -604]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![-324, -351, 446, 73, -604]] 
 ![![193, 0, 0, 0, 0], ![0, 193, 0, 0, 0], ![77, 147, 1, 0, 0], ![167, 120, 0, 1, 0], ![145, 7, 0, 0, 1]] where
  M :=![![![-324, -351, 446, 73, -604], ![1760, 1594, -1851, 666, 1792], ![-4858, -3039, 2514, -6544, 1744], ![-1205, -1882, 2767, 2272, -5098], ![-909, 407, -1378, -4589, 5099]]]
  hmulB := by decide  
  f := ![![![68932, -24915, -20222, 4913, 28750]], ![![-44180, 16224, 12933, -2838, -18196]], ![![-5994, 2370, 1737, -181, -2318]], ![![32089, -11435, -9431, 2485, 13530]], ![![50231, -18140, -14737, 3598, 20963]]]
  g := ![![![211, -365, 446, 73, -604], ![-1175, 939, -1851, 666, 1792], ![3324, 2075, 2514, -6544, 1744], ![754, -3345, 2767, 2272, -5098], ![685, 3720, -1378, -4589, 5099]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P1 : CertificateIrreducibleZModOfList' 193 2 2 7 [155, 146, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [47, 192], [0, 1]]
 g := ![![[179, 139], [12], [25], [130], [118], [129], [47, 1]], ![[150, 54], [12], [25], [130], [118], [129], [94, 192]]]
 h' := ![![[47, 192], [134, 116], [185, 28], [59, 5], [41, 55], [162, 73], [49, 124], [0, 1]], ![[0, 1], [182, 77], [150, 165], [101, 188], [117, 138], [119, 120], [87, 69], [47, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [120]]
 b := ![[], [134, 60]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N1 : CertifiedPrimeIdeal' SI193N1 193 where
  n := 2
  hpos := by decide
  P := [155, 146, 1]
  hirr := P193P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2686676, 2621548, -468855, 4681186, 3401883]
  a := ![-333, -359, 248, -250, -557]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6405402, -2663276, -468855, 4681186, 3401883]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N1 B_one_repr
lemma NI193N1 : Nat.card (O ⧸ I193N1) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![-68932, 24915, 20222, -4913, -28750]] ![![-324, -351, 446, 73, -604]]
  ![![193, 0, 0, 0, 0]] where
 M := ![![![-193, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC193 : ContainsPrimesAboveP 193 ![I193N0, I193N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI193N0
    exact isPrimeI193N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 193 (by decide) (𝕀 ⊙ MulI193N0)
instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5238, 13927, 7950, -4463, -11446]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![5238, 13927, 7950, -4463, -11446]] 
 ![![197, 0, 0, 0, 0], ![0, 197, 0, 0, 0], ![0, 0, 197, 0, 0], ![33, 54, 51, 1, 0], ![67, 29, 32, 0, 1]] where
  M :=![![![5238, 13927, 7950, -4463, -11446], ![6956, 15690, 8887, -5094, -12812], ![7322, 18203, 10442, -6040, -15128], ![-4831, -11814, -6669, 3704, 9556], ![-1989, -4479, -2470, 1311, 3491]]]
  hmulB := by decide  
  f := ![![![-258, -233, 270, -99, -260]], ![![704, 436, -357, 962, -272]], ![![1162, 2495, -3956, -4536, 8240]], ![![439, 714, -1061, -925, 1994]], ![![217, 406, -625, -640, 1245]]]
  g := ![![![4667, 2979, 3055, -4463, -11446], ![5246, 3362, 3445, -5094, -12812], ![6194, 3975, 4074, -6040, -15128], ![-3895, -2482, -2545, 3704, 9556], ![-1417, -896, -919, 1311, 3491]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 3 2 7 [159, 133, 58, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [40, 135, 48], [99, 61, 149], [0, 1]]
 g := ![![[84, 117, 6], [96, 169], [131, 26, 97], [164, 134], [75, 43], [177, 15], [1]], ![[82, 112, 16, 18], [125, 104], [109, 160, 123, 145], [192, 161], [120, 16], [174, 62], [122, 132, 112, 75]], ![[23, 194, 29, 141], [1, 146], [158, 64, 105, 126], [161, 25], [37, 173], [78, 155], [76, 47, 68, 122]]]
 h' := ![![[40, 135, 48], [153, 184, 20], [53, 17, 13], [135, 174, 57], [73, 140, 79], [93, 17, 35], [38, 64, 139], [0, 1]], ![[99, 61, 149], [182, 67, 5], [95, 150, 33], [100, 98, 9], [129, 152, 113], [10, 66, 193], [80, 86, 125], [40, 135, 48]], ![[0, 1], [192, 143, 172], [96, 30, 151], [2, 122, 131], [42, 102, 5], [58, 114, 166], [7, 47, 130], [99, 61, 149]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [142, 49], []]
 b := ![[], [130, 183, 118], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 3
  hpos := by decide
  P := [159, 133, 58, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-354868143, -355256169, 130881423, -504565626, -497372400]
  a := ![-67, -73, 53, -45, -119]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![251876895, 209721255, 212079417, -504565626, -497372400]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 7645373 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-258, -233, 270, -99, -260]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![-258, -233, 270, -99, -260]] 
 ![![197, 0, 0, 0, 0], ![0, 197, 0, 0, 0], ![167, 176, 1, 0, 0], ![145, 191, 0, 1, 0], ![173, 117, 0, 0, 1]] where
  M :=![![![-258, -233, 270, -99, -260], ![704, 436, -357, 962, -272], ![1162, 2495, -3956, -4536, 8240], ![-2281, -2442, 3107, 430, -4154], ![2435, 3109, -4270, -2193, 6893]]]
  hmulB := by decide  
  f := ![![![5238, 13927, 7950, -4463, -11446]], ![![6956, 15690, 8887, -5094, -12812]], ![![10692, 25916, 14732, -8365, -21226]], ![![10575, 25403, 14434, -8205, -20798]], ![![8721, 21526, 12247, -6938, -17643]]]
  g := ![![![71, 8, 270, -99, -260], ![-163, -450, -357, 962, -272], ![-538, 3051, -3956, -4536, 8240], ![686, -738, 3107, 430, -4154], ![-807, 1863, -4270, -2193, 6893]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P1 : CertificateIrreducibleZModOfList' 197 2 2 7 [190, 35, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [162, 196], [0, 1]]
 g := ![![[192, 28], [135], [164, 7], [133], [178], [136], [162, 1]], ![[0, 169], [135], [116, 190], [133], [178], [136], [127, 196]]]
 h' := ![![[162, 196], [131, 15], [163, 23], [1, 106], [45, 112], [104, 93], [149, 50], [0, 1]], ![[0, 1], [0, 182], [146, 174], [34, 91], [65, 85], [1, 104], [172, 147], [162, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [147]]
 b := ![[], [55, 172]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N1 : CertifiedPrimeIdeal' SI197N1 197 where
  n := 2
  hpos := by decide
  P := [190, 35, 1]
  hirr := P197P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1405728, 1371178, -248086, 2443462, 1774126]
  a := ![241, 260, -182, 176, 407]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3139034, -3194110, -248086, 2443462, 1774126]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N1 B_one_repr
lemma NI197N1 : Nat.card (O ⧸ I197N1) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![5238, 13927, 7950, -4463, -11446]] ![![-258, -233, 270, -99, -260]]
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


lemma PB1640I4_primes (p : ℕ) :
  p ∈ Set.range ![157, 163, 167, 173, 179, 181, 191, 193, 197] ↔ Nat.Prime p ∧ 151 < p ∧ p ≤ 197 := by
  rw [← List.mem_ofFn']
  convert primes_range 151 197 (by omega)

def PB1640I4 : PrimesBelowBoundCertificateInterval O 151 197 1640 where
  m := 9
  g := ![2, 1, 1, 2, 2, 1, 4, 2, 2]
  P := ![157, 163, 167, 173, 179, 181, 191, 193, 197]
  hP := PB1640I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I157N0, I157N1]
    · exact ![I163N0]
    · exact ![I167N0]
    · exact ![I173N0, I173N1]
    · exact ![I179N0, I179N1]
    · exact ![I181N0]
    · exact ![I191N0, I191N1, I191N2, I191N3]
    · exact ![I193N0, I193N1]
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
    · exact ![3869893, 24649]
    · exact ![115063617043]
    · exact ![129891985607]
    · exact ![5177717, 29929]
    · exact ![5735339, 32041]
    · exact ![194264244901]
    · exact ![36481, 191, 191, 191]
    · exact ![7189057, 37249]
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
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
      exact NI197N1
  β := ![I191N1, I191N2, I191N3]
  Il := ![[], [], [], [], [], [], [I191N1, I191N2, I191N3], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
