
import IdealArithmetic.Examples.NF5_3_729000000_3.RI5_3_729000000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9235, -5585, 376, -787, 1766]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![9235, -5585, 376, -787, 1766]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![0, 0, 107, 0, 0], ![0, 0, 0, 107, 0], ![66, 65, 3, 31, 1]] where
  M :=![![![9235, -5585, 376, -787, 1766], ![-7064, 4505, -574, 560, -1190], ![2380, -2069, 935, -539, 490], ![2552, -1624, -312, 949, -532], ![3560, -1176, -986, -202, 991]]]
  hmulB := by decide  
  f := ![![![25953, 6431, -35610, -7847, -25132]], ![![100528, 24913, -137930, -30394, -97346]], ![![194692, 48251, -267125, -58863, -188528]], ![![326792, 80992, -448368, -98801, -316444]], ![![179890, 44582, -246817, -54388, -174195]]]
  g := ![![![-1003, -1125, -46, -519, 1766], ![668, 765, 28, 350, -1190], ![-280, -317, -5, -147, 490], ![352, 308, 12, 163, -532], ![-578, -613, -37, -289, 991]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 4 2 6 [37, 41, 72, 16, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [41, 21, 66, 43], [54, 34, 48, 56], [103, 51, 100, 8], [0, 1]]
 g := ![![[103, 80, 45, 30], [86, 20, 87, 83], [23, 43, 89], [41, 84, 51, 89], [77, 91, 1], []], ![[14, 44, 84, 39, 73, 21], [79, 26, 97, 0, 12, 68], [81, 46, 12], [106, 5, 4, 91, 21, 93], [23, 104, 10], [52, 79, 50, 41, 66, 6]], ![[68, 49, 16, 93, 92, 105], [37, 81, 56, 65, 4, 33], [85, 94, 99], [9, 94, 57, 2, 63, 101], [37, 6, 89], [44, 20, 100, 26, 8, 29]], ![[91, 33, 66, 21, 73, 55], [64, 40, 58, 96, 50, 74], [11, 97, 37], [8, 2, 105, 8, 14, 91], [98, 42, 57], [87, 81, 24, 99, 94, 84]]]
 h' := ![![[41, 21, 66, 43], [28, 6, 82, 43], [45, 92, 84, 46], [88, 21, 89, 93], [40, 3, 104, 93], [0, 0, 0, 1], [0, 1]], ![[54, 34, 48, 56], [53, 95, 35, 31], [68, 77, 24, 33], [47, 11, 71, 71], [16, 39, 33, 12], [15, 54, 3, 44], [41, 21, 66, 43]], ![[103, 51, 100, 8], [40, 51, 94, 91], [6, 4, 66, 22], [72, 9, 105, 62], [32, 49, 4, 33], [44, 103, 74, 14], [54, 34, 48, 56]], ![[0, 1], [24, 62, 3, 49], [77, 41, 40, 6], [22, 66, 56, 95], [98, 16, 73, 76], [34, 57, 30, 48], [103, 51, 100, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [14, 56, 81], []]
 b := ![[], [], [36, 36, 77, 96], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 4
  hpos := by decide
  P := [37, 41, 72, 16, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![46434221, 103714431, -103764662, 8956111, 202290234]
  a := ![0, -8, -3, 2, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-124343189, -121917297, -6641452, -58523749, 202290234]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 131079601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-25953, -6431, 35610, 7847, 25132]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![-25953, -6431, 35610, 7847, 25132]] 
 ![![107, 0, 0, 0, 0], ![26, 1, 0, 0, 0], ![90, 0, 1, 0, 0], ![101, 0, 0, 1, 0], ![51, 0, 0, 0, 1]] where
  M :=![![![-25953, -6431, 35610, 7847, 25132], ![-100528, -24913, 137930, 30394, 97346], ![-194692, -48251, 267125, 58863, 188528], ![-326792, -80992, 448368, 98801, 316444], ![-286384, -70978, 392926, 86584, 277315]]]
  hmulB := by decide  
  f := ![![![-9235, 5585, -376, 787, -1766]], ![![-2178, 1315, -86, 186, -418]], ![![-7790, 4717, -325, 667, -1490]], ![![-8741, 5287, -352, 734, -1662]], ![![-4435, 2673, -170, 377, -851]]]
  g := ![![![-48018, -6431, 35610, 7847, 25132], ![-185990, -24913, 137930, 30394, 97346], ![-360201, -48251, 267125, 58863, 188528], ![-604595, -80992, 448368, 98801, 316444], ![-529835, -70978, 392926, 86584, 277315]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![9235, -5585, 376, -787, 1766]] ![![-25953, -6431, 35610, 7847, 25132]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1747, -1055, 74, -158, 342]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![1747, -1055, 74, -158, 342]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![61, 77, 1, 0, 0], ![99, 97, 0, 1, 0], ![59, 12, 0, 0, 1]] where
  M :=![![![1747, -1055, 74, -158, 342], ![-1368, 821, -58, 122, -264], ![528, -327, 29, -48, 102], ![480, -282, 8, -35, 90], ![556, -328, 18, -53, 113]]]
  hmulB := by decide  
  f := ![![![-545, -143, 736, 162, 522]], ![![-2088, -529, 2846, 626, 2016]], ![![-1817, -463, 2473, 544, 1752]], ![![-2415, -616, 3286, 723, 2328]], ![![-579, -149, 786, 173, 557]]]
  g := ![![![-67, 41, 74, -158, 342], ![52, -31, -58, 122, -264], ![-23, 8, 29, -48, 102], ![-17, 13, 8, -35, 90], ![-18, 19, 18, -53, 113]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [39, 72, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [37, 108], [0, 1]]
 g := ![![[27, 61], [66], [21, 16], [9, 48], [48], [37, 1]], ![[104, 48], [66], [68, 93], [41, 61], [48], [74, 108]]]
 h' := ![![[37, 108], [17, 37], [53, 75], [85, 105], [3, 87], [83, 22], [0, 1]], ![[0, 1], [78, 72], [103, 34], [46, 4], [61, 22], [25, 87], [37, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62]]
 b := ![[], [26, 31]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [39, 72, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1728, 13661, -30044, 84823, -3103]
  a := ![3, -61, 2, -69, 11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-58532, -53794, -30044, 84823, -3103]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![213137, 52824, -292430, -64439, -206388]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![213137, 52824, -292430, -64439, -206388]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![76, 13, 1, 0, 0], ![102, 33, 0, 1, 0], ![70, 67, 0, 0, 1]] where
  M :=![![![213137, 52824, -292430, -64439, -206388], ![825552, 204605, -1132680, -249594, -799410], ![1598820, 396252, -2193625, -483381, -1548192], ![2683608, 665106, -3681984, -811351, -2598630], ![2351772, 582864, -3226696, -711025, -2277301]]]
  hmulB := by decide  
  f := ![![![-1147, -486, 74, 23, 198]], ![![-792, -1423, 216, -96, 534]], ![![-904, -517, 79, 5, 204]], ![![-1314, -885, 132, -7, 348]], ![![-1222, -1183, 180, -45, 455]]]
  g := ![![![398695, 181733, -292430, -64439, -206388], ![1544280, 703913, -1132680, -249594, -799410], ![2990758, 1363246, -2193625, -483381, -1548192], ![5019966, 2288199, -3681984, -811351, -2598630], ![4399232, 2005256, -3226696, -711025, -2277301]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P1 : CertificateIrreducibleZModOfList' 109 2 2 6 [84, 48, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [61, 108], [0, 1]]
 g := ![![[94, 61], [104], [95, 64], [91, 26], [74], [61, 1]], ![[0, 48], [104], [75, 45], [42, 83], [74], [13, 108]]]
 h' := ![![[61, 108], [77, 72], [86, 70], [95, 101], [107, 74], [108, 40], [0, 1]], ![[0, 1], [0, 37], [105, 39], [43, 8], [43, 35], [41, 69], [61, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [72]]
 b := ![[], [101, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N1 : CertifiedPrimeIdeal' SI109N1 109 where
  n := 2
  hpos := by decide
  P := [84, 48, 1]
  hirr := P109P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-419, -232, 767, -224, 900]
  a := ![1, -6, -1, -3, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-907, -579, 767, -224, 900]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N1 B_one_repr
lemma NI109N1 : Nat.card (O ⧸ I109N1) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N1

def I109N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 7, 0, -29, 30]] i)))

def SI109N2: IdealEqSpanCertificate' Table ![![7, 7, 0, -29, 30]] 
 ![![109, 0, 0, 0, 0], ![38, 1, 0, 0, 0], ![41, 0, 1, 0, 0], ![74, 0, 0, 1, 0], ![52, 0, 0, 0, 1]] where
  M :=![![![7, 7, 0, -29, 30], ![-120, -111, 194, 28, -114], ![228, 179, -453, 223, -30], ![120, 196, -8, -675, 696], ![-384, -336, 694, -128, -173]]]
  hmulB := by decide  
  f := ![![![-941, -2311, -1734, -535, -492]], ![![-310, -831, -674, -204, -210]], ![![-277, -874, -793, -234, -276]], ![![-466, -1530, -1420, -417, -504]], ![![-284, -1054, -1042, -302, -389]]]
  g := ![![![3, 7, 0, -29, 30], ![0, -111, 194, 28, -114], ![-27, 179, -453, 223, -30], ![62, 196, -8, -675, 696], ![22, -336, 694, -128, -173]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N2 : Nat.card (O ⧸ I109N2) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N2)

lemma isPrimeI109N2 : Ideal.IsPrime I109N2 := prime_ideal_of_norm_prime hp109.out _ NI109N2
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![1747, -1055, 74, -158, 342]] ![![213137, 52824, -292430, -64439, -206388]]
  ![![1619, 641, -2620, -549, -1896]] where
 M := ![![![1619, 641, -2620, -549, -1896]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![1619, 641, -2620, -549, -1896]] ![![7, 7, 0, -29, 30]]
  ![![109, 0, 0, 0, 0]] where
 M := ![![![-763, 654, -218, 0, 0]]]
 hmul := by decide  
 g := ![![![![-7, 6, -2, 0, 0]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N1, I109N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N1
    exact isPrimeI109N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0 ⊙ MulI109N1)
instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1725417, -1039658, 73300, -156221, 337000]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![1725417, -1039658, 73300, -156221, 337000]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![40, 17, 1, 0, 0], ![111, 14, 0, 1, 0], ![1, 76, 0, 0, 1]] where
  M :=![![![1725417, -1039658, 73300, -156221, 337000], ![-1348000, 812275, -57316, 122042, -263326], ![526652, -317290, 22297, -47695, 102800], ![468400, -282158, 19768, -42429, 91378], ![544548, -328052, 23020, -49321, 106265]]]
  hmulB := by decide  
  f := ![![![593, 608, -820, -459, 814]], ![![-3256, -2773, 6100, -1536, -1126]], ![![-260, -193, 573, -321, 68]], ![![295, 372, -220, -736, 832]], ![![-2251, -1910, 4232, -1118, -727]]]
  g := ![![![139796, -227528, 73300, -156221, 337000], ![-109192, 177795, -57316, 122042, -263326], ![42709, -69393, 22297, -47695, 102800], ![38017, -61672, 19768, -42429, 91378], ![44178, -71726, 23020, -49321, 106265]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [102, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [95, 112], [0, 1]]
 g := ![![[60, 41], [63], [61], [36], [53, 16], [95, 1]], ![[0, 72], [63], [61], [36], [104, 97], [77, 112]]]
 h' := ![![[95, 112], [17, 70], [62, 17], [42, 20], [18, 6], [28, 109], [0, 1]], ![[0, 1], [0, 43], [95, 96], [21, 93], [23, 107], [100, 4], [95, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [70]]
 b := ![[], [89, 35]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [102, 18, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8751, 693, 13886, -1533, 17405]
  a := ![1, 26, 4, 10, 23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3641, -13599, 13886, -1533, 17405]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-34421, -8531, 47228, 10407, 33332]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![-34421, -8531, 47228, 10407, 33332]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![42, 29, 1, 0, 0], ![25, 28, 0, 1, 0], ![106, 101, 0, 0, 1]] where
  M :=![![![-34421, -8531, 47228, 10407, 33332], ![-133328, -33043, 182930, 40310, 129106], ![-258212, -63995, 354275, 78067, 250036], ![-433408, -107416, 594648, 131035, 419684], ![-379816, -94134, 521118, 114832, 367789]]]
  hmulB := by decide  
  f := ![![![123, -13, -26, 29, -22]], ![![88, 199, -158, -88, 130]], ![![66, 44, -45, -13, 24]], ![![51, 47, -50, -8, 22]], ![![198, 169, -172, -52, 99]]]
  g := ![![![-51428, -44567, 47228, 10407, 33332], ![-199198, -172623, 182930, 40310, 129106], ![-385781, -334314, 354275, 78067, 250036], ![-647531, -561144, 594648, 131035, 419684], ![-567462, -491757, 521118, 114832, 367789]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P1 : CertificateIrreducibleZModOfList' 113 2 2 6 [44, 61, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [52, 112], [0, 1]]
 g := ![![[81, 18], [98], [18], [52], [10, 105], [52, 1]], ![[0, 95], [98], [18], [52], [46, 8], [104, 112]]]
 h' := ![![[52, 112], [46, 73], [8, 18], [3, 73], [12, 74], [85, 61], [0, 1]], ![[0, 1], [0, 40], [40, 95], [70, 40], [18, 39], [93, 52], [52, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [86]]
 b := ![[], [12, 43]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N1 : CertifiedPrimeIdeal' SI113N1 113 where
  n := 2
  hpos := by decide
  P := [44, 61, 1]
  hirr := P113P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8368, -7491, 12970, 3390, -7704]
  a := ![-1, -6, -4, 13, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1582, 2651, 12970, 3390, -7704]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N1 B_one_repr
lemma NI113N1 : Nat.card (O ⧸ I113N1) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N1

def I113N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![135, 32, -200, -44, -140]] i)))

def SI113N2: IdealEqSpanCertificate' Table ![![135, 32, -200, -44, -140]] 
 ![![113, 0, 0, 0, 0], ![21, 1, 0, 0, 0], ![62, 0, 1, 0, 0], ![73, 0, 0, 1, 0], ![82, 0, 0, 0, 1]] where
  M :=![![![135, 32, -200, -44, -140], ![560, 127, -776, -172, -544], ![1088, 264, -1505, -332, -1060], ![1840, 456, -2528, -557, -1784], ![1616, 404, -2216, -488, -1565]]]
  hmulB := by decide  
  f := ![![![71, 48, -216, 252, -164]], ![![19, 15, -48, 40, -20]], ![![18, 8, -81, 132, -100]], ![![63, 40, -184, 215, -140]], ![![78, 60, -200, 176, -93]]]
  g := ![![![235, 32, -200, -44, -140], ![913, 127, -776, -172, -544], ![1770, 264, -1505, -332, -1060], ![2973, 456, -2528, -557, -1784], ![2606, 404, -2216, -488, -1565]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N2 : Nat.card (O ⧸ I113N2) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N2)

lemma isPrimeI113N2 : Ideal.IsPrime I113N2 := prime_ideal_of_norm_prime hp113.out _ NI113N2
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![1725417, -1039658, 73300, -156221, 337000]] ![![-34421, -8531, 47228, 10407, 33332]]
  ![![7442835, 530303, -8025572, -1922896, -5408668]] where
 M := ![![![7442835, 530303, -8025572, -1922896, -5408668]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI113N1 : IdealMulLeCertificate' Table 
  ![![7442835, 530303, -8025572, -1922896, -5408668]] ![![135, 32, -200, -44, -140]]
  ![![113, 0, 0, 0, 0]] where
 M := ![![![-19708606059, -4875174255, 27025093108, 5956276104, 19071636472]]]
 hmul := by decide  
 g := ![![![![-174412443, -43143135, 239160116, 52710408, 168775544]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-751, -184, 1030, 228, 732]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![-751, -184, 1030, 228, 732]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![0, 0, 127, 0, 0], ![8, 72, 72, 1, 0], ![107, 3, 98, 0, 1]] where
  M :=![![![-751, -184, 1030, 228, 732], ![-2928, -729, 4024, 872, 2832], ![-5664, -1412, 7767, 1736, 5448], ![-9432, -2296, 12920, 2871, 9240], ![-8328, -2064, 11440, 2476, 8087]]]
  hmulB := by decide  
  f := ![![![-4849, 2992, -214, 444, -972]], ![![3888, -2231, 152, -344, 720]], ![![-1440, 956, -71, 136, -312]], ![![1072, -528, 32, -89, 168]], ![![-5117, 3213, -232, 472, -1045]]]
  g := ![![![-637, -148, -686, 228, 732], ![-2464, -567, -2648, 872, 2832], ![-4744, -1124, -5127, 1736, 5448], ![-8040, -1864, -8656, 2871, 9240], ![-7035, -1611, -7554, 2476, 8087]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [104, 21, 26, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [94, 26, 13], [7, 100, 114], [0, 1]]
 g := ![![[109, 6, 74], [107, 21, 74], [87, 99, 100], [43, 118, 8], [121, 26, 41], [1]], ![[118, 5, 40, 99], [64, 59, 58, 82], [55, 101, 35, 76], [92, 48, 1, 70], [6, 123, 102, 107], [113, 20, 2, 38]], ![[109, 107, 11, 53], [25, 120, 113, 75], [36, 41, 120, 43], [103, 66, 89, 5], [83, 67, 54, 58], [81, 72, 126, 89]]]
 h' := ![![[94, 26, 13], [48, 86, 57], [96, 36, 57], [100, 27, 10], [116, 110, 95], [23, 106, 101], [0, 1]], ![[7, 100, 114], [63, 111, 87], [110, 81, 72], [17, 44, 81], [98, 38, 8], [63, 98, 48], [94, 26, 13]], ![[0, 1], [26, 57, 110], [105, 10, 125], [106, 56, 36], [100, 106, 24], [47, 50, 105], [7, 100, 114]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34, 91], []]
 b := ![[], [34, 34, 120], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [104, 21, 26, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7635368, 7819702, -11154380, -6478482, 11525870]
  a := ![0, -2, 4, -26, 22]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9242558, 3462148, -5308968, -6478482, 11525870]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 2048383 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4849, -2992, 214, -444, 972]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![4849, -2992, 214, -444, 972]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![65, 55, 1, 0, 0], ![108, 56, 0, 1, 0], ![8, 111, 0, 0, 1]] where
  M :=![![![4849, -2992, 214, -444, 972], ![-3888, 2231, -152, 344, -720], ![1440, -956, 71, -136, 312], ![1320, -808, 56, -121, 264], ![1560, -912, 64, -140, 295]]]
  hmulB := by decide  
  f := ![![![751, 184, -1030, -228, -732]], ![![2928, 729, -4024, -872, -2832]], ![![1697, 421, -2331, -508, -1644]], ![![2004, 496, -2752, -601, -1944]], ![![2672, 665, -3672, -796, -2585]]]
  g := ![![![245, -770, 214, -444, 972], ![-200, 561, -152, 344, -720], ![71, -251, 71, -136, 312], ![68, -208, 56, -121, 264], ![80, -231, 64, -140, 295]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P1 : CertificateIrreducibleZModOfList' 127 2 2 6 [36, 40, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [87, 126], [0, 1]]
 g := ![![[114, 60], [19, 71], [4, 37], [111, 16], [19, 76], [87, 1]], ![[0, 67], [100, 56], [48, 90], [106, 111], [27, 51], [47, 126]]]
 h' := ![![[87, 126], [78, 21], [110, 84], [68, 52], [78, 4], [43, 40], [0, 1]], ![[0, 1], [0, 106], [52, 43], [20, 75], [45, 123], [94, 87], [87, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [23, 71]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N1 : CertifiedPrimeIdeal' SI127N1 127 where
  n := 2
  hpos := by decide
  P := [36, 40, 1]
  hirr := P127P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4171, -4221, 7721, 1185, -3433]
  a := ![13, -6, -3, 8, -19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4776, -899, 7721, 1185, -3433]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N1 B_one_repr
lemma NI127N1 : Nat.card (O ⧸ I127N1) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![-751, -184, 1030, 228, 732]] ![![4849, -2992, 214, -444, 972]]
  ![![127, 0, 0, 0, 0]] where
 M := ![![![-127, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC127 : ContainsPrimesAboveP 127 ![I127N0, I127N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
    exact isPrimeI127N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 127 (by decide) (𝕀 ⊙ MulI127N0)
instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7521, 7261, -11996, -2921, 8258]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![7521, 7261, -11996, -2921, 8258]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![0, 0, 131, 0, 0], ![55, 31, 78, 1, 0], ![73, 122, 17, 0, 1]] where
  M :=![![![7521, 7261, -11996, -2921, 8258], ![-33032, -26833, 64070, -26408, -1010], ![2020, -9879, -29863, 90983, -80234], ![176984, 170712, -282616, -67525, 193220], ![-58808, -38672, 134562, -117606, 61625]]]
  hmulB := by decide  
  f := ![![![-47669, 28221, -1258, 4427, -8668]], ![![34672, -22737, 4434, -2702, 9226]], ![![-18452, 7625, 4941, 2523, 1120]], ![![-22945, 11054, 3530, 2746, -758]], ![![3173, -4402, 4127, 302, 3929]]]
  g := ![![![-3318, -6944, 576, -2921, 8258], ![11398, 6985, 16344, -26408, -1010], ![6527, 53116, -43989, 90983, -80234], ![-77971, -162663, 12974, -67525, 193220], ![14587, -29856, 63055, -117606, 61625]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [75, 70, 87, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [77, 77, 1], [98, 53, 130], [0, 1]]
 g := ![![[116, 111, 27], [28, 79, 45], [57, 44], [14, 112], [74, 107], [44, 1], []], ![[116, 81, 19, 38], [128, 128, 122, 89], [22, 81], [9, 16], [66, 62], [112, 58], [67, 1]], ![[103, 61, 11, 115], [57, 62, 106, 10], [107, 28], [65, 12], [52, 65], [11, 34], [69, 1]]]
 h' := ![![[77, 77, 1], [127, 3, 17], [40, 47, 62], [56, 62, 100], [53, 52, 51], [106, 120, 32], [0, 0, 1], [0, 1]], ![[98, 53, 130], [6, 30, 118], [102, 81, 58], [124, 124, 122], [119, 126, 4], [22, 23, 113], [118, 19, 53], [77, 77, 1]], ![[0, 1], [127, 98, 127], [83, 3, 11], [95, 76, 40], [75, 84, 76], [62, 119, 117], [106, 112, 77], [98, 53, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 105], []]
 b := ![[], [79, 23, 26], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [75, 70, 87, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![350531, 313747, -625186, 89967, 193922]
  a := ![-1, 0, 2, -8, 11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-143160, -199494, -83506, 89967, 193922]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 2248091 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47669, -28221, 1258, -4427, 8668]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![47669, -28221, 1258, -4427, 8668]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![55, 53, 1, 0, 0], ![98, 101, 0, 1, 0], ![15, 100, 0, 0, 1]] where
  M :=![![![47669, -28221, 1258, -4427, 8668], ![-34672, 22737, -4434, 2702, -9226], ![18452, -7625, -4941, -2523, -1120], ![19576, -6016, -8768, -3209, -4076], ![20800, -7494, -7526, -3144, -2851]]]
  hmulB := by decide  
  f := ![![![-7521, -7261, 11996, 2921, -8258]], ![![33032, 26833, -64070, 26408, 1010]], ![![10191, 7883, -20657, 11216, -2446]], ![![18490, 13953, -38266, 23061, -6874]], ![![24803, 19947, -48562, 21391, -645]]]
  g := ![![![2155, -3928, 1258, -4427, 8668], ![632, 6927, -4434, 2702, -9226], ![4231, 4741, -4941, -2523, -1120], ![6698, 9087, -8768, -3209, -4076], ![5997, 7588, -7526, -3144, -2851]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P1 : CertificateIrreducibleZModOfList' 131 2 2 7 [110, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [116, 130], [0, 1]]
 g := ![![[18, 81], [75, 91], [36], [20], [123], [94], [1]], ![[113, 50], [20, 40], [36], [20], [123], [94], [1]]]
 h' := ![![[116, 130], [3, 9], [3, 109], [66, 125], [68, 85], [57, 56], [21, 116], [0, 1]], ![[0, 1], [130, 122], [71, 22], [25, 6], [103, 46], [3, 75], [115, 15], [116, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [61, 78]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N1 : CertifiedPrimeIdeal' SI131N1 131 where
  n := 2
  hpos := by decide
  P := [110, 15, 1]
  hirr := P131P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16076, -12477, 26106, 2792, -6986]
  a := ![3, 10, 7, -15, 35]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-12372, -7477, 26106, 2792, -6986]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N1 B_one_repr
lemma NI131N1 : Nat.card (O ⧸ I131N1) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![7521, 7261, -11996, -2921, 8258]] ![![47669, -28221, 1258, -4427, 8668]]
  ![![131, 0, 0, 0, 0]] where
 M := ![![![-131, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 26, -112, 73, -20]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![41, 26, -112, 73, -20]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![122, 130, 1, 0, 0], ![32, 81, 0, 1, 0], ![96, 39, 0, 0, 1]] where
  M :=![![![41, 26, -112, 73, -20], ![80, 115, -68, -350, 398], ![-796, -742, 1309, 83, -652], ![1264, 934, -2664, 1727, -602], ![796, 816, -1156, -671, 1193]]]
  hmulB := by decide  
  f := ![![![13305, -8372, 1152, -1117, 3082]], ![![-12328, 6059, 1748, 1456, -538]], ![![158, -1730, 2717, 391, 2262]], ![![-4192, 1601, 1356, 609, 444]], ![![5812, -4169, 1352, -361, 2045]]]
  g := ![![![97, 69, -112, 73, -20], ![-136, 159, -68, -350, 398], ![-734, -1111, 1309, 83, -652], ![2400, 1685, -2664, 1727, -602], ![356, 1160, -1156, -671, 1193]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [8, 37, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [100, 136], [0, 1]]
 g := ![![[56, 120], [101], [11], [86, 128], [122], [136], [1]], ![[0, 17], [101], [11], [8, 9], [122], [136], [1]]]
 h' := ![![[100, 136], [90, 95], [58, 85], [134, 55], [98, 26], [72, 81], [129, 100], [0, 1]], ![[0, 1], [0, 42], [64, 52], [17, 82], [95, 111], [89, 56], [128, 37], [100, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [79]]
 b := ![[], [80, 108]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [8, 37, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2266, -1719, 3792, 221, -792]
  a := ![1, 4, 2, -6, 13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2890, -3516, 3792, 221, -792]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-71, -56, 134, -78, 24]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![-71, -56, 134, -78, 24]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![93, 2, 1, 0, 0], ![88, 43, 0, 1, 0], ![112, 92, 0, 0, 1]] where
  M :=![![![-71, -56, 134, -78, 24], ![-96, -141, 32, 400, -420], ![840, 788, -1401, -158, 780], ![-1512, -1148, 3112, -1833, 516], ![-816, -852, 1160, 818, -1349]]]
  hmulB := by decide  
  f := ![![![3665, -584, -2554, -738, -1512]], ![![6048, 2659, -10240, -2120, -7452]], ![![2685, -334, -2027, -564, -1236]], ![![4432, 501, -5096, -1193, -3480]], ![![7216, 1344, -9176, -2074, -6389]]]
  g := ![![![-61, 6, 134, -78, 24], ![64, 155, 32, 400, -420], ![421, -448, -1401, -158, 780], ![-1368, 175, 3112, -1833, 516], ![-216, 626, 1160, 818, -1349]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P1 : CertificateIrreducibleZModOfList' 137 2 2 7 [4, 131, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 136], [0, 1]]
 g := ![![[67, 103], [34], [101], [88, 73], [2], [36], [1]], ![[0, 34], [34], [101], [115, 64], [2], [36], [1]]]
 h' := ![![[6, 136], [134, 69], [63, 87], [59, 85], [73, 22], [9, 31], [133, 6], [0, 1]], ![[0, 1], [0, 68], [37, 50], [21, 52], [68, 115], [58, 106], [32, 131], [6, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [82]]
 b := ![[], [14, 41]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N1 : CertifiedPrimeIdeal' SI137N1 137 where
  n := 2
  hpos := by decide
  P := [4, 131, 1]
  hirr := P137P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![216, -436, 362, 590, -1024]
  a := ![4, -1, -1, 3, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![214, 494, 362, 590, -1024]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N1 B_one_repr
lemma NI137N1 : Nat.card (O ⧸ I137N1) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N1

def I137N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11, -7, 16, -3, -4]] i)))

def SI137N2: IdealEqSpanCertificate' Table ![![-11, -7, 16, -3, -4]] 
 ![![137, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![87, 0, 1, 0, 0], ![108, 0, 0, 1, 0], ![81, 0, 0, 0, 1]] where
  M :=![![![-11, -7, 16, -3, -4], ![16, 7, -38, 42, -26], ![52, 57, -71, -67, 100], ![-208, -180, 376, -75, -88], ![-16, -30, -10, 126, -125]]]
  hmulB := by decide  
  f := ![![![7821, 1923, -10842, -2389, -7642]], ![![794, 195, -1098, -242, -774]], ![![5399, 1328, -7479, -1648, -5272]], ![![6892, 1696, -9544, -2103, -6728]], ![![5261, 1295, -7284, -1605, -5135]]]
  g := ![![![-5, -7, 16, -3, -4], ![6, 7, -38, 42, -26], ![35, 57, -71, -67, 100], ![-116, -180, 376, -75, -88], ![-17, -30, -10, 126, -125]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N2 : Nat.card (O ⧸ I137N2) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N2)

lemma isPrimeI137N2 : Ideal.IsPrime I137N2 := prime_ideal_of_norm_prime hp137.out _ NI137N2
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![41, 26, -112, 73, -20]] ![![-71, -56, 134, -78, 24]]
  ![![-193543, -160982, 367214, -125271, -32648]] where
 M := ![![![-193543, -160982, 367214, -125271, -32648]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI137N1 : IdealMulLeCertificate' Table 
  ![![-193543, -160982, 367214, -125271, -32648]] ![![-11, -7, 16, -3, -4]]
  ![![137, 0, 0, 0, 0]] where
 M := ![![![45227125, 44687345, -69826982, -25502276, 56785952]]]
 hmul := by decide  
 g := ![![![![330125, 326185, -509686, -186148, 414496]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N1, I137N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
    exact isPrimeI137N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0 ⊙ MulI137N1)
instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-248611, -61591, 341138, 75174, 240756]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![-248611, -61591, 341138, 75174, 240756]] 
 ![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![0, 0, 139, 0, 0], ![0, 0, 0, 139, 0], ![77, 33, 4, 49, 1]] where
  M :=![![![-248611, -61591, 341138, 75174, 240756], ![-963024, -238637, 1321354, 291172, 932556], ![-1865112, -462219, 2559031, 563904, 1806072], ![-3130632, -775890, 4295320, 946505, 3031506], ![-2743540, -679970, 3764198, 829465, 2656657]]]
  hmulB := by decide  
  f := ![![![1175, -709, 52, -106, 228]], ![![-912, 559, -50, 88, -180]], ![![360, -213, 19, -48, 84]], ![![288, -222, 64, -19, 30]], ![![549, -346, 40, -46, 97]]]
  g := ![![![-135157, -57601, -4474, -84330, 240756], ![-523524, -223115, -17330, -326648, 932556], ![-1013904, -432105, -33563, -632616, 1806072], ![-1701846, -725292, -56336, -1061851, 3031506], ![-1491411, -635609, -49370, -930552, 2656657]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 4 2 7 [11, 46, 21, 49, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [65, 125, 2, 134], [97, 117, 125, 124], [67, 35, 12, 20], [0, 1]]
 g := ![![[32, 39, 4, 36], [17, 91, 76, 107], [32, 28, 136], [104, 128, 57, 113], [107, 57, 38], [1], []], ![[57, 7, 76, 102, 11, 17], [26, 4, 38, 132, 3, 93], [114, 86, 118], [77, 105, 35, 129, 28, 62], [84, 73, 9], [41, 115, 42], [20, 6, 25]], ![[128, 49, 51, 32, 111, 67], [126, 2, 2, 35, 112, 57], [41, 13, 9], [120, 3, 113, 110, 42, 52], [137, 125, 54], [112, 20, 5], [86, 98, 86]], ![[80, 30, 47, 57, 132, 91], [51, 65, 51, 124, 42, 57], [45, 7, 122], [71, 76, 9, 92, 17, 63], [58, 50, 64], [58, 7, 106], [114, 62, 122]]]
 h' := ![![[65, 125, 2, 134], [91, 136, 101, 6], [116, 38, 6, 61], [107, 2, 98, 54], [56, 50, 71, 104], [128, 93, 118, 90], [0, 0, 1], [0, 1]], ![[97, 117, 125, 124], [136, 6, 130, 91], [61, 114, 123, 68], [131, 23, 86, 102], [78, 45, 33, 40], [86, 8, 132, 3], [113, 113, 41, 96], [65, 125, 2, 134]], ![[67, 35, 12, 20], [72, 2, 130, 33], [12, 49, 52, 21], [18, 50, 122, 3], [31, 118, 41, 16], [136, 114, 20, 38], [123, 11, 99, 127], [97, 117, 125, 124]], ![[0, 1], [75, 134, 56, 9], [61, 77, 97, 128], [0, 64, 111, 119], [7, 65, 133, 118], [111, 63, 8, 8], [38, 15, 137, 55], [67, 35, 12, 20]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [112, 14, 115], []]
 b := ![[], [], [26, 79, 76, 54], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 4
  hpos := by decide
  P := [11, 46, 21, 49, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![110230103022, 226119809018, -163743643284, -203883582428, 544259826265]
  a := ![7, -46, -24, 25, -119]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-300703428197, -127586003293, -16840165096, -193328165967, 544259826265]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 373301041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1175, 709, -52, 106, -228]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![-1175, 709, -52, 106, -228]] 
 ![![139, 0, 0, 0, 0], ![121, 1, 0, 0, 0], ![116, 0, 1, 0, 0], ![80, 0, 0, 1, 0], ![41, 0, 0, 0, 1]] where
  M :=![![![-1175, 709, -52, 106, -228], ![912, -559, 50, -88, 180], ![-360, 213, -19, 48, -84], ![-288, 222, -64, 19, -30], ![-380, 218, 6, 13, -61]]]
  hmulB := by decide  
  f := ![![![248611, 61591, -341138, -75174, -240756]], ![![223345, 55332, -306468, -67534, -216288]], ![![220892, 54725, -303101, -66792, -213912]], ![![165608, 41030, -227240, -50075, -160374]], ![![93069, 23059, -127704, -28141, -90127]]]
  g := ![![![-576, 709, -52, 106, -228], ![449, -559, 50, -88, 180], ![-175, 213, -19, 48, -84], ![-144, 222, -64, 19, -30], ![-187, 218, 6, 13, -61]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![-248611, -61591, 341138, 75174, 240756]] ![![-1175, 709, -52, 106, -228]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-15, 1, 18, -1, 22]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![-15, 1, 18, -1, 22]] 
 ![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![0, 0, 149, 0, 0], ![105, 80, 57, 1, 0], ![126, 24, 105, 0, 1]] where
  M :=![![![-15, 1, 18, -1, 22], ![-88, -43, 134, 16, 38], ![-76, 1, 71, 99, 86], ![-128, 32, 192, -79, 364], ![-256, -112, 394, -2, 151]]]
  hmulB := by decide  
  f := ![![![797, 899, -124, 25, -332]], ![![1328, 1387, -194, 34, -514]], ![![1028, 1115, -155, 29, -412]], ![![1669, 1806, -251, 47, -668]], ![![1610, 1767, -245, 47, -653]]]
  g := ![![![-18, -3, -15, -1, 22], ![-44, -15, -32, 16, 38], ![-143, -67, -98, 99, 86], ![-253, -16, -225, -79, 364], ![-128, -24, -103, -2, 151]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [110, 46, 37, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [62, 132, 4], [50, 16, 145], [0, 1]]
 g := ![![[78, 28, 7], [132, 68], [84, 20, 61], [86, 95], [25, 134, 26], [112, 1], []], ![[4, 13, 9, 116], [64, 102], [109, 83, 32, 102], [110, 36], [64, 58, 116, 86], [115, 107], [17, 16]], ![[71, 67, 65, 30], [134, 124], [80, 85, 83, 114], [4, 142], [106, 69, 23, 104], [24, 140], [25, 16]]]
 h' := ![![[62, 132, 4], [86, 105, 56], [147, 50, 98], [81, 100, 106], [81, 27, 86], [47, 102, 131], [0, 0, 1], [0, 1]], ![[50, 16, 145], [26, 55, 124], [19, 135, 129], [71, 80, 10], [20, 4, 143], [43, 16, 120], [37, 118, 16], [62, 132, 4]], ![[0, 1], [127, 138, 118], [50, 113, 71], [37, 118, 33], [46, 118, 69], [111, 31, 47], [48, 31, 132], [50, 16, 145]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [63, 148], []]
 b := ![[], [6, 125, 112], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [110, 46, 37, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-756850, -1362102, 3840856, -6891342, 1238946]
  a := ![1, -12, -7, 9, -36]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3803536, 3491346, 1788980, -6891342, 1238946]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 3307949 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-851, 512, -36, 77, -166]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![-851, 512, -36, 77, -166]] 
 ![![149, 0, 0, 0, 0], ![76, 1, 0, 0, 0], ![92, 0, 1, 0, 0], ![42, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![-851, 512, -36, 77, -166], ![664, -401, 28, -60, 130], ![-260, 156, -11, 23, -50], ![-232, 138, -8, 21, -46], ![-268, 162, -12, 25, -53]]]
  hmulB := by decide  
  f := ![![![81, -18, -172, -41, -100]], ![![44, -9, -92, -22, -54]], ![![56, -10, -115, -27, -68]], ![![34, -2, -64, -15, -38]], ![![11, 2, -16, -4, -11]]]
  g := ![![![-263, 512, -36, 77, -166], ![206, -401, 28, -60, 130], ![-80, 156, -11, 23, -50], ![-72, 138, -8, 21, -46], ![-83, 162, -12, 25, -53]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1

def I149N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 1, -2, 0, 0]] i)))

def SI149N2: IdealEqSpanCertificate' Table ![![1, 1, -2, 0, 0]] 
 ![![149, 0, 0, 0, 0], ![108, 1, 0, 0, 0], ![128, 0, 1, 0, 0], ![37, 0, 0, 1, 0], ![105, 0, 0, 0, 1]] where
  M :=![![![1, 1, -2, 0, 0], ![0, -1, 2, -4, 0], ![0, -3, -1, 6, -12], ![24, 18, -40, 1, 6], ![4, 2, -2, -13, 5]]]
  hmulB := by decide  
  f := ![![![533, 989, -128, 44, -360]], ![![396, 725, -94, 32, -264]], ![![464, 857, -111, 38, -312]], ![![133, 247, -32, 11, -90]], ![![373, 695, -90, 31, -253]]]
  g := ![![![1, 1, -2, 0, 0], ![0, -1, 2, -4, 0], ![10, -3, -1, 6, -12], ![17, 18, -40, 1, 6], ![0, 2, -2, -13, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N2 : Nat.card (O ⧸ I149N2) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N2)

lemma isPrimeI149N2 : Ideal.IsPrime I149N2 := prime_ideal_of_norm_prime hp149.out _ NI149N2
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![-15, 1, 18, -1, 22]] ![![-851, 512, -36, 77, -166]]
  ![![3085, -1847, 114, -272, 600]] where
 M := ![![![3085, -1847, 114, -272, 600]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI149N1 : IdealMulLeCertificate' Table 
  ![![3085, -1847, 114, -272, 600]] ![![1, 1, -2, 0, 0]]
  ![![149, 0, 0, 0, 0]] where
 M := ![![![-1043, 894, -298, 0, 0]]]
 hmul := by decide  
 g := ![![![![-7, 6, -2, 0, 0]]]]
 hle2 := by decide  


def PBC149 : ContainsPrimesAboveP 149 ![I149N0, I149N1, I149N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
    exact isPrimeI149N1
    exact isPrimeI149N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 149 (by decide) (𝕀 ⊙ MulI149N0 ⊙ MulI149N1)
instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1381, -263, -6, -85, 68]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![1381, -263, -6, -85, 68]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![0, 0, 151, 0, 0], ![0, 0, 0, 151, 0], ![138, 25, 31, 112, 1]] where
  M :=![![![1381, -263, -6, -85, 68], ![-272, 1069, -118, 90, -374], ![748, 269, -53, -21, -104], ![344, -104, 16, -25, 20], ![192, -346, 30, -28, 113]]]
  hmulB := by decide  
  f := ![![![3, 1, -4, -1, -2]], ![![8, 1, -10, -4, -10]], ![![20, 5, -29, -1, -22]], ![![40, 16, -56, -15, -20]], ![![38, 14, -53, -13, -23]]]
  g := ![![![-53, -13, -14, -51, 68], ![340, 69, 76, 278, -374], ![100, 19, 21, 77, -104], ![-16, -4, -4, -15, 20], ![-102, -21, -23, -84, 113]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 4 2 7 [60, 31, 86, 32, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 10, 29, 107], [116, 57, 96, 59], [131, 83, 26, 136], [0, 1]]
 g := ![![[133, 85, 130, 20], [45, 31, 91, 105], [54, 31, 33, 85], [59, 111, 40], [71, 108, 67, 118], [1], []], ![[47, 88, 93, 135, 29, 122], [24, 40, 43, 14, 90, 61], [15, 129, 101, 138, 75, 63], [133, 55, 47], [51, 107, 40, 139, 80, 142], [0, 39, 110], [127, 124, 124]], ![[114, 101, 93, 51, 27, 125], [31, 53, 54, 139, 41, 88], [64, 8, 99, 83, 135, 19], [71, 29, 78], [45, 78, 101, 115, 111, 64], [59, 53, 17], [96, 49, 8]], ![[78, 54, 18, 5, 130, 17], [143, 56, 70, 144, 100, 121], [70, 0, 117, 73, 47, 11], [101, 58, 40], [89, 147, 75, 118, 61, 55], [92, 145, 136], [146, 23, 74]]]
 h' := ![![[23, 10, 29, 107], [18, 147, 79, 110], [82, 124, 29, 135], [51, 48, 70, 38], [119, 53, 61, 77], [91, 120, 65, 119], [0, 0, 1], [0, 1]], ![[116, 57, 96, 59], [45, 45, 100, 19], [71, 37, 35, 135], [11, 70, 8, 105], [21, 31, 41, 54], [36, 140, 142, 29], [6, 106, 66, 67], [23, 10, 29, 107]], ![[131, 83, 26, 136], [143, 38, 71, 86], [58, 105, 22, 137], [129, 67, 11, 92], [37, 46, 56, 94], [109, 129, 92, 64], [146, 60, 15, 35], [116, 57, 96, 59]], ![[0, 1], [81, 72, 52, 87], [42, 36, 65, 46], [135, 117, 62, 67], [2, 21, 144, 77], [72, 64, 3, 90], [96, 136, 69, 49], [131, 83, 26, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [20, 42, 88], []]
 b := ![[], [], [17, 22, 99, 106], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 4
  hpos := by decide
  P := [60, 31, 86, 32, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-283592552, -94935474, 426330258, 993110, 250465888]
  a := ![3, 9, 2, 7, 11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-230780696, -42096574, -48596770, -185769446, 250465888]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 519885601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, -1, 4, 1, 2]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![-3, -1, 4, 1, 2]] 
 ![![151, 0, 0, 0, 0], ![81, 1, 0, 0, 0], ![117, 0, 1, 0, 0], ![53, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![-3, -1, 4, 1, 2], ![-8, -1, 10, 4, 10], ![-20, -5, 29, 1, 22], ![-40, -16, 56, 15, 20], ![-24, -4, 30, 14, 25]]]
  hmulB := by decide  
  f := ![![![-1381, 263, 6, 85, -68]], ![![-739, 134, 4, 45, -34]], ![![-1075, 202, 5, 66, -52]], ![![-487, 93, 2, 30, -24]], ![![-47, 11, 0, 3, -3]]]
  g := ![![![-3, -1, 4, 1, 2], ![-9, -1, 10, 4, 10], ![-21, -5, 29, 1, 22], ![-41, -16, 56, 15, 20], ![-27, -4, 30, 14, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![1381, -263, -6, -85, 68]] ![![-3, -1, 4, 1, 2]]
  ![![151, 0, 0, 0, 0]] where
 M := ![![![-151, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC151 : ContainsPrimesAboveP 151 ![I151N0, I151N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
    exact isPrimeI151N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 151 (by decide) (𝕀 ⊙ MulI151N0)


lemma PB1321I3_primes (p : ℕ) :
  p ∈ Set.range ![107, 109, 113, 127, 131, 137, 139, 149, 151] ↔ Nat.Prime p ∧ 103 < p ∧ p ≤ 151 := by
  rw [← List.mem_ofFn']
  convert primes_range 103 151 (by omega)

def PB1321I3 : PrimesBelowBoundCertificateInterval O 103 151 1321 where
  m := 9
  g := ![2, 3, 3, 2, 2, 3, 2, 3, 2]
  P := ![107, 109, 113, 127, 131, 137, 139, 149, 151]
  hP := PB1321I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1, I109N2]
    · exact ![I113N0, I113N1, I113N2]
    · exact ![I127N0, I127N1]
    · exact ![I131N0, I131N1]
    · exact ![I137N0, I137N1, I137N2]
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1, I149N2]
    · exact ![I151N0, I151N1]
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
    · exact ![11881, 11881, 109]
    · exact ![12769, 12769, 113]
    · exact ![2048383, 16129]
    · exact ![2248091, 17161]
    · exact ![18769, 18769, 137]
    · exact ![373301041, 139]
    · exact ![3307949, 149, 149]
    · exact ![519885601, 151]
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
      exact NI109N2
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
      exact NI113N2
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
      exact NI137N2
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
      exact NI139N1
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
      exact NI149N2
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
  β := ![I107N1, I109N2, I113N2, I137N2, I139N1, I149N1, I149N2, I151N1]
  Il := ![[I107N1], [I109N2], [I113N2], [], [], [I137N2], [I139N1], [I149N1, I149N2], [I151N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
