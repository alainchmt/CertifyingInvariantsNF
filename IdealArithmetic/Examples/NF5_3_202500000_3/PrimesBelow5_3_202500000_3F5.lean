
import IdealArithmetic.Examples.NF5_3_202500000_3.RI5_3_202500000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 22, 19, -9, -28]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![5, 22, 19, -9, -28]] 
 ![![199, 0, 0, 0, 0], ![0, 199, 0, 0, 0], ![0, 0, 199, 0, 0], ![7, 120, 38, 1, 0], ![26, 117, 179, 0, 1]] where
  M :=![![![5, 22, 19, -9, -28], ![-12, 14, -21, 30, 68], ![-264, -25, -248, 238, 584], ![-774, -209, -685, 625, 1570], ![102, 57, 89, -72, -191]]]
  hmulB := by decide  
  f := ![![![-7, 6, 1, -1, -2]], ![![12, -6, 19, -10, -28]], ![![24, 23, -4, -2, -24]], ![![11, 1, 10, -6, -20]], ![![28, 18, 8, -8, -39]]]
  g := ![![![4, 22, 27, -9, -28], ![-10, -58, -67, 30, 68], ![-86, -487, -572, 238, 584], ![-231, -1301, -1535, 625, 1570], ![28, 156, 186, -72, -191]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 3 2 7 [74, 153, 54, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [35, 43, 120], [110, 155, 79], [0, 1]]
 g := ![![[56, 66, 57], [89, 151, 64], [27, 51, 100], [177, 165], [54, 79], [151, 130], [1]], ![[62, 1, 140, 108], [51, 29, 31, 147], [76, 30, 32, 152], [14, 53], [49, 64], [103, 116], [0, 191, 30, 83]], ![[40, 94, 191, 56], [77, 125, 176, 160], [97, 100, 138, 49], [7, 145], [99, 161], [94, 193], [44, 130, 152, 116]]]
 h' := ![![[35, 43, 120], [180, 148, 16], [191, 185, 191], [54, 16, 189], [139, 92, 31], [73, 70, 173], [125, 46, 145], [0, 1]], ![[110, 155, 79], [128, 62, 141], [128, 161, 65], [103, 0, 171], [187, 79, 124], [80, 67, 191], [90, 14, 135], [35, 43, 120]], ![[0, 1], [170, 188, 42], [30, 52, 142], [105, 183, 38], [15, 28, 44], [66, 62, 34], [16, 139, 118], [110, 155, 79]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44, 22], []]
 b := ![[], [106, 49, 96], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 3
  hpos := by decide
  P := [74, 153, 54, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![175913480, 49421356, 167820912, -141417532, -365705106]
  a := ![153, 6, 189, -140, -391]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![53639040, 300537802, 356798498, -141417532, -365705106]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 7880599 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, 6, 1, -1, -2]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![-7, 6, 1, -1, -2]] 
 ![![199, 0, 0, 0, 0], ![0, 199, 0, 0, 0], ![149, 123, 1, 0, 0], ![90, 172, 0, 1, 0], ![33, 72, 0, 0, 1]] where
  M :=![![![-7, 6, 1, -1, -2], ![12, -6, 19, -10, -28], ![24, 23, -4, -2, -24], ![-114, 3, -145, 89, 306], ![54, 11, 59, -38, -137]]]
  hmulB := by decide  
  f := ![![![5, 22, 19, -9, -28]], ![![-12, 14, -21, 30, 68]], ![![-5, 25, 0, 13, 24]], ![![-12, 21, -13, 25, 54]], ![![-3, 9, -4, 9, 19]]]
  g := ![![![0, 1, 1, -1, -2], ![-5, 7, 19, -10, -28], ![8, 13, -4, -2, -24], ![17, -98, -145, 89, 306], ![-4, 46, 59, -38, -137]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P1 : CertificateIrreducibleZModOfList' 199 2 2 7 [166, 139, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [60, 198], [0, 1]]
 g := ![![[38, 144], [61, 144], [105, 36], [29], [162], [14], [60, 1]], ![[121, 55], [144, 55], [76, 163], [29], [162], [14], [120, 198]]]
 h' := ![![[60, 198], [23, 12], [82, 12], [177, 6], [4, 32], [164, 19], [189, 51], [0, 1]], ![[0, 1], [146, 187], [6, 187], [139, 193], [133, 167], [110, 180], [65, 148], [60, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61]]
 b := ![[], [80, 130]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N1 : CertifiedPrimeIdeal' SI199N1 199 where
  n := 2
  hpos := by decide
  P := [166, 139, 1]
  hirr := P199P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-322400, 162374, -873301, 547649, 1333994]
  a := ![-183, -72, -226, 103, 468]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![183363, -415401, -873301, 547649, 1333994]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N1 B_one_repr
lemma NI199N1 : Nat.card (O ⧸ I199N1) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N1
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![5, 22, 19, -9, -28]] ![![-7, 6, 1, -1, -2]]
  ![![199, 0, 0, 0, 0]] where
 M := ![![![199, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC199 : ContainsPrimesAboveP 199 ![I199N0, I199N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI199N0
    exact isPrimeI199N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 199 (by decide) (𝕀 ⊙ MulI199N0)
instance hp211 : Fact (Nat.Prime 211) := {out := by norm_num}

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2105, -673, -1864, 1655, 4156]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![-2105, -673, -1864, 1655, 4156]] 
 ![![211, 0, 0, 0, 0], ![0, 211, 0, 0, 0], ![0, 0, 211, 0, 0], ![61, 89, 188, 1, 0], ![41, 202, 130, 0, 1]] where
  M :=![![![-2105, -673, -1864, 1655, 4156], ![-9708, -3123, -8652, 7672, 19268], ![-44976, -14436, -40075, 35520, 89248], ![-99018, -31860, -88108, 78169, 196318], ![6426, 2090, 5688, -5066, -12701]]]
  hmulB := by decide  
  f := ![![![-617, -421, -496, 339, 914]], ![![-1236, -877, -1052, 716, 1940]], ![![-2496, -1780, -2057, 1408, 3792]], ![![-2933, -2084, -2428, 1660, 4476]], ![![-2845, -2021, -2374, 1621, 4377]]]
  g := ![![![-1296, -4680, -4044, 1655, 4156], ![-6008, -21697, -18748, 7672, 19268], ![-27824, -100492, -86825, 35520, 89248], ![-61215, -221067, -191020, 78169, 196318], ![3963, 14306, 12366, -5066, -12701]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 3 2 7 [59, 48, 204, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [191, 31, 84], [27, 179, 127], [0, 1]]
 g := ![![[172, 128, 99], [82, 46, 56], [183, 64], [147, 78], [60, 25, 144], [93, 49], [1]], ![[177, 168, 20, 209], [35, 192, 172, 137], [152, 144], [48, 82], [167, 15, 162, 120], [208, 30], [13, 52, 33, 5]], ![[164, 140, 141, 3], [156, 20, 163, 77], [135, 16], [92, 54], [116, 20, 165, 63], [77, 208], [91, 108, 110, 206]]]
 h' := ![![[191, 31, 84], [15, 116, 164], [196, 55, 181], [77, 23, 8], [47, 131, 17], [104, 208, 199], [152, 163, 7], [0, 1]], ![[27, 179, 127], [2, 120, 65], [169, 25, 94], [203, 106, 199], [202, 160, 121], [129, 79, 132], [95, 170, 175], [191, 31, 84]], ![[0, 1], [95, 186, 193], [119, 131, 147], [158, 82, 4], [10, 131, 73], [200, 135, 91], [177, 89, 29], [27, 179, 127]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 117], []]
 b := ![[], [40, 81, 187], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 3
  hpos := by decide
  P := [59, 48, 204, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3548113, 1057399, 3401721, -2915497, -7289013]
  a := ![38, -1, 47, -37, -97]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2276033, 8212878, 7104677, -2915497, -7289013]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 9393931 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, -15, 94, -53, -166]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![47, -15, 94, -53, -166]] 
 ![![211, 0, 0, 0, 0], ![113, 1, 0, 0, 0], ![102, 0, 1, 0, 0], ![194, 0, 0, 1, 0], ![26, 0, 0, 0, 1]] where
  M :=![![![47, -15, 94, -53, -166], ![-84, 81, -286, 152, 436], ![-240, -238, 217, -68, 32], ![1458, 32, 1810, -1107, -3858], ![-678, -114, -622, 408, 1537]]]
  hmulB := by decide  
  f := ![![![8735, -5683, -10674, 6423, 18900]], ![![4657, -3024, -5680, 3417, 10056]], ![![4254, -2752, -5167, 3106, 9144]], ![![8068, -5220, -9798, 5889, 17338]], ![![1096, -714, -1342, 808, 2377]]]
  g := ![![![32, -15, 94, -53, -166], ![-99, 81, -286, 152, 436], ![80, -238, 217, -68, 32], ![608, 32, 1810, -1107, -3858], ![-206, -114, -622, 408, 1537]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1

def I211N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4793, -3387, -4018, 2737, 7400]] i)))

def SI211N2: IdealEqSpanCertificate' Table ![![-4793, -3387, -4018, 2737, 7400]] 
 ![![211, 0, 0, 0, 0], ![144, 1, 0, 0, 0], ![153, 0, 1, 0, 0], ![95, 0, 0, 1, 0], ![155, 0, 0, 0, 1]] where
  M :=![![![-4793, -3387, -4018, 2737, 7400], ![-9732, -6885, -8152, 5548, 15004], ![-19680, -13976, -16481, 11192, 30288], ![-14862, -10686, -12428, 8377, 22722], ![-6858, -4826, -5750, 3926, 10607]]]
  hmulB := by decide  
  f := ![![![-1529, -475, -1126, 801, 3238]], ![![-996, -329, -696, 504, 2068]], ![![-1275, -281, -1171, 779, 2962]], ![![-595, -363, -58, 128, 820]], ![![-1231, -263, -1156, 765, 2893]]]
  g := ![![![-1466, -3387, -4018, 2737, 7400], ![-2956, -6885, -8152, 5548, 15004], ![-5893, -13976, -16481, 11192, 30288], ![-4229, -10686, -12428, 8377, 22722], ![-2129, -4826, -5750, 3926, 10607]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N2 : Nat.card (O ⧸ I211N2) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N2)

lemma isPrimeI211N2 : Ideal.IsPrime I211N2 := prime_ideal_of_norm_prime hp211.out _ NI211N2
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![-2105, -673, -1864, 1655, 4156]] ![![47, -15, 94, -53, -166]]
  ![![179, -130, 638, -416, -864]] where
 M := ![![![179, -130, 638, -416, -864]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI211N1 : IdealMulLeCertificate' Table 
  ![![179, -130, 638, -416, -864]] ![![-4793, -3387, -4018, 2737, 7400]]
  ![![211, 0, 0, 0, 0]] where
 M := ![![![-40723, -12871, -36292, 32283, 81024]]]
 hmul := by decide  
 g := ![![![![-193, -61, -172, 153, 384]]]]
 hle2 := by decide  


def PBC211 : ContainsPrimesAboveP 211 ![I211N0, I211N1, I211N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI211N0
    exact isPrimeI211N1
    exact isPrimeI211N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 211 (by decide) (𝕀 ⊙ MulI211N0 ⊙ MulI211N1)
instance hp223 : Fact (Nat.Prime 223) := {out := by norm_num}

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![161, 11, 183, -114, -406]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![161, 11, 183, -114, -406]] 
 ![![223, 0, 0, 0, 0], ![0, 223, 0, 0, 0], ![140, 105, 1, 0, 0], ![9, 133, 0, 1, 0], ![8, 200, 0, 0, 1]] where
  M :=![![![161, 11, 183, -114, -406], ![-768, 166, -1355, 778, 2504], ![2040, -1175, 5220, -2854, -8552], ![444, 2125, -4111, 1927, 4296], ![696, -1341, 3853, -1980, -5349]]]
  hmulB := by decide  
  f := ![![![863, -1, -155, 50, 222]], ![![864, 830, 1301, -930, -2504]], ![![964, 397, 527, -416, -1064]], ![![573, 504, 789, -569, -1526]], ![![808, 745, 1161, -832, -2237]]]
  g := ![![![-95, 346, 183, -114, -406], ![726, -2071, -1355, 778, 2504], ![-2846, 6909, 5220, -2854, -8552], ![2351, -3057, -4111, 1927, 4296], ![-2144, 4158, 3853, -1980, -5349]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 2 2 7 [66, 123, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [100, 222], [0, 1]]
 g := ![![[12, 98], [78, 220], [178, 9], [175, 144], [124, 138], [166], [100, 1]], ![[0, 125], [1, 3], [186, 214], [80, 79], [98, 85], [166], [200, 222]]]
 h' := ![![[100, 222], [204, 105], [71, 144], [46, 220], [67, 12], [43, 204], [90, 122], [0, 1]], ![[0, 1], [0, 118], [199, 79], [192, 3], [152, 211], [150, 19], [25, 101], [100, 222]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47]]
 b := ![[], [163, 135]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 2
  hpos := by decide
  P := [66, 123, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-740606, -249887, -615367, 570518, 1423146]
  a := ![-259, 5, -320, 250, 662]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![308928, -1328002, -615367, 570518, 1423146]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 49729 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1673, 1735, 3048, -1873, -5438]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![-1673, 1735, 3048, -1873, -5438]] 
 ![![223, 0, 0, 0, 0], ![0, 223, 0, 0, 0], ![112, 123, 1, 0, 0], ![25, 74, 0, 1, 0], ![198, 23, 0, 0, 1]] where
  M :=![![![-1673, 1735, 3048, -1873, -5438], ![2172, -317, -988, 540, 1700], ![960, 1804, 2583, -1696, -4720], ![1122, 1266, 1796, -1223, -3346], ![-486, 1136, 1840, -1148, -3295]]]
  hmulB := by decide  
  f := ![![![-365, 607, -1808, 935, 2556]], ![![-2988, -1487, -572, 744, 4228]], ![![-1724, -519, -1077, 792, 3316]], ![![-1241, -357, -812, 588, 2430]], ![![-504, 357, -1436, 776, 2285]]]
  g := ![![![3500, -491, 3048, -1873, -5438], ![-1064, 189, -988, 540, 1700], ![3088, -367, 2583, -1696, -4720], ![2211, -234, 1796, -1223, -3346], ![2128, -289, 1840, -1148, -3295]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P1 : CertificateIrreducibleZModOfList' 223 2 2 7 [196, 109, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [114, 222], [0, 1]]
 g := ![![[29, 33], [205, 138], [192, 36], [54, 146], [12, 39], [116], [114, 1]], ![[0, 190], [104, 85], [59, 187], [196, 77], [221, 184], [116], [5, 222]]]
 h' := ![![[114, 222], [183, 16], [55, 19], [120, 6], [101, 121], [162, 40], [179, 89], [0, 1]], ![[0, 1], [0, 207], [214, 204], [135, 217], [69, 102], [39, 183], [67, 134], [114, 222]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [181]]
 b := ![[], [82, 202]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N1 : CertifiedPrimeIdeal' SI223N1 223 where
  n := 2
  hpos := by decide
  P := [196, 109, 1]
  hirr := P223P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-240768, -174377, -88000, 184481, 258886]
  a := ![385, 23, 476, -339, -984]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-207427, -40163, -88000, 184481, 258886]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N1 B_one_repr
lemma NI223N1 : Nat.card (O ⧸ I223N1) = 49729 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N1

def I223N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 0, 1, -1, -2]] i)))

def SI223N2: IdealEqSpanCertificate' Table ![![1, 0, 1, -1, -2]] 
 ![![223, 0, 0, 0, 0], ![218, 1, 0, 0, 0], ![198, 0, 1, 0, 0], ![163, 0, 0, 1, 0], ![17, 0, 0, 0, 1]] where
  M :=![![![1, 0, 1, -1, -2], ![12, 2, 13, -10, -28], ![24, 17, 4, -14, -24], ![102, 15, 125, -95, -246], ![-18, 5, -37, 22, 63]]]
  hmulB := by decide  
  f := ![![![373, -440, -765, 471, 1364]], ![![362, -430, -747, 460, 1332]], ![![330, -393, -682, 420, 1216]], ![![271, -323, -562, 346, 1002]], ![![29, -35, -60, 37, 107]]]
  g := ![![![0, 0, 1, -1, -2], ![-4, 2, 13, -10, -28], ![-8, 17, 4, -14, -24], ![-37, 15, 125, -95, -246], ![7, 5, -37, 22, 63]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N2 : Nat.card (O ⧸ I223N2) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N2)

lemma isPrimeI223N2 : Ideal.IsPrime I223N2 := prime_ideal_of_norm_prime hp223.out _ NI223N2
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![161, 11, 183, -114, -406]] ![![-1673, 1735, 3048, -1873, -5438]]
  ![![-373, 440, 765, -471, -1364]] where
 M := ![![![-373, 440, 765, -471, -1364]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI223N1 : IdealMulLeCertificate' Table 
  ![![-373, 440, 765, -471, -1364]] ![![1, 0, 1, -1, -2]]
  ![![223, 0, 0, 0, 0]] where
 M := ![![![-223, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC223 : ContainsPrimesAboveP 223 ![I223N0, I223N1, I223N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI223N0
    exact isPrimeI223N1
    exact isPrimeI223N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 223 (by decide) (𝕀 ⊙ MulI223N0 ⊙ MulI223N1)
instance hp227 : Fact (Nat.Prime 227) := {out := by norm_num}

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2431, -798, 4899, -2759, -8646]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![2431, -798, 4899, -2759, -8646]] 
 ![![227, 0, 0, 0, 0], ![0, 227, 0, 0, 0], ![0, 0, 227, 0, 0], ![0, 0, 0, 227, 0], ![26, 108, 175, 172, 1]] where
  M :=![![![2431, -798, 4899, -2759, -8646], ![-4428, 4202, -14979, 7970, 22844], ![-12792, -12503, 11056, -3358, 2232], ![76050, 1505, 94649, -57817, -201602], ![-35526, -5939, -32687, 21422, 80633]]]
  hmulB := by decide  
  f := ![![![-2641, -1830, -2163, 1477, 3988]], ![![-5316, -3770, -4487, 3058, 8268]], ![![-10872, -7651, -9092, 6202, 16760]], ![![-8418, -5919, -7047, 4811, 12998]], ![![-17608, -12398, -14745, 10060, 27185]]]
  g := ![![![1001, 4110, 6687, 6539, -8646], ![-2636, -10850, -17677, -17274, 22844], ![-312, -1117, -1672, -1706, 2232], ![23426, 95923, 155837, 152501, -201602], ![-9392, -38389, -62306, -61002, 80633]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 4 2 7 [50, 186, 147, 120, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [83, 41, 26, 12], [11, 76, 196, 107], [13, 109, 5, 108], [0, 1]]
 g := ![![[130, 211, 59, 203], [61, 174, 123, 171], [16, 19, 100], [186, 184, 49], [83, 197, 99], [60, 179, 107, 1], []], ![[17, 190, 211, 132, 132, 161], [151, 65, 135, 90, 214, 7], [225, 176, 62], [117, 56, 97], [164, 142, 53], [144, 126, 36, 106, 183, 196], [211, 169, 39, 50, 0, 139]], ![[67, 200, 80, 190, 177, 180], [31, 106, 7, 127, 79, 165], [130, 40, 21], [113, 197, 113], [160, 86, 78], [144, 74, 66, 69, 95, 54], [208, 71, 160, 134, 140, 151]], ![[144, 158, 103, 175, 72, 189], [225, 5, 123, 181, 141, 43], [210, 60, 49], [105, 80, 136], [14, 115, 10], [162, 174, 55, 16, 222, 159], [158, 155, 179, 73, 159, 89]]]
 h' := ![![[83, 41, 26, 12], [128, 158, 90, 89], [1, 64, 82, 202], [183, 63, 181, 10], [67, 102, 44, 7], [178, 93, 206, 107], [0, 0, 0, 1], [0, 1]], ![[11, 76, 196, 107], [214, 62, 104, 154], [173, 58, 11, 70], [181, 41, 224, 17], [105, 75, 224, 18], [157, 180, 210, 196], [93, 157, 81, 186], [83, 41, 26, 12]], ![[13, 109, 5, 108], [183, 52, 135, 79], [204, 149, 130, 150], [11, 134, 176, 193], [126, 96, 6, 106], [33, 36, 143, 87], [11, 105, 226, 83], [11, 76, 196, 107]], ![[0, 1], [205, 182, 125, 132], [161, 183, 4, 32], [30, 216, 100, 7], [112, 181, 180, 96], [49, 145, 122, 64], [199, 192, 147, 184], [13, 109, 5, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [12, 175, 181], []]
 b := ![[], [], [90, 204, 59, 185], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 4
  hpos := by decide
  P := [50, 186, 147, 120, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-117974098606, 63158262168, -291292627296, 159918355176, 482166724536]
  a := ![-162, -18, -200, 126, 414]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-55745854346, -229122678360, -372997662648, -364637701608, 482166724536]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 2655237841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2641, 1830, 2163, -1477, -3988]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![2641, 1830, 2163, -1477, -3988]] 
 ![![227, 0, 0, 0, 0], ![98, 1, 0, 0, 0], ![157, 0, 1, 0, 0], ![203, 0, 0, 1, 0], ![184, 0, 0, 0, 1]] where
  M :=![![![2641, 1830, 2163, -1477, -3988], ![5316, 3770, 4487, -3058, -8268], ![10872, 7651, 9092, -6202, -16760], ![8418, 5919, 7047, -4811, -12998], ![3726, 2613, 3097, -2112, -5707]]]
  hmulB := by decide  
  f := ![![![-2431, 798, -4899, 2759, 8646]], ![![-1030, 326, -2049, 1156, 3632]], ![![-1625, 607, -3437, 1923, 5970]], ![![-2509, 707, -4798, 2722, 8620]], ![![-1814, 673, -3827, 2142, 6653]]]
  g := ![![![2279, 1830, 2163, -1477, -3988], ![4729, 3770, 4487, -3058, -8268], ![9588, 7651, 9092, -6202, -16760], ![7446, 5919, 7047, -4811, -12998], ![3261, 2613, 3097, -2112, -5707]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N1 : Nat.card (O ⧸ I227N1) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N1)

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := prime_ideal_of_norm_prime hp227.out _ NI227N1
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![2431, -798, 4899, -2759, -8646]] ![![2641, 1830, 2163, -1477, -3988]]
  ![![227, 0, 0, 0, 0]] where
 M := ![![![-227, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC227 : ContainsPrimesAboveP 227 ![I227N0, I227N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI227N0
    exact isPrimeI227N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 227 (by decide) (𝕀 ⊙ MulI227N0)
instance hp229 : Fact (Nat.Prime 229) := {out := by norm_num}

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-59, 76, -101, 55, 236]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![-59, 76, -101, 55, 236]] 
 ![![229, 0, 0, 0, 0], ![0, 229, 0, 0, 0], ![0, 0, 229, 0, 0], ![0, 0, 0, 229, 0], ![57, 109, 51, 106, 1]] where
  M :=![![![-59, 76, -101, 55, 236], ![852, -34, 1377, -802, -2492], ![-1032, 1341, -3816, 2010, 5960], ![-846, -1437, 2437, -1055, -1654], ![-18, 1207, -2511, 1220, 3049]]]
  hmulB := by decide  
  f := ![![![43, 20, 51, -43, -110]], ![![228, 70, 195, -174, -436]], ![![1032, 335, 924, -818, -2056]], ![![2274, 733, 2027, -1797, -4514]], ![![1401, 452, 1249, -1107, -2781]]]
  g := ![![![-59, -112, -53, -109, 236], ![624, 1186, 561, 1150, -2492], ![-1488, -2831, -1344, -2750, 5960], ![408, 781, 379, 761, -1654], ![-759, -1446, -690, -1406, 3049]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 4 2 7 [35, 212, 111, 225, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [179, 209, 164, 23], [128, 70, 72, 123], [155, 178, 222, 83], [0, 1]]
 g := ![![[165, 153, 149, 165], [106, 37, 149], [148, 129, 207, 15], [126, 147, 75], [57, 126, 26], [109, 134, 4, 1], []], ![[174, 61, 127, 221, 142, 141], [172, 2, 210], [123, 96, 83, 162, 165, 113], [60, 222, 148], [65, 3, 20], [56, 213, 109, 85, 179, 223], [74, 124, 53, 35, 15, 30]], ![[215, 22, 62, 221, 60, 119], [5, 183, 192], [195, 12, 82, 59, 123, 119], [89, 91, 187], [75, 41, 56], [34, 203, 193, 140, 199, 197], [135, 43, 146, 49, 86, 13]], ![[27, 44, 7, 100, 129, 202], [18, 217, 58], [31, 11, 166, 138, 223, 161], [5, 53, 81], [173, 47, 71], [23, 198, 145, 19, 69, 46], [71, 152, 213, 92, 184, 203]]]
 h' := ![![[179, 209, 164, 23], [195, 3, 32, 60], [87, 5, 19, 148], [114, 27, 153, 106], [196, 79, 156, 103], [78, 140, 115, 22], [0, 0, 0, 1], [0, 1]], ![[128, 70, 72, 123], [143, 131, 81, 223], [74, 11, 42, 50], [157, 96, 90, 108], [14, 130, 113, 47], [122, 171, 48, 97], [192, 119, 93, 13], [179, 209, 164, 23]], ![[155, 178, 222, 83], [212, 37, 115, 48], [58, 116, 65, 110], [199, 47, 222, 48], [32, 102, 34, 88], [162, 104, 26, 133], [54, 18, 215, 185], [128, 70, 72, 123]], ![[0, 1], [93, 58, 1, 127], [6, 97, 103, 150], [103, 59, 222, 196], [7, 147, 155, 220], [197, 43, 40, 206], [140, 92, 150, 30], [155, 178, 222, 83]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [227, 168, 138], []]
 b := ![[], [], [124, 141, 193, 105], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 4
  hpos := by decide
  P := [35, 212, 111, 225, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3094568257148, -997175736171, -2751941978003, 2443600294886, 6132176182730]
  a := ![-163, 3, -201, 170, 418]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1539862928702, -2923163229929, -1377698372477, -2827803821286, 6132176182730]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 2750058481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-43, -20, -51, 43, 110]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![-43, -20, -51, 43, 110]] 
 ![![229, 0, 0, 0, 0], ![127, 1, 0, 0, 0], ![130, 0, 1, 0, 0], ![40, 0, 0, 1, 0], ![186, 0, 0, 0, 1]] where
  M :=![![![-43, -20, -51, 43, 110], ![-228, -70, -195, 174, 436], ![-1032, -335, -924, 818, 2056], ![-2274, -733, -2027, 1797, 4514], ![150, 45, 127, -114, -285]]]
  hmulB := by decide  
  f := ![![![59, -76, 101, -55, -236]], ![![29, -42, 50, -27, -120]], ![![38, -49, 74, -40, -160]], ![![14, -7, 7, -5, -34]], ![![48, -67, 93, -50, -205]]]
  g := ![![![-57, -20, -51, 43, 110], ![-236, -70, -195, 174, 436], ![-1107, -335, -924, 818, 2056], ![-2433, -733, -2027, 1797, 4514], ![155, 45, 127, -114, -285]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N1 : Nat.card (O ⧸ I229N1) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N1)

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := prime_ideal_of_norm_prime hp229.out _ NI229N1
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![-59, 76, -101, 55, 236]] ![![-43, -20, -51, 43, 110]]
  ![![229, 0, 0, 0, 0]] where
 M := ![![![-229, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC229 : ContainsPrimesAboveP 229 ![I229N0, I229N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI229N0
    exact isPrimeI229N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 229 (by decide) (𝕀 ⊙ MulI229N0)
instance hp233 : Fact (Nat.Prime 233) := {out := by norm_num}

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-943, -2247, -2962, 1849, 5240]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![-943, -2247, -2962, 1849, 5240]] 
 ![![233, 0, 0, 0, 0], ![0, 233, 0, 0, 0], ![0, 0, 233, 0, 0], ![48, 138, 36, 1, 0], ![229, 164, 130, 0, 1]] where
  M :=![![![-943, -2247, -2962, 1849, 5240], ![-3684, -2363, -1612, 844, 2428], ![-1248, -4556, -1495, -496, -48], ![10482, 282, 9304, -9613, -23262], ![-3978, -3086, -4502, 3230, 8649]]]
  hmulB := by decide  
  f := ![![![1027, 271, 726, -513, -2074]], ![![-6420, 705, -9828, 5776, 19172]], ![![22128, -8628, 47537, -26544, -82112]], ![![-222, -774, 1420, -655, -1402]], ![![8897, -4101, 20506, -11349, -34649]]]
  g := ![![![-5535, -4793, -3222, 1849, 5240], ![-2576, -2219, -1492, 844, 2428], ![144, 308, 97, -496, -48], ![24888, 22068, 14504, -9613, -23262], ![-9183, -8014, -5344, 3230, 8649]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 3 2 7 [122, 97, 23, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [92, 73, 178], [118, 159, 55], [0, 1]]
 g := ![![[68, 167, 109], [231, 15], [228, 2], [166, 150, 28], [79, 28], [191, 217, 63], [1]], ![[40, 155, 8, 201], [230, 201], [140, 18], [107, 56, 116, 117], [90, 113], [76, 44, 144, 131], [128, 204, 122, 220]], ![[183, 231, 208, 184], [98, 101], [89, 32], [117, 230, 70, 126], [2, 36], [44, 87, 57, 225], [113, 52, 123, 13]]]
 h' := ![![[92, 73, 178], [134, 107, 80], [39, 103, 134], [19, 119, 148], [152, 112, 93], [231, 173, 93], [111, 136, 210], [0, 1]], ![[118, 159, 55], [31, 186, 78], [36, 77, 30], [56, 231, 211], [78, 142, 6], [177, 168, 146], [230, 77, 47], [92, 73, 178]], ![[0, 1], [111, 173, 75], [157, 53, 69], [225, 116, 107], [146, 212, 134], [200, 125, 227], [110, 20, 209], [118, 159, 55]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [164, 224], []]
 b := ![[], [13, 229, 182], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 3
  hpos := by decide
  P := [122, 97, 23, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1006851, -1711693, 5070164, -2619622, -7146976]
  a := ![-47, -7, -58, 36, 120]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![7568267, 6574679, 4414092, -2619622, -7146976]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 12649337 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1027, -271, -726, 513, 2074]] i)))

def SI233N1: IdealEqSpanCertificate' Table ![![-1027, -271, -726, 513, 2074]] 
 ![![233, 0, 0, 0, 0], ![0, 233, 0, 0, 0], ![1, 161, 1, 0, 0], ![36, 205, 0, 1, 0], ![36, 110, 0, 0, 1]] where
  M :=![![![-1027, -271, -726, 513, 2074], ![6420, -705, 9828, -5776, -19172], ![-22128, 8628, -47537, 26544, 82112], ![11670, -19968, 59056, -30505, -83182], ![-14058, 11572, -43626, 23384, 67919]]]
  hmulB := by decide  
  f := ![![![943, 2247, 2962, -1849, -5240]], ![![3684, 2363, 1612, -844, -2428]], ![![2555, 1662, 1133, -589, -1700]], ![![3342, 2425, 1836, -987, -2846]], ![![1902, 1476, 1238, -698, -1993]]]
  g := ![![![-401, -930, -726, 513, 2074], ![3840, 7339, 9828, -5776, -19172], ![-16679, -29235, -47537, 26544, 82112], ![17362, 25217, 59056, -30505, -83182], ![-13980, -22444, -43626, 23384, 67919]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P1 : CertificateIrreducibleZModOfList' 233 2 2 7 [79, 71, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [162, 232], [0, 1]]
 g := ![![[228, 120], [120], [144], [161, 31], [135], [68, 101], [162, 1]], ![[96, 113], [120], [144], [57, 202], [135], [120, 132], [91, 232]]]
 h' := ![![[162, 232], [81, 54], [170, 54], [96, 221], [222, 168], [220, 64], [17, 69], [0, 1]], ![[0, 1], [208, 179], [64, 179], [16, 12], [177, 65], [103, 169], [11, 164], [162, 232]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [172]]
 b := ![[], [24, 86]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N1 : CertifiedPrimeIdeal' SI233N1 233 where
  n := 2
  hpos := by decide
  P := [79, 71, 1]
  hirr := P233P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-148397, -59361, -111804, 113805, 265208]
  a := ![-165, -7, -203, 151, 422]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-58717, -148334, -111804, 113805, 265208]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N1 B_one_repr
lemma NI233N1 : Nat.card (O ⧸ I233N1) = 54289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N1
def MulI233N0 : IdealMulLeCertificate' Table 
  ![![-943, -2247, -2962, 1849, 5240]] ![![-1027, -271, -726, 513, 2074]]
  ![![233, 0, 0, 0, 0]] where
 M := ![![![-233, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC233 : ContainsPrimesAboveP 233 ![I233N0, I233N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI233N0
    exact isPrimeI233N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 233 (by decide) (𝕀 ⊙ MulI233N0)
instance hp239 : Fact (Nat.Prime 239) := {out := by norm_num}

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-15059, -10625, -12619, 8602, 23252]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![-15059, -10625, -12619, 8602, 23252]] 
 ![![239, 0, 0, 0, 0], ![0, 239, 0, 0, 0], ![0, 0, 239, 0, 0], ![228, 146, 158, 1, 0], ![62, 65, 175, 0, 1]] where
  M :=![![![-15059, -10625, -12619, 8602, 23252], ![-30648, -21630, -25683, 17506, 47320], ![-62376, -44023, -52280, 35626, 96312], ![-48072, -33983, -40259, 27423, 74144], ![-21408, -15091, -17953, 12238, 33081]]]
  hmulB := by decide  
  f := ![![![-133, 95, 167, -102, -300]], ![![72, -62, -115, 70, 216]], ![![72, 33, 244, -150, -472]], ![![-36, 75, 249, -153, -464]], ![![38, 32, 192, -118, -367]]]
  g := ![![![-14301, -11623, -22765, 8602, 23252], ![-29104, -23654, -46329, 17506, 47320], ![-59232, -48141, -94292, 35626, 96312], ![-45596, -37059, -72587, 27423, 74144], ![-20346, -16536, -32388, 12238, 33081]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 3 2 7 [41, 155, 205, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [226, 87, 124], [47, 151, 115], [0, 1]]
 g := ![![[216, 35, 1], [33, 115, 124], [213, 231, 10], [219, 81, 180], [151, 204], [24, 84, 200], [1]], ![[166, 147, 47, 174], [85, 163, 178, 72], [167, 230, 57, 45], [173, 94, 36, 27], [229, 153], [161, 149, 115, 176], [13, 34, 138, 121]], ![[187, 72, 74, 175], [126, 54, 228, 238], [212, 219, 90, 59], [42, 138, 6, 97], [174, 4], [82, 172, 179, 70], [210, 113, 100, 118]]]
 h' := ![![[226, 87, 124], [81, 119, 238], [110, 149, 210], [103, 231, 201], [90, 190, 186], [211, 14, 193], [198, 84, 34], [0, 1]], ![[47, 151, 115], [22, 78, 26], [217, 115, 235], [108, 97, 201], [4, 145, 22], [123, 115, 48], [138, 70, 15], [226, 87, 124]], ![[0, 1], [233, 42, 214], [133, 214, 33], [182, 150, 76], [38, 143, 31], [99, 110, 237], [91, 85, 190], [47, 151, 115]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 149], []]
 b := ![[], [157, 237, 20], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 3
  hpos := by decide
  P := [41, 155, 205, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-469708614, -138716899, -428007980, 364787914, 956994016]
  a := ![-241, -13, -298, 214, 616]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-598221682, -483691897, -943675528, 364787914, 956994016]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N0 B_one_repr
lemma NI239N0 : Nat.card (O ⧸ I239N0) = 13651919 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N0

def I239N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![133, -95, -167, 102, 300]] i)))

def SI239N1: IdealEqSpanCertificate' Table ![![133, -95, -167, 102, 300]] 
 ![![239, 0, 0, 0, 0], ![0, 239, 0, 0, 0], ![126, 162, 1, 0, 0], ![71, 206, 0, 1, 0], ![9, 121, 0, 0, 1]] where
  M :=![![![133, -95, -167, 102, 300], ![-72, 62, 115, -70, -216], ![-72, -33, -244, 150, 472], ![168, -103, 327, -169, -544], ![-48, -13, -309, 178, 553]]]
  hmulB := by decide  
  f := ![![![15059, 10625, 12619, -8602, -23252]], ![![30648, 21630, 25683, -17506, -47320]], ![![28974, 20447, 24280, -16550, -44736]], ![![31091, 21942, 26054, -17759, -48004]], ![![16173, 11414, 13553, -9238, -24971]]]
  g := ![![![47, -127, -167, 102, 300], ![-32, 92, 115, -70, -216], ![66, -203, -244, 150, 472], ![-101, 199, 327, -169, -544], ![89, -224, -309, 178, 553]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P1 : CertificateIrreducibleZModOfList' 239 2 2 7 [109, 180, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [59, 238], [0, 1]]
 g := ![![[17, 182], [58, 157], [21, 232], [7, 225], [36], [159, 198], [59, 1]], ![[0, 57], [0, 82], [86, 7], [137, 14], [36], [130, 41], [118, 238]]]
 h' := ![![[59, 238], [131, 95], [101, 55], [193, 94], [211, 15], [116, 233], [22, 26], [0, 1]], ![[0, 1], [0, 144], [0, 184], [3, 145], [140, 224], [1, 6], [122, 213], [59, 238]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [108]]
 b := ![[], [80, 54]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N1 : CertifiedPrimeIdeal' SI239N1 239 where
  n := 2
  hpos := by decide
  P := [109, 180, 1]
  hirr := P239P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-163396, -52475, -139613, 128301, 319817]
  a := ![-127, -3, -157, 121, 325]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![22762, -178088, -139613, 128301, 319817]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N1 : Ideal.IsPrime I239N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N1 B_one_repr
lemma NI239N1 : Nat.card (O ⧸ I239N1) = 57121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N1
def MulI239N0 : IdealMulLeCertificate' Table 
  ![![-15059, -10625, -12619, 8602, 23252]] ![![133, -95, -167, 102, 300]]
  ![![239, 0, 0, 0, 0]] where
 M := ![![![-239, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC239 : ContainsPrimesAboveP 239 ![I239N0, I239N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI239N0
    exact isPrimeI239N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 239 (by decide) (𝕀 ⊙ MulI239N0)
instance hp241 : Fact (Nat.Prime 241) := {out := by norm_num}

def I241N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, -74, 393, -219, -676]] i)))

def SI241N0: IdealEqSpanCertificate' Table ![![181, -74, 393, -219, -676]] 
 ![![241, 0, 0, 0, 0], ![0, 241, 0, 0, 0], ![0, 0, 241, 0, 0], ![42, 195, 38, 1, 0], ![97, 102, 88, 0, 1]] where
  M :=![![![181, -74, 393, -219, -676], ![-228, 336, -1035, 538, 1484], ![-1560, -855, -130, 306, 2008], ![6654, -315, 9269, -5543, -18794], ![-3294, -241, -3717, 2320, 8281]]]
  hmulB := by decide  
  f := ![![![31, -102, -155, 95, 274]], ![![-132, -40, 7, -10, -28]], ![![24, -133, -38, -26, -24]], ![![-96, -71, -26, 3, 18]], ![![-35, -107, -74, 25, 91]]]
  g := ![![![311, 463, 283, -219, -676], ![-692, -1062, -631, 538, 1484], ![-868, -1101, -782, 306, 2008], ![8558, 12438, 7775, -5543, -18794], ![-3751, -5383, -3405, 2320, 8281]]]
  hle1 := by decide   
  hle2 := by decide  


def P241P0 : CertificateIrreducibleZModOfList' 241 3 2 7 [12, 144, 80, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [56, 165, 63], [105, 75, 178], [0, 1]]
 g := ![![[156, 76, 159], [23, 238], [51, 67], [88, 50], [174, 28, 6], [76, 29, 134], [1]], ![[98, 101, 208, 190], [172, 3], [172, 180], [205, 141], [97, 158, 27, 110], [228, 148, 223, 203], [125, 113, 227, 130]], ![[101, 3, 201, 52], [58, 98], [99, 53], [224, 135], [112, 79, 209, 124], [18, 100, 212, 189], [122, 229, 157, 111]]]
 h' := ![![[56, 165, 63], [37, 138, 221], [109, 124, 210], [203, 18, 157], [81, 207, 110], [52, 179, 27], [229, 97, 161], [0, 1]], ![[105, 75, 178], [52, 82, 205], [195, 91, 185], [50, 128, 136], [231, 120, 83], [112, 203, 47], [114, 204, 111], [56, 165, 63]], ![[0, 1], [15, 21, 56], [179, 26, 87], [43, 95, 189], [171, 155, 48], [71, 100, 167], [84, 181, 210], [105, 75, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [172, 77], []]
 b := ![[], [131, 156, 213], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 3
  hpos := by decide
  P := [12, 144, 80, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![621349, -8834719, 20300728, -9955609, -24545364]
  a := ![-85, -9, -108, 65, 218]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![11616835, 18407204, 10616622, -9955609, -24545364]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI241N0 : Ideal.IsPrime I241N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI241N0 B_one_repr
lemma NI241N0 : Nat.card (O ⧸ I241N0) = 13997521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI241N0

def I241N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-325, -230, -271, 185, 500]] i)))

def SI241N1: IdealEqSpanCertificate' Table ![![-325, -230, -271, 185, 500]] 
 ![![241, 0, 0, 0, 0], ![190, 1, 0, 0, 0], ![50, 0, 1, 0, 0], ![216, 0, 0, 1, 0], ![99, 0, 0, 0, 1]] where
  M :=![![![-325, -230, -271, 185, 500], ![-660, -466, -555, 378, 1020], ![-1368, -951, -1156, 786, 2136], ![-1002, -747, -795, 551, 1470], ![-486, -321, -429, 288, 791]]]
  hmulB := by decide  
  f := ![![![-655, 1046, 2125, -1433, -4010]], ![![-502, 826, 1681, -1136, -3176]], ![![-86, 235, 490, -340, -940]], ![![-474, 975, 2007, -1375, -3822]], ![![-279, 429, 870, -585, -1639]]]
  g := ![![![-135, -230, -271, 185, 500], ![-278, -466, -555, 378, 1020], ![-598, -951, -1156, 786, 2136], ![-348, -747, -795, 551, 1470], ![-243, -321, -429, 288, 791]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI241N1 : Nat.card (O ⧸ I241N1) = 241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI241N1)

lemma isPrimeI241N1 : Ideal.IsPrime I241N1 := prime_ideal_of_norm_prime hp241.out _ NI241N1

def I241N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, 1, -12, 7, 22]] i)))

def SI241N2: IdealEqSpanCertificate' Table ![![-7, 1, -12, 7, 22]] 
 ![![241, 0, 0, 0, 0], ![216, 1, 0, 0, 0], ![98, 0, 1, 0, 0], ![153, 0, 0, 1, 0], ![148, 0, 0, 0, 1]] where
  M :=![![![-7, 1, -12, 7, 22], ![12, -11, 38, -20, -60], ![0, 30, -71, 36, 80], ![-174, -26, -174, 115, 406], ![66, 22, 36, -28, -121]]]
  hmulB := by decide  
  f := ![![![3587, -2661, -4920, 2989, 8748]], ![![3204, -2379, -4398, 2672, 7820]], ![![1462, -1088, -2011, 1222, 3576]], ![![2277, -1693, -3130, 1902, 5566]], ![![2210, -1640, -3032, 1842, 5391]]]
  g := ![![![-14, 1, -12, 7, 22], ![44, -11, 38, -20, -60], ![-70, 30, -71, 36, 80], ![-229, -26, -174, 115, 406], ![58, 22, 36, -28, -121]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI241N2 : Nat.card (O ⧸ I241N2) = 241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI241N2)

lemma isPrimeI241N2 : Ideal.IsPrime I241N2 := prime_ideal_of_norm_prime hp241.out _ NI241N2
def MulI241N0 : IdealMulLeCertificate' Table 
  ![![181, -74, 393, -219, -676]] ![![-325, -230, -271, 185, 500]]
  ![![365, -300, 1820, -946, -2178]] where
 M := ![![![365, -300, 1820, -946, -2178]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI241N1 : IdealMulLeCertificate' Table 
  ![![365, -300, 1820, -946, -2178]] ![![-7, 1, -12, 7, 22]]
  ![![241, 0, 0, 0, 0]] where
 M := ![![![14701, 34945, -58804, 26269, 51092]]]
 hmul := by decide  
 g := ![![![![61, 145, -244, 109, 212]]]]
 hle2 := by decide  


def PBC241 : ContainsPrimesAboveP 241 ![I241N0, I241N1, I241N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI241N0
    exact isPrimeI241N1
    exact isPrimeI241N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 241 (by decide) (𝕀 ⊙ MulI241N0 ⊙ MulI241N1)
instance hp251 : Fact (Nat.Prime 251) := {out := by norm_num}

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-115, -515, -756, 485, 1366]] i)))

def SI251N0: IdealEqSpanCertificate' Table ![![-115, -515, -756, 485, 1366]] 
 ![![251, 0, 0, 0, 0], ![0, 251, 0, 0, 0], ![0, 0, 251, 0, 0], ![159, 185, 177, 1, 0], ![211, 35, 61, 0, 1]] where
  M :=![![![-115, -515, -756, 485, 1366], ![-1068, -475, -484, 348, 908], ![-1632, -1340, -1607, 1088, 2960], ![-1290, -990, -1228, 827, 2234], ![-450, -544, -692, 460, 1275]]]
  hmulB := by decide  
  f := ![![![109, 33, 100, -87, -220]], ![![492, 163, 428, -384, -964]], ![![2256, 724, 2019, -1792, -4480]], ![![2043, 658, 1821, -1618, -4050]], ![![707, 226, 633, -561, -1405]]]
  g := ![![![-1456, -550, -677, 485, 1366], ![-988, -385, -468, 348, 908], ![-3184, -1220, -1493, 1088, 2960], ![-2407, -925, -1131, 827, 2234], ![-1365, -519, -637, 460, 1275]]]
  hle1 := by decide   
  hle2 := by decide  


def P251P0 : CertificateIrreducibleZModOfList' 251 3 2 7 [229, 11, 174, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [43, 225, 67], [34, 25, 184], [0, 1]]
 g := ![![[59, 128, 154], [64, 182, 156], [121, 214], [66, 236, 21], [18, 228, 122], [107, 27, 156], [1]], ![[115, 129, 107, 79], [204, 142, 44, 89], [29, 12], [63, 240, 30, 94], [206, 235, 95, 48], [50, 8, 15, 65], [64, 227, 239, 65]], ![[106, 28, 105, 236], [209, 84, 63, 30], [162, 80], [157, 248, 164, 46], [166, 145, 95, 235], [84, 220, 160, 77], [239, 235, 99, 186]]]
 h' := ![![[43, 225, 67], [153, 161, 107], [56, 54, 174], [197, 140, 163], [145, 38, 71], [95, 152, 97], [22, 240, 77], [0, 1]], ![[34, 25, 184], [152, 139, 159], [77, 11, 187], [145, 21, 152], [152, 214, 54], [21, 133, 59], [93, 126, 184], [43, 225, 67]], ![[0, 1], [32, 202, 236], [150, 186, 141], [241, 90, 187], [28, 250, 126], [22, 217, 95], [135, 136, 241], [34, 25, 184]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58, 61], []]
 b := ![[], [234, 210, 89], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI251N0 : CertifiedPrimeIdeal' SI251N0 251 where
  n := 3
  hpos := by decide
  P := [229, 11, 174, 1]
  hirr := P251P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![37955035, 10322348, 36870502, -30710010, -79777160]
  a := ![92, 5, 113, -85, -235]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![86668635, 33800298, 41191032, -30710010, -79777160]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI251N0 : Ideal.IsPrime I251N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI251N0 B_one_repr
lemma NI251N0 : Nat.card (O ⧸ I251N0) = 15813251 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI251N0

def I251N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-65, 2, -52, 56, 134]] i)))

def SI251N1: IdealEqSpanCertificate' Table ![![-65, 2, -52, 56, 134]] 
 ![![251, 0, 0, 0, 0], ![42, 1, 0, 0, 0], ![244, 0, 1, 0, 0], ![126, 0, 0, 1, 0], ![84, 0, 0, 0, 1]] where
  M :=![![![-65, 2, -52, 56, 134], ![-408, -95, -374, 348, 864], ![-2160, -614, -1931, 1748, 4368], ![-5052, -1562, -4506, 4023, 10088], ![408, 160, 364, -310, -787]]]
  hmulB := by decide  
  f := ![![![1013, -722, 2952, -1596, -4694]], ![![174, -111, 478, -260, -772]], ![![892, -714, 2777, -1492, -4344]], ![![750, -410, 1898, -1041, -3132]], ![![204, -228, 784, -414, -1171]]]
  g := ![![![-23, 2, -52, 56, 134], ![-86, -95, -374, 348, 864], ![-368, -614, -1931, 1748, 4368], ![-774, -1562, -4506, 4023, 10088], ![40, 160, 364, -310, -787]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N1 : Nat.card (O ⧸ I251N1) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N1)

lemma isPrimeI251N1 : Ideal.IsPrime I251N1 := prime_ideal_of_norm_prime hp251.out _ NI251N1

def I251N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, -63, 148, -73, -182]] i)))

def SI251N2: IdealEqSpanCertificate' Table ![![7, -63, 148, -73, -182]] 
 ![![251, 0, 0, 0, 0], ![106, 1, 0, 0, 0], ![59, 0, 1, 0, 0], ![83, 0, 0, 1, 0], ![160, 0, 0, 0, 1]] where
  M :=![![![7, -63, 148, -73, -182], ![444, 119, 310, -220, -892], ![-2784, 302, -4253, 2500, 8304], ![4602, -1926, 10178, -5663, -17418], ![-3006, 890, -5836, 3304, 10425]]]
  hmulB := by decide  
  f := ![![![-42337, -26131, -29760, 20547, 55060]], ![![-18194, -11267, -12846, 8866, 23764]], ![![-10609, -6601, -7537, 5199, 13940]], ![![-14503, -8995, -10258, 7078, 18974]], ![![-27218, -16812, -19152, 13222, 35433]]]
  g := ![![![132, -63, 148, -73, -182], ![520, 119, 310, -220, -892], ![-5259, 302, -4253, 2500, 8304], ![11415, -1926, 10178, -5663, -17418], ![-6754, 890, -5836, 3304, 10425]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N2 : Nat.card (O ⧸ I251N2) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N2)

lemma isPrimeI251N2 : Ideal.IsPrime I251N2 := prime_ideal_of_norm_prime hp251.out _ NI251N2
def MulI251N0 : IdealMulLeCertificate' Table 
  ![![-115, -515, -756, 485, 1366]] ![![-65, 2, -52, 56, 134]]
  ![![-42337, -26131, -29760, 20547, 55060]] where
 M := ![![![-42337, -26131, -29760, 20547, 55060]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI251N1 : IdealMulLeCertificate' Table 
  ![![-42337, -26131, -29760, 20547, 55060]] ![![7, -63, 148, -73, -182]]
  ![![251, 0, 0, 0, 0]] where
 M := ![![![251, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC251 : ContainsPrimesAboveP 251 ![I251N0, I251N1, I251N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI251N0
    exact isPrimeI251N1
    exact isPrimeI251N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 251 (by decide) (𝕀 ⊙ MulI251N0 ⊙ MulI251N1)


lemma PB696I5_primes (p : ℕ) :
  p ∈ Set.range ![199, 211, 223, 227, 229, 233, 239, 241, 251] ↔ Nat.Prime p ∧ 197 < p ∧ p ≤ 251 := by
  rw [← List.mem_ofFn']
  convert primes_range 197 251 (by omega)

def PB696I5 : PrimesBelowBoundCertificateInterval O 197 251 696 where
  m := 9
  g := ![2, 3, 3, 2, 2, 2, 2, 3, 3]
  P := ![199, 211, 223, 227, 229, 233, 239, 241, 251]
  hP := PB696I5_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I199N0, I199N1]
    · exact ![I211N0, I211N1, I211N2]
    · exact ![I223N0, I223N1, I223N2]
    · exact ![I227N0, I227N1]
    · exact ![I229N0, I229N1]
    · exact ![I233N0, I233N1]
    · exact ![I239N0, I239N1]
    · exact ![I241N0, I241N1, I241N2]
    · exact ![I251N0, I251N1, I251N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC199
    · exact PBC211
    · exact PBC223
    · exact PBC227
    · exact PBC229
    · exact PBC233
    · exact PBC239
    · exact PBC241
    · exact PBC251
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![7880599, 39601]
    · exact ![9393931, 211, 211]
    · exact ![49729, 49729, 223]
    · exact ![2655237841, 227]
    · exact ![2750058481, 229]
    · exact ![12649337, 54289]
    · exact ![13651919, 57121]
    · exact ![13997521, 241, 241]
    · exact ![15813251, 251, 251]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI199N0
      exact NI199N1
    · dsimp ; intro j
      fin_cases j
      exact NI211N0
      exact NI211N1
      exact NI211N2
    · dsimp ; intro j
      fin_cases j
      exact NI223N0
      exact NI223N1
      exact NI223N2
    · dsimp ; intro j
      fin_cases j
      exact NI227N0
      exact NI227N1
    · dsimp ; intro j
      fin_cases j
      exact NI229N0
      exact NI229N1
    · dsimp ; intro j
      fin_cases j
      exact NI233N0
      exact NI233N1
    · dsimp ; intro j
      fin_cases j
      exact NI239N0
      exact NI239N1
    · dsimp ; intro j
      fin_cases j
      exact NI241N0
      exact NI241N1
      exact NI241N2
    · dsimp ; intro j
      fin_cases j
      exact NI251N0
      exact NI251N1
      exact NI251N2
  β := ![I211N1, I211N2, I223N2, I227N1, I229N1, I241N1, I241N2, I251N1, I251N2]
  Il := ![[], [I211N1, I211N2], [I223N2], [I227N1], [I229N1], [], [], [I241N1, I241N2], [I251N1, I251N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
