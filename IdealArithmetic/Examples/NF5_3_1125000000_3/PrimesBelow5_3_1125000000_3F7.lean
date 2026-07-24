
import IdealArithmetic.Examples.NF5_3_1125000000_3.RI5_3_1125000000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp311 : Fact (Nat.Prime 311) := {out := by norm_num}

def I311N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13725, 5284, 3818, -930, -5516]] i)))

def SI311N0: IdealEqSpanCertificate' Table ![![-13725, 5284, 3818, -930, -5516]] 
 ![![311, 0, 0, 0, 0], ![0, 311, 0, 0, 0], ![0, 0, 311, 0, 0], ![0, 0, 0, 311, 0], ![155, 292, 130, 19, 1]] where
  M :=![![![-13725, 5284, 3818, -930, -5516], ![8156, -3871, -2028, -172, 3592], ![-5672, 920, 4001, 4056, -8560], ![5390, 804, -3766, -493, 5392], ![-3122, -1700, 3742, 2322, -6507]]]
  hmulB := by decide  
  f := ![![![409, 388, -158, 638, 604]], ![![2812, 2775, -956, 4212, 3896]], ![![18904, 18776, -6281, 28120, 25904]], ![![9174, 9140, -3014, 13601, 12504]], ![![11349, 11248, -3800, 16921, 15609]]]
  g := ![![![2705, 5196, 2318, 334, -5516], ![-1764, -3385, -1508, -220, 3592], ![4248, 8040, 3591, 536, -8560], ![-2670, -5060, -2266, -331, 5392], ![3233, 6104, 2732, 405, -6507]]]
  hle1 := by decide   
  hle2 := by decide  


def P311P0 : CertificateIrreducibleZModOfList' 311 4 2 8 [297, 293, 275, 129, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [70, 13, 67, 146], [143, 234, 2, 197], [280, 63, 242, 279], [0, 1]]
 g := ![![[5, 237, 260, 78], [4, 111, 82, 300], [156, 155, 247, 108], [53, 189, 63], [293, 136, 196, 173], [35, 116, 186, 158], [1], []], ![[205, 55, 49, 246, 7, 197], [85, 181, 161, 117], [187, 235, 74, 242, 268, 192], [136, 194, 2], [46, 31, 297, 237, 305, 208], [87, 303, 28, 266, 288, 39], [244, 137, 223], [145, 69, 168]], ![[45, 289, 109, 215, 30, 201], [216, 236, 16, 163, 2, 168], [74, 258, 200, 144, 26, 64], [289, 74, 98], [309, 263, 81, 297, 205, 130], [137, 55, 39, 77, 282, 180], [241, 95, 252], [136, 283, 245]], ![[153, 135, 152, 282, 168, 119], [305, 214, 296, 304, 247, 302], [108, 265, 236, 11, 34, 198], [99, 67, 265], [124, 206, 173, 229, 154, 92], [147, 283, 134, 253, 26, 131], [157, 218, 268], [122, 141, 91]]]
 h' := ![![[70, 13, 67, 146], [56, 120, 59, 156], [7, 58, 272, 61], [180, 30, 266, 150], [59, 33, 270, 202], [179, 273, 236, 22], [14, 18, 36, 182], [0, 0, 1], [0, 1]], ![[143, 234, 2, 197], [302, 155, 204, 261], [197, 257, 244], [200, 199, 252, 155], [28, 239, 6, 245], [193, 154, 294, 118], [275, 303, 105, 40], [88, 109, 14, 277], [70, 13, 67, 146]], ![[280, 63, 242, 279], [280, 184, 244, 300], [162, 81, 109, 303], [203, 260, 21, 285], [38, 306, 73, 151], [299, 59, 99, 165], [230, 241, 260, 51], [272, 249, 17, 218], [143, 234, 2, 197]], ![[0, 1], [139, 163, 115, 216], [64, 226, 308, 258], [187, 133, 83, 32], [271, 44, 273, 24], [281, 136, 304, 6], [127, 60, 221, 38], [181, 264, 279, 127], [280, 63, 242, 279]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [235, 119, 232], []]
 b := ![[], [], [197, 277, 106, 193], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI311N0 : CertifiedPrimeIdeal' SI311N0 311 where
  n := 4
  hpos := by decide
  P := [297, 293, 275, 129, 1]
  hirr := P311P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![44894468948771, 44536184876728, -14339617599440, 67538145111212, 60794920549248]
  a := ![-176, -194, 145, -109, -324]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-30155364039179, -56937558249208, -25458775848880, -3496994679500, 60794920549248]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI311N0 : Ideal.IsPrime I311N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI311N0 B_one_repr
lemma NI311N0 : Nat.card (O ⧸ I311N0) = 9354951841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI311N0

def I311N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-409, -388, 158, -638, -604]] i)))

def SI311N1: IdealEqSpanCertificate' Table ![![-409, -388, 158, -638, -604]] 
 ![![311, 0, 0, 0, 0], ![161, 1, 0, 0, 0], ![203, 0, 1, 0, 0], ![268, 0, 0, 1, 0], ![159, 0, 0, 0, 1]] where
  M :=![![![-409, -388, 158, -638, -604], ![-2812, -2775, 956, -4212, -3896], ![-18904, -18776, 6281, -28120, -25904], ![-9174, -9140, 3014, -13601, -12504], ![-13214, -13148, 4362, -19618, -18051]]]
  hmulB := by decide  
  f := ![![![13725, -5284, -3818, 930, 5516]], ![![7079, -2723, -1970, 482, 2844]], ![![8977, -3452, -2505, 594, 3628]], ![![11810, -4556, -3278, 803, 4736]], ![![7027, -2696, -1964, 468, 2841]]]
  g := ![![![955, -388, 158, -638, -604], ![6425, -2775, 956, -4212, -3896], ![43035, -18776, 6281, -28120, -25904], ![20848, -9140, 3014, -13601, -12504], ![30051, -13148, 4362, -19618, -18051]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI311N1 : Nat.card (O ⧸ I311N1) = 311 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI311N1)

lemma isPrimeI311N1 : Ideal.IsPrime I311N1 := prime_ideal_of_norm_prime hp311.out _ NI311N1
def MulI311N0 : IdealMulLeCertificate' Table 
  ![![-13725, 5284, 3818, -930, -5516]] ![![-409, -388, 158, -638, -604]]
  ![![311, 0, 0, 0, 0]] where
 M := ![![![-311, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC311 : ContainsPrimesAboveP 311 ![I311N0, I311N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI311N0
    exact isPrimeI311N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 311 (by decide) (𝕀 ⊙ MulI311N0)
instance hp313 : Fact (Nat.Prime 313) := {out := by norm_num}

def I313N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 7, 4, -1, -6]] i)))

def SI313N0: IdealEqSpanCertificate' Table ![![2, 7, 4, -1, -6]] 
 ![![313, 0, 0, 0, 0], ![0, 313, 0, 0, 0], ![47, 170, 1, 0, 0], ![65, 100, 0, 1, 0], ![281, 252, 0, 0, 1]] where
  M :=![![![2, 7, 4, -1, -6], ![8, 12, -1, -2, 4], ![-6, -1, 28, 16, -24], ![11, 6, -11, 16, 16], ![-7, -7, 12, 9, -3]]]
  hmulB := by decide  
  f := ![![![-214, 83, 68, -17, -96]], ![![148, -38, -41, 14, 56]], ![![48, -8, -12, 5, 16]], ![![3, 5, 1, 1, -2]], ![![-73, 44, 28, -4, -41]]]
  g := ![![![5, 3, 4, -1, -6], ![-3, -2, -1, -2, 4], ![14, -1, 28, 16, -24], ![-16, -12, -11, 16, 16], ![-1, -7, 12, 9, -3]]]
  hle1 := by decide   
  hle2 := by decide  


def P313P0 : CertificateIrreducibleZModOfList' 313 2 2 8 [175, 45, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [268, 312], [0, 1]]
 g := ![![[197, 100], [213], [176], [188, 139], [162, 265], [104, 234], [147], [1]], ![[79, 213], [213], [176], [193, 174], [131, 48], [216, 79], [147], [1]]]
 h' := ![![[268, 312], [219, 303], [160, 250], [278, 241], [133, 96], [267, 151], [205, 58], [138, 268], [0, 1]], ![[0, 1], [43, 10], [178, 63], [75, 72], [195, 217], [45, 162], [99, 255], [285, 45], [268, 312]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [120]]
 b := ![[], [98, 60]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI313N0 : CertifiedPrimeIdeal' SI313N0 313 where
  n := 2
  hpos := by decide
  P := [175, 45, 1]
  hirr := P313P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![153559847, 148383780, -22865814, 274362142, 186852660]
  a := ![-2547, -2778, 1994, -1752, -4457]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-220801545, -225199720, -22865814, 274362142, 186852660]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI313N0 : Ideal.IsPrime I313N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI313N0 B_one_repr
lemma NI313N0 : Nat.card (O ⧸ I313N0) = 97969 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI313N0

def I313N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![535, -771, -503, 214, 720]] i)))

def SI313N1: IdealEqSpanCertificate' Table ![![535, -771, -503, 214, 720]] 
 ![![313, 0, 0, 0, 0], ![71, 1, 0, 0, 0], ![280, 0, 1, 0, 0], ![114, 0, 0, 1, 0], ![82, 0, 0, 0, 1]] where
  M :=![![![535, -771, -503, 214, 720], ![-722, -404, -187, 152, 272], ![30, -777, -468, 236, 672], ![-10, 496, 298, -151, -428], ![152, 131, 67, -46, -97]]]
  hmulB := by decide  
  f := ![![![-157, -111, -29, -382, 8]], ![![-41, -31, -2, -90, -8]], ![![-146, -105, -38, -372, 0]], ![![-72, -54, -4, -159, -12]], ![![-46, -35, -13, -118, -9]]]
  g := ![![![360, -771, -503, 214, 720], ![130, -404, -187, 152, 272], ![333, -777, -468, 236, 672], ![-212, 496, 298, -151, -428], ![-47, 131, 67, -46, -97]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI313N1 : Nat.card (O ⧸ I313N1) = 313 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI313N1)

lemma isPrimeI313N1 : Ideal.IsPrime I313N1 := prime_ideal_of_norm_prime hp313.out _ NI313N1

def I313N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![399, 43, 185, 1250, -1154]] i)))

def SI313N2: IdealEqSpanCertificate' Table ![![399, 43, 185, 1250, -1154]] 
 ![![313, 0, 0, 0, 0], ![77, 1, 0, 0, 0], ![18, 0, 1, 0, 0], ![192, 0, 0, 1, 0], ![266, 0, 0, 0, 1]] where
  M :=![![![399, 43, 185, 1250, -1154], ![3802, 5170, -7265, -4512, 12308], ![-37022, -38263, 47834, 2260, -60712], ![12768, 10364, -11126, 8991, 7074], ![-25884, -24307, 28807, -6854, -30479]]]
  hmulB := by decide  
  f := ![![![255771, -86377, -71509, 16622, 101734]], ![![62413, -21037, -17430, 4054, 24802]], ![![15088, -5033, -4210, 1024, 6020]], ![![156700, -52908, -43818, 10211, 62354]], ![![217478, -73421, -60809, 14170, 86533]]]
  g := ![![![194, 43, 185, 1250, -1154], ![-8534, 5170, -7265, -4512, 12308], ![56753, -38263, 47834, 2260, -60712], ![-13396, 10364, -11126, 8991, 7074], ![34347, -24307, 28807, -6854, -30479]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI313N2 : Nat.card (O ⧸ I313N2) = 313 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI313N2)

lemma isPrimeI313N2 : Ideal.IsPrime I313N2 := prime_ideal_of_norm_prime hp313.out _ NI313N2

def I313N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![16, 20, -15, 1, 16]] i)))

def SI313N3: IdealEqSpanCertificate' Table ![![16, 20, -15, 1, 16]] 
 ![![313, 0, 0, 0, 0], ![308, 1, 0, 0, 0], ![288, 0, 1, 0, 0], ![253, 0, 0, 1, 0], ![281, 0, 0, 0, 1]] where
  M :=![![![16, 20, -15, 1, 16], ![-54, -39, 48, -50, -24], ![40, -38, 113, 284, -352], ![107, 122, -169, -54, 250], ![-79, -128, 187, 163, -351]]]
  hmulB := by decide  
  f := ![![![18848, 18992, -6233, 28241, 25926]], ![![18954, 19093, -6268, 28394, 26068]], ![![20064, 20182, -6635, 30028, 27576]], ![![16553, 16662, -5474, 24785, 22758]], ![![18821, 18940, -6224, 28176, 25873]]]
  g := ![![![-21, 20, -15, 1, 16], ![56, -39, 48, -50, -24], ![20, -38, 113, 284, -352], ![-145, 122, -169, -54, 250], ![137, -128, 187, 163, -351]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI313N3 : Nat.card (O ⧸ I313N3) = 313 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI313N3)

lemma isPrimeI313N3 : Ideal.IsPrime I313N3 := prime_ideal_of_norm_prime hp313.out _ NI313N3
def MulI313N0 : IdealMulLeCertificate' Table 
  ![![2, 7, 4, -1, -6]] ![![535, -771, -503, 214, 720]]
  ![![-4766, -8760, -4887, 2863, 7042]] where
 M := ![![![-4766, -8760, -4887, 2863, 7042]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI313N1 : IdealMulLeCertificate' Table 
  ![![-4766, -8760, -4887, 2863, 7042]] ![![399, 43, 185, 1250, -1154]]
  ![![-984, -619, 88, -1635, 1172]] where
 M := ![![![-984, -619, 88, -1635, 1172]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI313N2 : IdealMulLeCertificate' Table 
  ![![-984, -619, 88, -1635, 1172]] ![![16, 20, -15, 1, 16]]
  ![![313, 0, 0, 0, 0]] where
 M := ![![![-246331, -348369, 490471, 334284, -851986]]]
 hmul := by decide  
 g := ![![![![-787, -1113, 1567, 1068, -2722]]]]
 hle2 := by decide  


def PBC313 : ContainsPrimesAboveP 313 ![I313N0, I313N1, I313N2, I313N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI313N0
    exact isPrimeI313N1
    exact isPrimeI313N2
    exact isPrimeI313N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 313 (by decide) (𝕀 ⊙ MulI313N0 ⊙ MulI313N1 ⊙ MulI313N2)
instance hp317 : Fact (Nat.Prime 317) := {out := by norm_num}

def I317N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5208, -12428, -7053, 3999, 10156]] i)))

def SI317N0: IdealEqSpanCertificate' Table ![![-5208, -12428, -7053, 3999, 10156]] 
 ![![317, 0, 0, 0, 0], ![0, 317, 0, 0, 0], ![110, 40, 1, 0, 0], ![215, 114, 0, 1, 0], ![257, 281, 0, 0, 1]] where
  M :=![![![-5208, -12428, -7053, 3999, 10156], ![-6010, -14321, -8112, 4610, 11680], ![-6872, -16450, -9401, 5316, 13520], ![4433, 10590, 6017, -3422, -8654], ![1703, 4024, 2249, -1275, -3253]]]
  hmulB := by decide  
  f := ![![![-3648, -3752, 1209, -5549, -5074]], ![![-25090, -24873, 8296, -37182, -34244]], ![![-4960, -4966, 1641, -7402, -6804]], ![![-11753, -11744, 3888, -17515, -16106]], ![![-25567, -25457, 8456, -38006, -34973]]]
  g := ![![![-8515, -9590, -7053, 3999, 10156], ![-9800, -11033, -8112, 4610, 11680], ![-11326, -12762, -9401, 5316, 13520], ![7263, 8176, 6017, -3422, -8654], ![2727, 3071, 2249, -1275, -3253]]]
  hle1 := by decide   
  hle2 := by decide  


def P317P0 : CertificateIrreducibleZModOfList' 317 2 2 8 [236, 198, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [119, 316], [0, 1]]
 g := ![![[68, 90], [101], [291, 16], [2, 247], [52, 103], [104, 112], [213], [1]], ![[0, 227], [101], [293, 301], [231, 70], [263, 214], [118, 205], [213], [1]]]
 h' := ![![[119, 316], [28, 93], [113, 37], [162, 313], [91, 105], [182, 145], [39, 245], [81, 119], [0, 1]], ![[0, 1], [0, 224], [78, 280], [3, 4], [223, 212], [2, 172], [30, 72], [294, 198], [119, 316]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [219]]
 b := ![[], [221, 268]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI317N0 : CertifiedPrimeIdeal' SI317N0 317 where
  n := 2
  hpos := by decide
  P := [236, 198, 1]
  hirr := P317P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![434574, 418678, -53401, 795342, 525947]
  a := ![-139, -151, 107, -99, -239]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-945925, -744181, -53401, 795342, 525947]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI317N0 : Ideal.IsPrime I317N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI317N0 B_one_repr
lemma NI317N0 : Nat.card (O ⧸ I317N0) = 100489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI317N0

def I317N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-15, -19, 25, 10, -38]] i)))

def SI317N1: IdealEqSpanCertificate' Table ![![-15, -19, 25, 10, -38]] 
 ![![317, 0, 0, 0, 0], ![49, 1, 0, 0, 0], ![135, 0, 1, 0, 0], ![10, 0, 0, 1, 0], ![59, 0, 0, 0, 1]] where
  M :=![![![-15, -19, 25, 10, -38], ![114, 112, -135, 16, 156], ![-434, -341, 360, -340, -184], ![-4, -52, 98, 169, -242], ![-168, -89, 59, -278, 139]]]
  hmulB := by decide  
  f := ![![![-100039, -239595, -135977, 77102, 195786]], ![![-15829, -37905, -21512, 12198, 30974]], ![![-43023, -103038, -58477, 33158, 84198]], ![![-2886, -6914, -3924, 2225, 5650]], ![![-18517, -44350, -25170, 14272, 36241]]]
  g := ![![![-1, -19, 25, 10, -38], ![11, 112, -135, 16, 156], ![-57, -341, 360, -340, -184], ![6, -52, 98, 169, -242], ![-29, -89, 59, -278, 139]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI317N1 : Nat.card (O ⧸ I317N1) = 317 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI317N1)

lemma isPrimeI317N1 : Ideal.IsPrime I317N1 := prime_ideal_of_norm_prime hp317.out _ NI317N1

def I317N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![187, 186, -62, 278, 256]] i)))

def SI317N2: IdealEqSpanCertificate' Table ![![187, 186, -62, 278, 256]] 
 ![![317, 0, 0, 0, 0], ![100, 1, 0, 0, 0], ![144, 0, 1, 0, 0], ![291, 0, 0, 1, 0], ![37, 0, 0, 0, 1]] where
  M :=![![![187, 186, -62, 278, 256], ![1252, 1245, -414, 1860, 1712], ![8380, 8334, -2771, 12448, 11456], ![4058, 4036, -1342, 6027, 5548], ![5850, 5818, -1934, 8690, 7997]]]
  hmulB := by decide  
  f := ![![![-2805, 774, 658, -142, -920]], ![![-880, 241, 206, -44, -288]], ![![-1276, 354, 297, -64, -416]], ![![-2573, 710, 604, -131, -844]], ![![-327, 92, 76, -16, -107]]]
  g := ![![![-315, 186, -62, 278, 256], ![-2108, 1245, -414, 1860, 1712], ![-14108, 8334, -2771, 12448, 11456], ![-6831, 4036, -1342, 6027, 5548], ![-9849, 5818, -1934, 8690, 7997]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI317N2 : Nat.card (O ⧸ I317N2) = 317 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI317N2)

lemma isPrimeI317N2 : Ideal.IsPrime I317N2 := prime_ideal_of_norm_prime hp317.out _ NI317N2

def I317N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1184, 413, 338, -79, -480]] i)))

def SI317N3: IdealEqSpanCertificate' Table ![![-1184, 413, 338, -79, -480]] 
 ![![317, 0, 0, 0, 0], ![128, 1, 0, 0, 0], ![100, 0, 1, 0, 0], ![307, 0, 0, 1, 0], ![149, 0, 0, 0, 1]] where
  M :=![![![-1184, 413, 338, -79, -480], ![752, -290, -231, 58, 328], ![-498, 157, 134, -32, -192], ![303, -98, -81, 16, 114], ![-133, 51, 42, -13, -61]]]
  hmulB := by decide  
  f := ![![![-304, -363, 478, 181, -726]], ![![-116, -140, 185, 74, -284]], ![![-122, -135, 172, 36, -240]], ![![-295, -355, 469, 185, -718]], ![![-153, -176, 228, 68, -333]]]
  g := ![![![25, 413, 338, -79, -480], ![-18, -290, -231, 58, 328], ![14, 157, 134, -32, -192], ![-3, -98, -81, 16, 114], ![7, 51, 42, -13, -61]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI317N3 : Nat.card (O ⧸ I317N3) = 317 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI317N3)

lemma isPrimeI317N3 : Ideal.IsPrime I317N3 := prime_ideal_of_norm_prime hp317.out _ NI317N3
def MulI317N0 : IdealMulLeCertificate' Table 
  ![![-5208, -12428, -7053, 3999, 10156]] ![![-15, -19, 25, 10, -38]]
  ![![126, 257, -394, -445, 814]] where
 M := ![![![126, 257, -394, -445, 814]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI317N1 : IdealMulLeCertificate' Table 
  ![![126, 257, -394, -445, 814]] ![![187, 186, -62, 278, 256]]
  ![![-304, -363, 478, 181, -726]] where
 M := ![![![-304, -363, 478, 181, -726]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI317N2 : IdealMulLeCertificate' Table 
  ![![-304, -363, 478, 181, -726]] ![![-1184, 413, 338, -79, -480]]
  ![![317, 0, 0, 0, 0]] where
 M := ![![![317, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC317 : ContainsPrimesAboveP 317 ![I317N0, I317N1, I317N2, I317N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI317N0
    exact isPrimeI317N1
    exact isPrimeI317N2
    exact isPrimeI317N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 317 (by decide) (𝕀 ⊙ MulI317N0 ⊙ MulI317N1 ⊙ MulI317N2)
instance hp331 : Fact (Nat.Prime 331) := {out := by norm_num}

def I331N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29859, 59577, 33431, -19370, -48160]] i)))

def SI331N0: IdealEqSpanCertificate' Table ![![29859, 59577, 33431, -19370, -48160]] 
 ![![331, 0, 0, 0, 0], ![0, 331, 0, 0, 0], ![0, 0, 331, 0, 0], ![9, 49, 220, 1, 0], ![255, 300, 212, 0, 1]] where
  M :=![![![29859, 59577, 33431, -19370, -48160], ![26786, 71374, 40737, -22848, -58640], ![35750, 80439, 45486, -25972, -65504], ![-22922, -51712, -29246, 16693, 42116], ![-7776, -19861, -11311, 6370, 16283]]]
  hmulB := by decide  
  f := ![![![85, 87, -113, -10, 136]], ![![-446, -384, 399, -288, -352]], ![![538, 45, 64, 1396, -1600]], ![![295, -23, 96, 883, -1108]], ![![5, -254, 318, 628, -1245]]]
  g := ![![![37719, 46697, 43821, -19370, -48160], ![45878, 56746, 52867, -22848, -58640], ![51278, 63457, 59354, -25972, -65504], ![-32969, -40799, -38158, 16693, 42116], ![-12741, -15761, -14697, 6370, 16283]]]
  hle1 := by decide   
  hle2 := by decide  


def P331P0 : CertificateIrreducibleZModOfList' 331 3 2 8 [124, 299, 307, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [271, 294, 161], [84, 36, 170], [0, 1]]
 g := ![![[182, 287, 195], [230, 48, 234], [309, 318], [20, 222, 279], [102, 304], [7, 100], [277, 24, 1], []], ![[59, 117, 17, 143], [5, 0, 241, 238], [232, 169], [88, 71, 299, 20], [264, 274], [89, 169], [80, 306, 102, 126], [157, 103]], ![[77, 270, 224, 199], [265, 58, 135, 51], [207, 232], [65, 286, 200, 298], [153, 224], [115, 198], [92, 179, 195, 37], [148, 103]]]
 h' := ![![[271, 294, 161], [277, 179, 107], [169, 268, 123], [168, 203, 48], [200, 18, 96], [274, 23, 189], [76, 261, 10], [0, 0, 1], [0, 1]], ![[84, 36, 170], [283, 211, 233], [120, 260, 243], [202, 198, 318], [47, 188, 65], [26, 189, 246], [173, 293, 13], [20, 2, 36], [271, 294, 161]], ![[0, 1], [227, 272, 322], [303, 134, 296], [309, 261, 296], [328, 125, 170], [226, 119, 227], [65, 108, 308], [289, 329, 294], [84, 36, 170]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [78, 306], []]
 b := ![[], [266, 312, 68], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI331N0 : CertifiedPrimeIdeal' SI331N0 331 where
  n := 3
  hpos := by decide
  P := [124, 299, 307, 1]
  hirr := P331P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1287046737962, 1289854512117, -475528636654, 1828022552099, 1810572289647]
  a := ![1030, 1133, -838, 655, 1873]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1440667945894, -1907718844214, -2376077992458, 1828022552099, 1810572289647]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI331N0 : Ideal.IsPrime I331N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI331N0 B_one_repr
lemma NI331N0 : Nat.card (O ⧸ I331N0) = 36264691 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI331N0

def I331N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![85, 87, -113, -10, 136]] i)))

def SI331N1: IdealEqSpanCertificate' Table ![![85, 87, -113, -10, 136]] 
 ![![331, 0, 0, 0, 0], ![0, 331, 0, 0, 0], ![118, 8, 1, 0, 0], ![308, 198, 0, 1, 0], ![41, 292, 0, 0, 1]] where
  M :=![![![85, 87, -113, -10, 136], ![-446, -384, 399, -288, -352], ![538, 45, 64, 1396, -1600], ![374, 520, -838, -645, 1276], ![-276, -599, 805, 866, -1975]]]
  hmulB := by decide  
  f := ![![![29859, 59577, 33431, -19370, -48160]], ![![26786, 71374, 40737, -22848, -58640]], ![![11400, 23207, 13040, -7536, -18784]], ![![43738, 97976, 55388, -31641, -79764]], ![![27305, 70284, 40044, -22536, -57647]]]
  g := ![![![33, -111, -113, -10, 136], ![168, 472, 399, -288, -352], ![-1122, 575, 64, 1396, -1600], ![742, -718, -838, -645, 1276], ![-849, 1203, 805, 866, -1975]]]
  hle1 := by decide   
  hle2 := by decide  


def P331P1 : CertificateIrreducibleZModOfList' 331 2 2 8 [309, 283, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [48, 330], [0, 1]]
 g := ![![[273, 196], [177, 102], [39], [167, 64], [39], [319], [164, 318], [1]], ![[82, 135], [108, 229], [39], [260, 267], [39], [319], [202, 13], [1]]]
 h' := ![![[48, 330], [253, 14], [292, 226], [33, 286], [285, 323], [163, 45], [298, 126], [22, 48], [0, 1]], ![[0, 1], [263, 317], [217, 105], [190, 45], [232, 8], [6, 286], [57, 205], [9, 283], [48, 330]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [150]]
 b := ![[], [186, 75]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI331N1 : CertifiedPrimeIdeal' SI331N1 331 where
  n := 2
  hpos := by decide
  P := [309, 283, 1]
  hirr := P331P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1212989, 1062473, 54137, 2589402, 938266]
  a := ![-241, -275, 228, -100, -509]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2541329, -2374761, 54137, 2589402, 938266]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI331N1 : Ideal.IsPrime I331N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI331N1 B_one_repr
lemma NI331N1 : Nat.card (O ⧸ I331N1) = 109561 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI331N1
def MulI331N0 : IdealMulLeCertificate' Table 
  ![![29859, 59577, 33431, -19370, -48160]] ![![85, 87, -113, -10, 136]]
  ![![331, 0, 0, 0, 0]] where
 M := ![![![331, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC331 : ContainsPrimesAboveP 331 ![I331N0, I331N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI331N0
    exact isPrimeI331N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 331 (by decide) (𝕀 ⊙ MulI331N0)
instance hp337 : Fact (Nat.Prime 337) := {out := by norm_num}

def I337N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![680, -299, -176, 13, 282]] i)))

def SI337N0: IdealEqSpanCertificate' Table ![![680, -299, -176, 13, 282]] 
 ![![337, 0, 0, 0, 0], ![0, 337, 0, 0, 0], ![0, 0, 337, 0, 0], ![0, 0, 0, 337, 0], ![294, 177, 138, 300, 1]] where
  M :=![![![680, -299, -176, 13, 282], ![-440, 134, 213, 170, -460], ![1038, 845, -1466, -784, 2280], ![-771, -502, 711, -154, -852], ![835, 795, -1128, -269, 1501]]]
  hmulB := by decide  
  f := ![![![296, 705, 400, -227, -576]], ![![340, 812, 461, -262, -664]], ![![390, 933, 532, -304, -768]], ![![-253, -602, -341, 192, 490]], ![![371, 887, 505, -289, -729]]]
  g := ![![![-244, -149, -116, -251, 282], ![400, 242, 189, 410, -460], ![-1986, -1195, -938, -2032, 2280], ![741, 446, 351, 758, -852], ![-1307, -786, -618, -1337, 1501]]]
  hle1 := by decide   
  hle2 := by decide  


def P337P0 : CertificateIrreducibleZModOfList' 337 4 2 8 [304, 232, 211, 46, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [140, 12, 105, 207], [224, 150, 293, 250], [264, 174, 276, 217], [0, 1]]
 g := ![![[137, 228, 83, 290], [255, 142, 63], [148, 181, 145], [114, 287, 265], [294, 121, 122, 32], [109, 29, 209], [291, 1], []], ![[20, 101, 119, 266, 294, 291], [42, 63, 104], [306, 318, 239], [278, 331, 155], [294, 182, 171, 225, 237, 51], [259, 126, 13], [251, 26, 164, 116, 34, 46], [171, 56, 50]], ![[179, 304, 12, 313, 332, 212], [222, 95, 319], [198, 11, 103], [51, 143, 107], [28, 327, 118, 250, 257, 83], [237, 109, 12], [270, 227, 320, 295, 103, 31], [152, 189, 155]], ![[41, 59, 102, 49, 293, 212], [19, 296, 290], [2, 253, 190], [141, 293, 335], [231, 214, 69, 329, 221, 143], [194, 330, 25], [322, 309, 293, 153, 244, 53], [128, 291, 246]]]
 h' := ![![[140, 12, 105, 207], [285, 253, 224, 127], [162, 249, 261, 317], [41, 127, 152, 303], [266, 283, 290, 172], [145, 170, 147, 104], [167, 258, 38, 220], [0, 0, 1], [0, 1]], ![[224, 150, 293, 250], [227, 199, 97, 290], [111, 84, 21, 316], [125, 59, 326, 313], [130, 30, 223, 87], [171, 252, 42, 62], [330, 31, 243, 32], [305, 247, 319, 216], [140, 12, 105, 207]], ![[264, 174, 276, 217], [128, 146, 240, 239], [280, 210, 65, 251], [254, 250, 93, 281], [16, 30, 237, 219], [276, 64, 191, 212], [229, 91, 204, 90], [261, 92, 57, 130], [224, 150, 293, 250]], ![[0, 1], [126, 76, 113, 18], [39, 131, 327, 127], [240, 238, 103, 114], [110, 331, 261, 196], [154, 188, 294, 296], [87, 294, 189, 332], [117, 335, 297, 328], [264, 174, 276, 217]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [189, 260, 74], []]
 b := ![[], [], [79, 294, 44, 272], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI337N0 : CertifiedPrimeIdeal' SI337N0 337 where
  n := 4
  hpos := by decide
  P := [304, 232, 211, 46, 1]
  hirr := P337P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5506474047468, 4982578385816, -3390460026900, 5895534216000, 5341817815744]
  a := ![98, 126, -136, -32, 304]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4643881198164, -2790858086056, -2197511331156, -4737833265600, 5341817815744]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI337N0 : Ideal.IsPrime I337N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI337N0 B_one_repr
lemma NI337N0 : Nat.card (O ⧸ I337N0) = 12897917761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI337N0

def I337N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![296, 705, 400, -227, -576]] i)))

def SI337N1: IdealEqSpanCertificate' Table ![![296, 705, 400, -227, -576]] 
 ![![337, 0, 0, 0, 0], ![298, 1, 0, 0, 0], ![164, 0, 1, 0, 0], ![297, 0, 0, 1, 0], ![254, 0, 0, 0, 1]] where
  M :=![![![296, 705, 400, -227, -576], ![340, 812, 461, -262, -664], ![390, 933, 532, -304, -768], ![-253, -602, -341, 192, 490], ![-97, -229, -128, 71, 183]]]
  hmulB := by decide  
  f := ![![![680, -299, -176, 13, 282]], ![![600, -264, -155, 12, 248]], ![![334, -143, -90, 4, 144]], ![![597, -265, -153, 11, 246]], ![![515, -223, -136, 9, 217]]]
  g := ![![![-183, 705, 400, -227, -576], ![-210, 812, 461, -262, -664], ![-236, 933, 532, -304, -768], ![159, -602, -341, 192, 490], ![64, -229, -128, 71, 183]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI337N1 : Nat.card (O ⧸ I337N1) = 337 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI337N1)

lemma isPrimeI337N1 : Ideal.IsPrime I337N1 := prime_ideal_of_norm_prime hp337.out _ NI337N1
def MulI337N0 : IdealMulLeCertificate' Table 
  ![![680, -299, -176, 13, 282]] ![![296, 705, 400, -227, -576]]
  ![![337, 0, 0, 0, 0]] where
 M := ![![![337, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC337 : ContainsPrimesAboveP 337 ![I337N0, I337N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI337N0
    exact isPrimeI337N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 337 (by decide) (𝕀 ⊙ MulI337N0)
instance hp347 : Fact (Nat.Prime 347) := {out := by norm_num}

def I347N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2214, -5339, -3032, 1711, 4370]] i)))

def SI347N0: IdealEqSpanCertificate' Table ![![-2214, -5339, -3032, 1711, 4370]] 
 ![![347, 0, 0, 0, 0], ![0, 347, 0, 0, 0], ![0, 0, 347, 0, 0], ![207, 117, 337, 1, 0], ![10, 141, 257, 0, 1]] where
  M :=![![![-2214, -5339, -3032, 1711, 4370], ![-2608, -6160, -3443, 1998, 4948], ![-2770, -6883, -4256, 2264, 6088], ![1835, 4494, 2637, -1508, -3752], ![853, 1839, 828, -519, -1247]]]
  hmulB := by decide  
  f := ![![![-858, -869, 284, -1291, -1184]], ![![-5828, -5786, 1927, -8646, -7960]], ![![-38942, -38737, 12878, -57848, -53248]], ![![-40351, -40144, 13344, -59947, -55178]], ![![-31313, -31144, 10355, -46511, -42813]]]
  g := ![![![-1153, -2368, -4907, 1711, 4370], ![-1342, -2702, -5615, 1998, 4948], ![-1534, -3257, -6720, 2264, 6088], ![1013, 2046, 4251, -1508, -3752], ![348, 687, 1430, -519, -1247]]]
  hle1 := by decide   
  hle2 := by decide  


def P347P0 : CertificateIrreducibleZModOfList' 347 3 2 8 [336, 45, 291, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 228, 252], [23, 118, 95], [0, 1]]
 g := ![![[3, 260, 168], [215, 70, 115], [264, 46], [28, 202, 117], [31, 16, 321], [185, 31], [315, 56, 1], []], ![[276, 15, 269, 237], [181, 266, 163, 333], [167, 27], [302, 37, 230, 298], [21, 18, 234, 54], [110, 197], [255, 252, 163, 331], [223, 3]], ![[325, 97, 90, 14], [1, 230, 167, 297], [184, 161], [92, 144, 124, 192], [7, 6, 293, 40], [162, 127], [49, 54, 167, 323], [33, 3]]]
 h' := ![![[33, 228, 252], [283, 226, 207], [261, 308, 313], [308, 304, 156], [341, 306, 179], [325, 257, 254], [342, 321, 210], [0, 0, 1], [0, 1]], ![[23, 118, 95], [90, 224, 180], [343, 331, 40], [58, 92, 285], [78, 14, 33], [28, 166, 5], [30, 240, 184], [72, 188, 118], [33, 228, 252]], ![[0, 1], [316, 244, 307], [266, 55, 341], [18, 298, 253], [140, 27, 135], [314, 271, 88], [31, 133, 300], [198, 159, 228], [23, 118, 95]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [131, 205], []]
 b := ![[], [254, 235, 130], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI347N0 : CertifiedPrimeIdeal' SI347N0 347 where
  n := 3
  hpos := by decide
  P := [336, 45, 291, 1]
  hirr := P347P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![60588478672, 60900945470, -22589659936, 85652800593, 86103503205]
  a := ![374, 413, -313, 219, 701]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-53402237107, -63691846328, -147020702546, 85652800593, 86103503205]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI347N0 : Ideal.IsPrime I347N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI347N0 B_one_repr
lemma NI347N0 : Nat.card (O ⧸ I347N0) = 41781923 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI347N0

def I347N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![215, -77, -63, 16, 90]] i)))

def SI347N1: IdealEqSpanCertificate' Table ![![215, -77, -63, 16, 90]] 
 ![![347, 0, 0, 0, 0], ![209, 1, 0, 0, 0], ![41, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![243, 0, 0, 0, 1]] where
  M :=![![![215, -77, -63, 16, 90], ![-134, 54, 39, -4, -52], ![114, -7, -34, 44, 72], ![-42, 32, 12, 15, -6], ![42, 9, -13, 28, 35]]]
  hmulB := by decide  
  f := ![![![549, 1325, 797, -416, -1154]], ![![333, 803, 482, -252, -698]], ![![65, 160, 99, -52, -142]], ![![13, 31, 19, -9, -28]], ![![383, 926, 558, -292, -807]]]
  g := ![![![-9, -77, -63, 16, 90], ![-1, 54, 39, -4, -52], ![-43, -7, -34, 44, 72], ![-17, 32, 12, 15, -6], ![-29, 9, -13, 28, 35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI347N1 : Nat.card (O ⧸ I347N1) = 347 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI347N1)

lemma isPrimeI347N1 : Ideal.IsPrime I347N1 := prime_ideal_of_norm_prime hp347.out _ NI347N1

def I347N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-22, -22, 7, -33, -30]] i)))

def SI347N2: IdealEqSpanCertificate' Table ![![-22, -22, 7, -33, -30]] 
 ![![347, 0, 0, 0, 0], ![258, 1, 0, 0, 0], ![60, 0, 1, 0, 0], ![338, 0, 0, 1, 0], ![194, 0, 0, 0, 1]] where
  M :=![![![-22, -22, 7, -33, -30], ![-150, -149, 50, -222, -204], ![-996, -992, 331, -1476, -1368], ![-481, -478, 157, -718, -656], ![-697, -694, 233, -1031, -957]]]
  hmulB := by decide  
  f := ![![![5446, -2522, -1929, 549, 2748]], ![![4038, -1873, -1432, 408, 2040]], ![![948, -440, -337, 96, 480]], ![![5301, -2454, -1877, 534, 2674]], ![![3047, -1410, -1079, 307, 1537]]]
  g := ![![![64, -22, 7, -33, -30], ![432, -149, 50, -222, -204], ![2880, -992, 331, -1476, -1368], ![1393, -478, 157, -718, -656], ![2013, -694, 233, -1031, -957]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI347N2 : Nat.card (O ⧸ I347N2) = 347 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI347N2)

lemma isPrimeI347N2 : Ideal.IsPrime I347N2 := prime_ideal_of_norm_prime hp347.out _ NI347N2
def MulI347N0 : IdealMulLeCertificate' Table 
  ![![-2214, -5339, -3032, 1711, 4370]] ![![215, -77, -63, 16, 90]]
  ![![5446, -2522, -1929, 549, 2748]] where
 M := ![![![5446, -2522, -1929, 549, 2748]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI347N1 : IdealMulLeCertificate' Table 
  ![![5446, -2522, -1929, 549, 2748]] ![![-22, -22, 7, -33, -30]]
  ![![347, 0, 0, 0, 0]] where
 M := ![![![347, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC347 : ContainsPrimesAboveP 347 ![I347N0, I347N1, I347N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI347N0
    exact isPrimeI347N1
    exact isPrimeI347N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 347 (by decide) (𝕀 ⊙ MulI347N0 ⊙ MulI347N1)
instance hp349 : Fact (Nat.Prime 349) := {out := by norm_num}

def I349N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3821, -9087, -5155, 2926, 7422]] i)))

def SI349N0: IdealEqSpanCertificate' Table ![![-3821, -9087, -5155, 2926, 7422]] 
 ![![349, 0, 0, 0, 0], ![0, 349, 0, 0, 0], ![0, 0, 349, 0, 0], ![77, 137, 330, 1, 0], ![242, 204, 47, 0, 1]] where
  M :=![![![-3821, -9087, -5155, 2926, 7422], ![-4382, -10470, -5947, 3368, 8564], ![-5082, -12081, -6814, 3884, 9816], ![3260, 7756, 4390, -2489, -6326], ![1212, 2915, 1679, -946, -2411]]]
  hmulB := by decide  
  f := ![![![-21, 17, 7, 10, -2]], ![![78, 52, -27, 88, 84]], ![![358, 379, -132, 524, 536]], ![![365, 383, -134, 533, 540]], ![![80, 94, -29, 130, 121]]]
  g := ![![![-5803, -5513, -3781, 2926, 7422], ![-6694, -6358, -4355, 3368, 8564], ![-7678, -7297, -5014, 3884, 9816], ![4945, 4697, 3218, -2489, -6326], ![1884, 1789, 1224, -946, -2411]]]
  hle1 := by decide   
  hle2 := by decide  


def P349P0 : CertificateIrreducibleZModOfList' 349 3 2 8 [218, 244, 201, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [262, 53, 230], [235, 295, 119], [0, 1]]
 g := ![![[2, 201, 196], [345, 285], [104, 270, 86], [271, 288, 344], [268, 165, 148], [58, 279], [22, 148, 1], []], ![[297, 264, 159, 154], [193, 320], [261, 167, 62, 247], [214, 60, 230, 290], [80, 83, 279, 136], [284, 9], [282, 134, 85, 251], [33, 201]], ![[300, 171, 319, 174], [37, 68], [27, 117, 257, 209], [190, 329, 348, 186], [150, 65, 170, 39], [11, 76], [299, 114, 243, 278], [144, 201]]]
 h' := ![![[262, 53, 230], [343, 94, 335], [13, 208, 308], [252, 210, 321], [208, 246, 56], [342, 42, 219], [90, 60, 81], [0, 0, 1], [0, 1]], ![[235, 295, 119], [177, 334, 40], [46, 204, 147], [100, 89, 254], [155, 220, 159], [288, 248, 277], [117, 58, 3], [26, 332, 295], [262, 53, 230]], ![[0, 1], [79, 270, 323], [80, 286, 243], [8, 50, 123], [156, 232, 134], [223, 59, 202], [35, 231, 265], [101, 17, 53], [235, 295, 119]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [327, 15], []]
 b := ![[], [342, 76, 311], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI349N0 : CertifiedPrimeIdeal' SI349N0 349 where
  n := 3
  hpos := by decide
  P := [218, 244, 201, 1]
  hirr := P349P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1179070988, -1173740562, 419193560, -1704248590, -1619870774]
  a := ![-100, -107, 72, -79, -161]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1495864750, 1612498436, 1830817062, -1704248590, -1619870774]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI349N0 : Ideal.IsPrime I349N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI349N0 B_one_repr
lemma NI349N0 : Nat.card (O ⧸ I349N0) = 42508549 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI349N0

def I349N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![21, 56, 32, -18, -46]] i)))

def SI349N1: IdealEqSpanCertificate' Table ![![21, 56, 32, -18, -46]] 
 ![![349, 0, 0, 0, 0], ![72, 1, 0, 0, 0], ![51, 0, 1, 0, 0], ![188, 0, 0, 1, 0], ![345, 0, 0, 0, 1]] where
  M :=![![![21, 56, 32, -18, -46], ![28, 63, 36, -20, -52], ![32, 76, 39, -24, -56], ![-20, -48, -26, 15, 38], ![-6, -16, -12, 6, 17]]]
  hmulB := by decide  
  f := ![![![-99, 72, 20, 18, -22]], ![![-20, 15, 4, 4, -4]], ![![-13, 12, 3, 6, -2]], ![![-52, 40, 10, 11, -10]], ![![-97, 72, 20, 20, -21]]]
  g := ![![![39, 56, 32, -18, -46], ![44, 63, 36, -20, -52], ![47, 76, 39, -24, -56], ![-32, -48, -26, 15, 38], ![-15, -16, -12, 6, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI349N1 : Nat.card (O ⧸ I349N1) = 349 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI349N1)

lemma isPrimeI349N1 : Ideal.IsPrime I349N1 := prime_ideal_of_norm_prime hp349.out _ NI349N1

def I349N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1730, 3718, 1847, -667, -2398]] i)))

def SI349N2: IdealEqSpanCertificate' Table ![![1730, 3718, 1847, -667, -2398]] 
 ![![349, 0, 0, 0, 0], ![156, 1, 0, 0, 0], ![94, 0, 1, 0, 0], ![284, 0, 0, 1, 0], ![119, 0, 0, 0, 1]] where
  M :=![![![1730, 3718, 1847, -667, -2398], ![3618, 5899, 1590, 1646, -540], ![15044, 17612, -1765, 18052, 14248], ![5137, 3406, -3761, 10390, 11084], ![8709, 8018, -3659, 13979, 13441]]]
  hmulB := by decide  
  f := ![![![24794, -11106, -5635, 2249, 8096]], ![![11058, -4925, -2530, 1010, 3624]], ![![6640, -3048, -1487, 522, 2208]], ![![20143, -9054, -4545, 1860, 6514]], ![![8447, -3788, -1938, 706, 2827]]]
  g := ![![![-794, 3718, 1847, -667, -2398], ![-4210, 5899, 1590, 1646, -540], ![-26902, 17612, -1765, 18052, 14248], ![-12729, 3406, -3761, 10390, 11084], ![-18532, 8018, -3659, 13979, 13441]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI349N2 : Nat.card (O ⧸ I349N2) = 349 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI349N2)

lemma isPrimeI349N2 : Ideal.IsPrime I349N2 := prime_ideal_of_norm_prime hp349.out _ NI349N2
def MulI349N0 : IdealMulLeCertificate' Table 
  ![![-3821, -9087, -5155, 2926, 7422]] ![![21, 56, 32, -18, -46]]
  ![![-602689, -1437437, -815589, 462660, 1174332]] where
 M := ![![![-602689, -1437437, -815589, 462660, 1174332]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI349N1 : IdealMulLeCertificate' Table 
  ![![-602689, -1437437, -815589, 462660, 1174332]] ![![1730, 3718, 1847, -667, -2398]]
  ![![349, 0, 0, 0, 0]] where
 M := ![![![-5909078144, -14092778097, -7996121876, 4535984061, 11513271982]]]
 hmul := by decide  
 g := ![![![![-16931456, -40380453, -22911524, 12997089, 32989318]]]]
 hle2 := by decide  


def PBC349 : ContainsPrimesAboveP 349 ![I349N0, I349N1, I349N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI349N0
    exact isPrimeI349N1
    exact isPrimeI349N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 349 (by decide) (𝕀 ⊙ MulI349N0 ⊙ MulI349N1)
instance hp353 : Fact (Nat.Prime 353) := {out := by norm_num}

def I353N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3494, 1338, 1043, -213, -1454]] i)))

def SI353N0: IdealEqSpanCertificate' Table ![![-3494, 1338, 1043, -213, -1454]] 
 ![![353, 0, 0, 0, 0], ![0, 353, 0, 0, 0], ![0, 0, 353, 0, 0], ![0, 0, 0, 353, 0], ![100, 69, 34, 232, 1]] where
  M :=![![![-3494, 1338, 1043, -213, -1454], ![2498, -585, -718, 458, 1204], ![-68, 1944, -9, 1932, 1256], ![1555, 314, -495, 1066, 1304], ![563, 1098, -211, 1405, 1167]]]
  hmulB := by decide  
  f := ![![![2, 2, 1, 3, -4]], ![![10, 15, -18, -14, 32]], ![![-100, -104, 135, 12, -176]], ![![37, 30, -35, 24, 26]], ![![17, 13, -13, 15, 5]]]
  g := ![![![402, 288, 143, 955, -1454], ![-334, -237, -118, -790, 1204], ![-356, -240, -121, -820, 1256], ![-365, -254, -127, -854, 1304], ![-329, -225, -113, -763, 1167]]]
  hle1 := by decide   
  hle2 := by decide  


def P353P0 : CertificateIrreducibleZModOfList' 353 4 2 8 [284, 74, 124, 333, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [169, 135, 265, 38], [119, 293, 117, 77], [85, 277, 324, 238], [0, 1]]
 g := ![![[115, 13, 40, 35], [194, 253, 226], [137, 179, 159], [157, 83, 64], [45, 299, 315], [343, 345, 46, 281], [20, 1], []], ![[173, 334, 320, 36, 316, 314], [41, 312, 32], [144, 157, 43], [84, 327, 21], [304, 289, 109], [252, 146, 98, 9, 283, 337], [173, 156, 343, 20, 201, 164], [35, 306, 32]], ![[185, 168, 153, 31, 218, 74], [243, 153, 92], [72, 185, 169], [30, 292, 328], [257, 68, 336], [299, 326, 35, 48, 255, 215], [63, 339, 196, 123, 296, 236], [56, 340, 281]], ![[197, 281, 130, 137, 21, 298], [254, 16, 144], [246, 301, 242], [222, 185, 86], [284, 219, 240], [232, 177, 149, 208, 123, 193], [154, 93, 218, 165, 348, 28], [11, 66, 164]]]
 h' := ![![[169, 135, 265, 38], [138, 339, 36, 285], [318, 221, 324, 104], [211, 186, 335, 152], [184, 311, 141, 345], [16, 153, 0, 204], [321, 1, 270, 276], [0, 0, 1], [0, 1]], ![[119, 293, 117, 77], [311, 92, 25, 8], [219, 340, 283, 315], [102, 314, 46, 142], [183, 233, 35, 155], [280, 184, 246, 314], [100, 279, 337, 90], [265, 261, 64, 304], [169, 135, 265, 38]], ![[85, 277, 324, 238], [155, 70, 188, 318], [197, 2, 215, 299], [44, 88, 55, 340], [54, 44, 220, 143], [18, 105, 326, 267], [168, 28, 199, 93], [22, 94, 22, 344], [119, 293, 117, 77]], ![[0, 1], [159, 205, 104, 95], [49, 143, 237, 341], [250, 118, 270, 72], [200, 118, 310, 63], [103, 264, 134, 274], [197, 45, 253, 247], [218, 351, 266, 58], [85, 277, 324, 238]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [140, 35, 66], []]
 b := ![[], [], [274, 311, 259, 100], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI353N0 : CertifiedPrimeIdeal' SI353N0 353 where
  n := 4
  hpos := by decide
  P := [284, 74, 124, 333, 1]
  hirr := P353P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![517219626023878, 511550882513092, -164679444511288, 779593507795288, 693082629267778]
  a := ![325, 365, -289, 164, 647]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-194875476772674, -134025922201030, -67222347987580, -453301916380536, 693082629267778]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI353N0 : Ideal.IsPrime I353N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI353N0 B_one_repr
lemma NI353N0 : Nat.card (O ⧸ I353N0) = 15527402881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI353N0

def I353N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 2, 1, 3, -4]] i)))

def SI353N1: IdealEqSpanCertificate' Table ![![2, 2, 1, 3, -4]] 
 ![![353, 0, 0, 0, 0], ![264, 1, 0, 0, 0], ![198, 0, 1, 0, 0], ![300, 0, 0, 1, 0], ![53, 0, 0, 0, 1]] where
  M :=![![![2, 2, 1, 3, -4], ![10, 15, -18, -14, 32], ![-100, -104, 135, 12, -176], ![37, 30, -35, 24, 26], ![-73, -70, 83, -15, -91]]]
  hmulB := by decide  
  f := ![![![-3494, 1338, 1043, -213, -1454]], ![![-2606, 999, 778, -158, -1084]], ![![-1960, 756, 585, -114, -812]], ![![-2965, 1138, 885, -178, -1232]], ![![-523, 204, 156, -28, -215]]]
  g := ![![![-4, 2, 1, 3, -4], ![6, 15, -18, -14, 32], ![18, -104, 135, 12, -176], ![-27, 30, -35, 24, 26], ![32, -70, 83, -15, -91]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI353N1 : Nat.card (O ⧸ I353N1) = 353 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI353N1)

lemma isPrimeI353N1 : Ideal.IsPrime I353N1 := prime_ideal_of_norm_prime hp353.out _ NI353N1
def MulI353N0 : IdealMulLeCertificate' Table 
  ![![-3494, 1338, 1043, -213, -1454]] ![![2, 2, 1, 3, -4]]
  ![![353, 0, 0, 0, 0]] where
 M := ![![![353, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC353 : ContainsPrimesAboveP 353 ![I353N0, I353N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI353N0
    exact isPrimeI353N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 353 (by decide) (𝕀 ⊙ MulI353N0)
instance hp359 : Fact (Nat.Prime 359) := {out := by norm_num}

def I359N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-911, 335, 265, -62, -374]] i)))

def SI359N0: IdealEqSpanCertificate' Table ![![-911, 335, 265, -62, -374]] 
 ![![359, 0, 0, 0, 0], ![0, 359, 0, 0, 0], ![0, 0, 359, 0, 0], ![185, 238, 288, 1, 0], ![38, 47, 204, 0, 1]] where
  M :=![![![-911, 335, 265, -62, -374], ![594, -208, -165, 64, 252], ![-230, 277, 40, 164, 8], ![284, -28, -94, 77, 190], ![-12, 121, -1, 130, 47]]]
  hmulB := by decide  
  f := ![![![-253, -603, -343, 194, 494]], ![![-294, -698, -391, 224, 564]], ![![-322, -789, -466, 268, 664]], ![![-583, -1405, -809, 463, 1160]], ![![-248, -603, -352, 202, 503]]]
  g := ![![![69, 91, 263, -62, -374], ![-58, -76, -195, 64, 252], ![-86, -109, -136, 164, 8], ![-59, -76, -170, 77, 190], ![-72, -92, -131, 130, 47]]]
  hle1 := by decide   
  hle2 := by decide  


def P359P0 : CertificateIrreducibleZModOfList' 359 3 2 8 [317, 188, 160, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [246, 52, 247], [312, 306, 112], [0, 1]]
 g := ![![[211, 295, 153], [83, 257, 18], [36, 270, 253], [71, 165], [117, 250], [12, 124, 297], [282, 199, 1], []], ![[52, 117, 115, 352], [219, 290, 24, 15], [17, 9, 324, 85], [176, 165], [244, 41], [228, 244, 129, 64], [7, 139, 66, 235], [328, 338]], ![[265, 66, 174, 119], [52, 354, 165, 295], [21, 0, 78, 280], [135, 301], [355, 138], [122, 341, 340, 277], [48, 278, 28, 211], [104, 338]]]
 h' := ![![[246, 52, 247], [255, 248, 304], [76, 270, 57], [134, 288, 249], [91, 313, 122], [145, 89, 300], [356, 217, 80], [0, 0, 1], [0, 1]], ![[312, 306, 112], [311, 224, 269], [320, 176, 126], [56, 43, 140], [214, 156, 122], [302, 153, 339], [3, 278, 176], [338, 15, 306], [246, 52, 247]], ![[0, 1], [224, 246, 145], [44, 272, 176], [155, 28, 329], [128, 249, 115], [306, 117, 79], [75, 223, 103], [115, 344, 52], [312, 306, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [188, 52], []]
 b := ![[], [305, 142, 321], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI359N0 : CertifiedPrimeIdeal' SI359N0 359 where
  n := 3
  hpos := by decide
  P := [317, 188, 160, 1]
  hirr := P359P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8088868062, 8215501008, -3133071432, 11211816948, 11906939817]
  a := ![194, 219, -176, 93, 393]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7015490196, -8968866585, -15769225836, 11211816948, 11906939817]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI359N0 : Ideal.IsPrime I359N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI359N0 B_one_repr
lemma NI359N0 : Nat.card (O ⧸ I359N0) = 46268279 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI359N0

def I359N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-253, -603, -343, 194, 494]] i)))

def SI359N1: IdealEqSpanCertificate' Table ![![-253, -603, -343, 194, 494]] 
 ![![359, 0, 0, 0, 0], ![0, 359, 0, 0, 0], ![2, 134, 1, 0, 0], ![38, 30, 0, 1, 0], ![164, 11, 0, 0, 1]] where
  M :=![![![-253, -603, -343, 194, 494], ![-294, -698, -391, 224, 564], ![-322, -789, -466, 268, 664], ![216, 516, 290, -169, -414], ![88, 199, 107, -54, -159]]]
  hmulB := by decide  
  f := ![![![-911, 335, 265, -62, -374]], ![![594, -208, -165, 64, 252]], ![![216, -75, -60, 24, 92]], ![![-46, 18, 14, -1, -18]], ![![-398, 147, 116, -26, -163]]]
  g := ![![![-245, 95, -343, 194, 494], ![-280, 108, -391, 224, 564], ![-330, 129, -466, 268, 664], ![206, -80, 290, -169, -414], ![78, -30, 107, -54, -159]]]
  hle1 := by decide   
  hle2 := by decide  


def P359P1 : CertificateIrreducibleZModOfList' 359 2 2 8 [95, 302, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [57, 358], [0, 1]]
 g := ![![[143, 204], [118, 205], [152, 176], [101], [1], [76, 23], [248, 18], [1]], ![[283, 155], [315, 154], [132, 183], [101], [1], [310, 336], [197, 341], [1]]]
 h' := ![![[57, 358], [278, 113], [279, 88], [192, 251], [69, 137], [319, 358], [134, 270], [264, 57], [0, 1]], ![[0, 1], [257, 246], [269, 271], [139, 108], [339, 222], [262, 1], [87, 89], [282, 302], [57, 358]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [121]]
 b := ![[], [340, 240]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI359N1 : CertifiedPrimeIdeal' SI359N1 359 where
  n := 2
  hpos := by decide
  P := [95, 302, 1]
  hirr := P359P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![564870, 539544, -88246, 1003232, 655664]
  a := ![151, 167, -127, 88, 284]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-403650, -69484, -88246, 1003232, 655664]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI359N1 : Ideal.IsPrime I359N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI359N1 B_one_repr
lemma NI359N1 : Nat.card (O ⧸ I359N1) = 128881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI359N1
def MulI359N0 : IdealMulLeCertificate' Table 
  ![![-911, 335, 265, -62, -374]] ![![-253, -603, -343, 194, 494]]
  ![![359, 0, 0, 0, 0]] where
 M := ![![![359, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC359 : ContainsPrimesAboveP 359 ![I359N0, I359N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI359N0
    exact isPrimeI359N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 359 (by decide) (𝕀 ⊙ MulI359N0)


lemma PB1640I7_primes (p : ℕ) :
  p ∈ Set.range ![311, 313, 317, 331, 337, 347, 349, 353, 359] ↔ Nat.Prime p ∧ 307 < p ∧ p ≤ 359 := by
  rw [← List.mem_ofFn']
  convert primes_range 307 359 (by omega)

def PB1640I7 : PrimesBelowBoundCertificateInterval O 307 359 1640 where
  m := 9
  g := ![2, 4, 4, 2, 2, 3, 3, 2, 2]
  P := ![311, 313, 317, 331, 337, 347, 349, 353, 359]
  hP := PB1640I7_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I311N0, I311N1]
    · exact ![I313N0, I313N1, I313N2, I313N3]
    · exact ![I317N0, I317N1, I317N2, I317N3]
    · exact ![I331N0, I331N1]
    · exact ![I337N0, I337N1]
    · exact ![I347N0, I347N1, I347N2]
    · exact ![I349N0, I349N1, I349N2]
    · exact ![I353N0, I353N1]
    · exact ![I359N0, I359N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC311
    · exact PBC313
    · exact PBC317
    · exact PBC331
    · exact PBC337
    · exact PBC347
    · exact PBC349
    · exact PBC353
    · exact PBC359
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![9354951841, 311]
    · exact ![97969, 313, 313, 313]
    · exact ![100489, 317, 317, 317]
    · exact ![36264691, 109561]
    · exact ![12897917761, 337]
    · exact ![41781923, 347, 347]
    · exact ![42508549, 349, 349]
    · exact ![15527402881, 353]
    · exact ![46268279, 128881]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI311N0
      exact NI311N1
    · dsimp ; intro j
      fin_cases j
      exact NI313N0
      exact NI313N1
      exact NI313N2
      exact NI313N3
    · dsimp ; intro j
      fin_cases j
      exact NI317N0
      exact NI317N1
      exact NI317N2
      exact NI317N3
    · dsimp ; intro j
      fin_cases j
      exact NI331N0
      exact NI331N1
    · dsimp ; intro j
      fin_cases j
      exact NI337N0
      exact NI337N1
    · dsimp ; intro j
      fin_cases j
      exact NI347N0
      exact NI347N1
      exact NI347N2
    · dsimp ; intro j
      fin_cases j
      exact NI349N0
      exact NI349N1
      exact NI349N2
    · dsimp ; intro j
      fin_cases j
      exact NI353N0
      exact NI353N1
    · dsimp ; intro j
      fin_cases j
      exact NI359N0
      exact NI359N1
  β := ![I311N1, I313N1, I313N2, I313N3, I317N1, I317N2, I317N3, I337N1, I347N1, I347N2, I349N1, I349N2, I353N1]
  Il := ![[I311N1], [I313N1, I313N2, I313N3], [I317N1, I317N2, I317N3], [], [I337N1], [I347N1, I347N2], [I349N1, I349N2], [I353N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
